/* Moteur de recherche (port de recherche_parcelle_all.py) : bâtiments, piscines, voies, filtres, liens, vignettes.
   S'appuie sur core.js (Core). Sans dépendance ; utilisable dans le navigateur et dans Node. */
(function (root) {
  "use strict";
  const Core = typeof require !== "undefined" && typeof module !== "undefined" ? require("./core.js") : root.Core;

  const HIGHWAYS = "motorway|trunk|primary|secondary|tertiary|unclassified|residential|living_street|pedestrian|road|track|cycleway|footway|path|bridleway|motorway_link|trunk_link|primary_link|secondary_link|tertiary_link";
  const MIROIRS = ["https://overpass-api.de/api/interpreter", "https://overpass.openstreetmap.fr/api/interpreter", "https://overpass.kumi.systems/api/interpreter", "https://overpass.private.coffee/api/interpreter"];
  const VOIE_LARGEUR_MAX = 25, VOIE_LONGUEUR_MIN = 15;

  /* ---------- géométrie (degrés -> mètres par échelle locale) ---------- */
  const echelle = lat => ({ kx: 111320 * Math.cos(lat * Math.PI / 180), ky: 110540 });

  function pip(x, y, rings) { // règle pair/impair : gère les trous
    let dedans = false;
    for (const r of rings) for (let i = 0, j = r.length - 1; i < r.length; j = i++) {
      const xi = r[i][0], yi = r[i][1], xj = r[j][0], yj = r[j][1];
      if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) dedans = !dedans;
    }
    return dedans;
  }

  function distBord(x, y, rings, k) { // distance (m) au bord le plus proche
    let mini = Infinity;
    for (const r of rings) for (let i = 0; i < r.length - 1; i++) {
      const ax = (r[i][0] - x) * k.kx, ay = (r[i][1] - y) * k.ky, bx = (r[i + 1][0] - x) * k.kx, by = (r[i + 1][1] - y) * k.ky;
      const dx = bx - ax, dy = by - ay, l2 = dx * dx + dy * dy;
      const t = l2 ? Math.max(0, Math.min(1, -(ax * dx + ay * dy) / l2)) : 0;
      const d = Math.hypot(ax + t * dx, ay + t * dy);
      if (d < mini) mini = d;
    }
    return mini;
  }

  function perimetre(rings, k) {
    let p = 0;
    for (const r of rings) for (let i = 0; i < r.length - 1; i++)
      p += Math.hypot((r[i + 1][0] - r[i][0]) * k.kx, (r[i + 1][1] - r[i][1]) * k.ky);
    return p;
  }

  function aireAnneau(r, k) { // surface (m²) d'un anneau
    let a = 0;
    for (let i = 0; i < r.length - 1; i++) a += (r[i][0] * k.kx) * (r[i + 1][1] * k.ky) - (r[i + 1][0] * k.kx) * (r[i][1] * k.ky);
    return Math.abs(a) / 2;
  }

  /* Surface (m²) de la partie de `s` située dans `c`, par échantillonnage régulier (précision ~1-2 %).
     Retourne aussi un point à l'intérieur des deux formes. */
  function aireDans(s, c, k) {
    const x0 = Math.max(s.bb[0], c.bb[0]), y0 = Math.max(s.bb[1], c.bb[1]);
    const x1 = Math.min(s.bb[2], c.bb[2]), y1 = Math.min(s.bb[3], c.bb[3]);
    if (x0 >= x1 || y0 >= y1) return null;
    const wm = (x1 - x0) * k.kx, hm = (y1 - y0) * k.ky;
    const pas = Math.max(0.4, Math.sqrt(wm * hm / 2500));
    const nx = Math.max(1, Math.ceil(wm / pas)), ny = Math.max(1, Math.ceil(hm / pas));
    const dx = (x1 - x0) / nx, dy = (y1 - y0) / ny;
    const pts = []; let sx = 0, sy = 0;
    for (let i = 0; i < nx; i++) for (let j = 0; j < ny; j++) {
      const x = x0 + (i + 0.5) * dx, y = y0 + (j + 0.5) * dy;
      if (pip(x, y, s.rings) && pip(x, y, c.rings)) { pts.push([x, y]); sx += x; sy += y; }
    }
    if (!pts.length) return null;
    const mx = sx / pts.length, my = sy / pts.length;
    let best = pts[0], bd = Infinity;
    for (const p of pts) { const d = (p[0] - mx) ** 2 + (p[1] - my) ** 2; if (d < bd) { bd = d; best = p; } }
    return { aire: pts.length * (wm / nx) * (hm / ny), pt: { x: best[0], y: best[1] } };
  }

  /* ---------- index spatial à grille ---------- */
  function indexer(items, n = 150) {
    let a = Infinity, b = Infinity, c = -Infinity, d = -Infinity;
    for (const it of items) { a = Math.min(a, it.bb[0]); b = Math.min(b, it.bb[1]); c = Math.max(c, it.bb[2]); d = Math.max(d, it.bb[3]); }
    const cw = (c - a) / n || 1, ch = (d - b) / n || 1, g = new Map();
    const cell = (x, y) => [Math.min(n - 1, Math.max(0, Math.floor((x - a) / cw))), Math.min(n - 1, Math.max(0, Math.floor((y - b) / ch)))];
    items.forEach((it, i) => {
      const [x0, y0] = cell(it.bb[0], it.bb[1]), [x1, y1] = cell(it.bb[2], it.bb[3]);
      for (let x = x0; x <= x1; x++) for (let y = y0; y <= y1; y++) { const key = x * n + y; (g.get(key) || g.set(key, []).get(key)).push(i); }
    });
    return { requete(bb) {
      const [x0, y0] = cell(bb[0], bb[1]), [x1, y1] = cell(bb[2], bb[3]), out = new Set();
      for (let x = x0; x <= x1; x++) for (let y = y0; y <= y1; y++) for (const i of g.get(x * n + y) || []) out.add(i);
      return [...out];
    } };
  }

  /* ---------- bâtiments du cadastre ---------- */
  function chargerBatiments(geojson) {
    const items = [];
    for (const f of geojson.features || []) {
      if (!f.geometry) continue;
      const rings = f.geometry.type === "Polygon" ? f.geometry.coordinates
        : f.geometry.type === "MultiPolygon" ? f.geometry.coordinates.flat() : [];
      if (!rings.length) continue;
      let a = Infinity, b = Infinity, c = -Infinity, d = -Infinity;
      for (const r of rings) for (const p of r) { a = Math.min(a, p[0]); c = Math.max(c, p[0]); b = Math.min(b, p[1]); d = Math.max(d, p[1]); }
      items.push({ rings, bb: [a, b, c, d], props: f.properties || {} });
    }
    return { items, index: indexer(items) };
  }

  // Plus gros bâtiment (surface sur la parcelle). Retourne {aire, pt} ou null.
  function plusGrosBatiment(parcelle, B, k) {
    if (parcelle._bat !== undefined) return parcelle._bat;
    let meilleur = null;
    for (const j of B.index.requete(parcelle.bb)) {
      const r = aireDans(B.items[j], parcelle, k);
      if (r && (!meilleur || r.aire > meilleur.aire)) meilleur = r;
    }
    return (parcelle._bat = meilleur);
  }

  /* ---------- OpenStreetMap (Overpass) ---------- */
  function emprises(P, indices, marge = 0.0002, max = 60) {
    const b = indices.map(i => [P[i].bb[1] - marge, P[i].bb[0] - marge, P[i].bb[3] + marge, P[i].bb[2] + marge]);
    if (b.length > max) return [[Math.min(...b.map(x => x[0])), Math.min(...b.map(x => x[1])), Math.max(...b.map(x => x[2])), Math.max(...b.map(x => x[3]))]];
    return b;
  }

  function requeteOSM(P, indices, voies, piscines) {
    const parties = [];
    for (const [s, w, n, e] of emprises(P, indices)) {
      const bb = `(${s.toFixed(6)},${w.toFixed(6)},${n.toFixed(6)},${e.toFixed(6)})`;
      if (voies) parties.push(`way["highway"~"^(${HIGHWAYS})$"]["access"!~"^(private|no)$"]["footway"!~"^(sidewalk|crossing)$"]${bb};`);
      if (piscines) parties.push(`way["leisure"="swimming_pool"]${bb};way["amenity"="swimming_pool"]${bb};node["leisure"="swimming_pool"]${bb};`);
    }
    return "[out:json][timeout:180];(" + parties.join("") + ");out geom;";
  }

  function parserOSM(data) {
    const lignes = [], piscines = [];
    for (const el of data.elements || []) {
      const tags = el.tags || {};
      if (el.type === "node" && el.lat !== undefined) { piscines.push({ pt: { x: el.lon, y: el.lat } }); continue; }
      const pts = (el.geometry || []).map(g => [g.lon, g.lat]);
      if (tags.highway) { if (pts.length >= 2) lignes.push({ pts, bb: [Math.min(...pts.map(p => p[0])), Math.min(...pts.map(p => p[1])), Math.max(...pts.map(p => p[0])), Math.max(...pts.map(p => p[1]))] }); }
      else if (pts.length >= 4 && pts[0][0] === pts[pts.length - 1][0] && pts[0][1] === pts[pts.length - 1][1]) {
        piscines.push({ rings: [pts], bb: [Math.min(...pts.map(p => p[0])), Math.min(...pts.map(p => p[1])), Math.max(...pts.map(p => p[0])), Math.max(...pts.map(p => p[1]))] });
      } else if (pts.length >= 2) {
        piscines.push({ pt: { x: pts.reduce((s, p) => s + p[0], 0) / pts.length, y: pts.reduce((s, p) => s + p[1], 0) / pts.length } });
      }
    }
    return { lignes, piscines };
  }

  // Interroge Overpass : serveurs de secours, attente si limite atteinte (429/504).
  async function overpass(requete, log = () => {}, fetchFn = fetch, attente = ms => new Promise(r => setTimeout(r, ms))) {
    const erreurs = [];
    for (let tour = 0; tour < 3; tour++) {
      for (const url of MIROIRS) {
        try {
          const r = await fetchFn(url, { method: "POST", headers: { "Content-Type": "application/x-www-form-urlencoded" }, body: "data=" + encodeURIComponent(requete) });
          if (r.status === 429 || r.status === 504) { erreurs.push(`${new URL(url).host} : HTTP ${r.status}`); continue; }
          if (!r.ok) throw new Error("HTTP " + r.status);
          return await r.json();
        } catch (e) { erreurs.push(`${new URL(url).host} : ${e.message}`); }
      }
      if (tour < 2) { const s = 15 * (tour + 1); log(`Overpass occupé, nouvelle tentative dans ${s} s…`); await attente(s * 1000); }
    }
    throw new Error("Overpass injoignable : " + [...new Set(erreurs)].join(" ; "));
  }

  // Parcelles de voie publique parmi `indices` (heuristique sur les axes OSM).
  function detecterVoies(P, lignes, indices, k) {
    const voies = new Set();
    if (!lignes.length) return voies;
    for (const i of indices) {
      const p = P[i], per = perimetre(p.rings, k);
      if (!per) continue;
      const largeur = 2 * p.surface / per;
      if (largeur > VOIE_LARGEUR_MAX) continue;
      const marge = Math.min(3, Math.max(0.5, largeur / 4));
      let longueur = 0;
      for (const l of lignes) {
        if (l.bb[0] > p.bb[2] || l.bb[2] < p.bb[0] || l.bb[1] > p.bb[3] || l.bb[3] < p.bb[1]) continue;
        for (let s = 0; s < l.pts.length - 1; s++) {
          const a = l.pts[s], b = l.pts[s + 1];
          const L = Math.hypot((b[0] - a[0]) * k.kx, (b[1] - a[1]) * k.ky), n = Math.max(1, Math.ceil(L)); // 1 point par mètre
          for (let t = 0; t < n; t++) {
            const x = a[0] + (b[0] - a[0]) * (t + 0.5) / n, y = a[1] + (b[1] - a[1]) * (t + 0.5) / n;
            if (x < p.bb[0] || x > p.bb[2] || y < p.bb[1] || y > p.bb[3]) continue;
            if (pip(x, y, p.rings) && distBord(x, y, p.rings, k) >= marge) longueur += L / n;
          }
        }
      }
      const bande = Math.max(per / 2 - largeur, 1);
      if (longueur >= VOIE_LONGUEUR_MIN && longueur >= 0.5 * bande) voies.add(i);
    }
    return voies;
  }

  function compterPiscines(P, indices, piscines, k) {
    for (const i of indices) P[i].piscines = 0;
    for (const pis of piscines) {
      let meilleur = -1, aireMax = 0, ptMeilleur = null;
      const aireP = pis.rings ? aireAnneau(pis.rings[0], k) : 0;
      for (const i of indices) {
        const p = P[i];
        if (pis.pt) {
          if (pis.pt.x >= p.bb[0] && pis.pt.x <= p.bb[2] && pis.pt.y >= p.bb[1] && pis.pt.y <= p.bb[3] && pip(pis.pt.x, pis.pt.y, p.rings)) { meilleur = i; ptMeilleur = pis.pt; break; }
        } else {
          const r = aireDans(pis, p, k);
          if (r && r.aire > aireMax) { aireMax = r.aire; meilleur = i; ptMeilleur = r.pt; }
        }
      }
      if (meilleur >= 0 && (pis.pt || aireMax >= 0.3 * aireP)) {
        P[meilleur].piscines++;
        if (!P[meilleur].ptPiscine) P[meilleur].ptPiscine = ptMeilleur;
      }
    }
  }

  /* ---------- recherche complète ---------- */
  // prm : {cible, tol, maxN, maxR, aussi, garderInclus, construction, seuilBati, exclureVoies, piscine ("oui"|"non"|""), cpFiltre}
  // svc : {batiments(): Promise<{items,index}>, osm(requete): Promise<json>, adresse(pt): Promise<{label,cp}>}
  async function rechercher(P, prm, svc, log = () => {}, progression = () => {}) {
    const tol = prm.tol / 100, k = echelle(P[0].pt.y), stats = [];
    const compte = r => { const s = r.filter(g => g.length === 1).length; return `${s} parcelle(s) seule(s), ${r.length - s} groupe(s)`; };
    const etape = (nom, av, ap) => stats.push(`${nom} : ${compte(av)} → ${compte(ap)}`);
    const verifOSM = prm.exclureVoies || !!prm.piscine;
    const controlees = new Set();
    let B = null;
    const getB = async () => B || (B = await svc.batiments());

    async function verifier(res) {
      if (prm.construction) {
        const bati = await getB(), av = res;
        res = res.filter(g => g.some(i => { const r = plusGrosBatiment(P[i], bati, k); return r && r.aire >= prm.seuilBati; }));
        etape(`filtre construction (bâtiment ≥ ${prm.seuilBati} m²)`, av, res);
      }
      if (!verifOSM || !res.length) return res;
      const nouvelles = [...new Set(res.flat())].filter(i => !controlees.has(i));
      if (nouvelles.length) {
        log(`Vérification OpenStreetMap sur ${nouvelles.length} parcelle(s) candidate(s)…`);
        const data = parserOSM(await overpass(requeteOSM(P, nouvelles, prm.exclureVoies, !!prm.piscine), log, svc.fetch || fetch, svc.attente));
        if (prm.exclureVoies) for (const i of detecterVoies(P, data.lignes, nouvelles, k)) P[i].voie = true;
        if (prm.piscine) compterPiscines(P, nouvelles, data.piscines, k);
        nouvelles.forEach(i => controlees.add(i));
      }
      if (prm.exclureVoies) { const av = res; res = res.filter(g => !g.some(i => P[i].voie)); etape("filtre voies publiques", av, res); }
      if (prm.piscine) {
        const av = res, attendu = prm.piscine === "oui" ? 1 : 0;
        // Deux parcelles avec piscine dans un même groupe = deux propriétés différentes
        res = res.filter(g => g.filter(i => (P[i].piscines || 0) > 0).length === attendu);
        etape(`filtre piscine (${prm.piscine})`, av, res);
      }
      return res;
    }

    let tronque = false;
    const chercherGroupes = async () => {
      const V = await Core.construireVoisins(P, progression);
      const g = Core.groupesContigus(P, V, prm.cible, tol, prm.maxN);
      tronque = g.tronque; return g.groupes;
    };

    const seules = Core.parcellesSeules(P, prm.cible, tol);
    let resultats, mode;
    if (prm.aussi) {
      resultats = await verifier(seules.concat(await chercherGroupes()));
      mode = resultats.some(g => g.length === 1) ? "parcelles seules et contiguës" : "parcelles contiguës";
    } else {
      resultats = await verifier(seules); mode = "parcelle seule";
      if (!resultats.length) { log("Aucune parcelle seule ne correspond aux critères. Recherche de parcelles contiguës…"); resultats = await verifier(await chercherGroupes()); mode = "parcelles contiguës"; }
    }
    let ecartes = 0;
    if (!prm.garderInclus) { const av = resultats.length; resultats = Core.sansInclus(resultats); ecartes = av - resultats.length; }

    const ecart = g => Math.abs(g.reduce((s, i) => s + P[i].surface, 0) - prm.cible);
    resultats.sort((a, b) => ecart(a) - ecart(b) || a.length - b.length);
    let total = resultats.length, avantCP = total;
    if (prm.cpFiltre) {
      const gardes = [];
      for (const g of resultats) {
        let ok = false;
        for (const i of g) if ((await svc.adresse(P[i].pt)).cp === prm.cpFiltre) { ok = true; break; }
        if (ok) { gardes.push(g); if (gardes.length >= prm.maxR) break; }
      }
      resultats = gardes; total = gardes.length;
    }
    return { resultats: resultats.slice(0, prm.maxR), mode, total, avantCP, stats, ecartes, tronque, k, bati: B };
  }

  /* ---------- liens et vignettes ---------- */
  const f6 = x => x.toFixed(6);
  const lienGoogle = c => `https://www.google.com/maps/place/${f6(c.y)},${f6(c.x)}/@${f6(c.y)},${f6(c.x)},21z`;
  const lienBing3D = (c, titre) => `https://www.bing.com/maps?cp=${f6(c.y)}~${f6(c.x)}&lvl=19&style=g&pi=60&dir=0&sp=point.${f6(c.y)}_${f6(c.x)}_${encodeURIComponent(titre)}`;
  const lienOSM = c => `https://www.openstreetmap.org/?mlat=${f6(c.y)}&mlon=${f6(c.x)}#map=19/${f6(c.y)}/${f6(c.x)}`;

  // Repères d'un résultat : plus gros bâtiment (Google/Bing), maison de la parcelle à piscine (OSM)
  function reperes(P, g, B, k, piscine) {
    let rep = null;
    if (B) for (const i of g) { const r = plusGrosBatiment(P[i], B, k); if (r && (!rep || r.aire > rep.aire)) rep = { i, aire: r.aire, pt: r.pt }; }
    const centre = P[g[0]].pt;
    const point = rep ? rep.pt : centre;
    const titre = rep ? `${P[rep.i].ref} (batiment ${Math.round(rep.aire)} m2)` : g.map(i => P[i].ref).join(" + ");
    const info = rep ? `plus gros bâtiment : ${Math.round(rep.aire)} m² sur la parcelle ${P[rep.i].ref}` : "aucun bâtiment sur le cadastre : centre de la première parcelle";
    let osm = point, infoOsm = "repère (plus gros bâtiment)";
    if (piscine === "oui") {
      const ip = g.find(i => (P[i].piscines || 0) > 0);
      if (ip !== undefined) {
        const r = B ? plusGrosBatiment(P[ip], B, k) : null;
        if (r) { osm = r.pt; infoOsm = `maison avec piscine : parcelle ${P[ip].ref}`; }
        else if (P[ip].ptPiscine) { osm = P[ip].ptPiscine; infoOsm = `piscine (aucun bâtiment) : parcelle ${P[ip].ref}`; }
      }
    }
    return { point, titre, info, osm, infoOsm };
  }

  // Vignette IGN (photo aérienne, sans clé) cadrée sur le groupe ; `facteur` > 1 pour un plan élargi.
  const IGN = ["https://data.geopf.fr/wms-r/wms", "https://data.geopf.fr/wms-r"];
  const VIG_W = 960, VIG_H = 600; // pixels réels de l'image (≥ 480)
  function vignetteIGN(P, g, k, pin, facteur, extentMin) {
    let a = Infinity, b = Infinity, c = -Infinity, d = -Infinity;
    for (const i of g) { a = Math.min(a, P[i].bb[0]); b = Math.min(b, P[i].bb[1]); c = Math.max(c, P[i].bb[2]); d = Math.max(d, P[i].bb[3]); }
    const cx = (a + c) / 2, cy = (b + d) / 2;
    let wm = Math.max(extentMin, (c - a) * k.kx * 1.5), hm = (d - b) * k.ky * 1.5;
    wm = Math.max(wm, hm * VIG_W / VIG_H) * facteur; hm = wm * VIG_H / VIG_W;
    const dLon = wm / 2 / k.kx, dLat = hm / 2 / k.ky;
    const bbox = [cy - dLat, cx - dLon, cy + dLat, cx + dLon]; // WMS 1.3.0 EPSG:4326 : lat,lon
    const url = base => `${base}?SERVICE=WMS&VERSION=1.3.0&REQUEST=GetMap&LAYERS=ORTHOIMAGERY.ORTHOPHOTOS&STYLES=&CRS=EPSG:4326&BBOX=${bbox.map(v => v.toFixed(7)).join(",")}&WIDTH=${VIG_W}&HEIGHT=${VIG_H}&FORMAT=image/jpeg`;
    const px = (lon, lat) => [(lon - bbox[1]) / (2 * dLon) * VIG_W, (bbox[2] - lat) / (2 * dLat) * VIG_H];
    const polys = g.map(i => P[i].rings.map(r => "M" + r.map(p => px(p[0], p[1]).map(v => v.toFixed(1)).join(",")).join("L") + "Z").join(""));
    return { url: url(IGN[0]), urlAlt: url(IGN[1]), polys, pin: px(pin.x, pin.y), largeurM: wm, w: VIG_W, h: VIG_H };
  }

  function vignetteGoogle(pin, cle) {
    if (!cle) return null;
    return `https://maps.googleapis.com/maps/api/staticmap?center=${f6(pin.y)},${f6(pin.x)}&zoom=20&size=640x400&scale=2&maptype=satellite&markers=color:red%7C${f6(pin.y)},${f6(pin.x)}&key=${encodeURIComponent(cle)}`;
  }

  const API = { echelle, pip, aireDans, indexer, chargerBatiments, plusGrosBatiment, requeteOSM, parserOSM, overpass, detecterVoies, compterPiscines, rechercher, lienGoogle, lienBing3D, lienOSM, reperes, vignetteIGN, vignetteGoogle, VIG_W, VIG_H };
  if (typeof module !== "undefined" && module.exports) module.exports = API; else root.Rech = API;
})(typeof self !== "undefined" ? self : this);
