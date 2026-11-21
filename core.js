/* Cœur de l'algorithme (port de recherche_parcelle_all.py). Sans dépendance, utilisable dans le navigateur et dans Node. */
(function (root) {
  "use strict";
  const BORDURE_MIN = 1e-5;   // degrés (~1 m) de frontière commune minimale
  const EPS_COLIN = 2e-7;     // tolérance de colinéarité (~2 cm)

  function normaliser(t) {
    return t.normalize("NFD").replace(/[̀-ͯ]/g, "").replace(/[-'’]/g, " ").toLowerCase().split(/\s+/).filter(Boolean).join(" ");
  }

  // Anneaux d'une géométrie Polygon / MultiPolygon
  function anneaux(geom) {
    const out = [];
    if (geom.type === "Polygon") geom.coordinates.forEach(r => out.push(r));
    else if (geom.type === "MultiPolygon") geom.coordinates.forEach(p => p.forEach(r => out.push(r)));
    return out;
  }

  function bbox(rings) {
    let a = Infinity, b = Infinity, c = -Infinity, d = -Infinity;
    for (const r of rings) for (const [x, y] of r) {
      if (x < a) a = x; if (x > c) c = x; if (y < b) b = y; if (y > d) d = y;
    }
    return [a, b, c, d];
  }

  // Point à l'intérieur de la parcelle (équivalent de representative_point)
  function pointInterieur(rings, bb) {
    const essais = [0.5, 0.4, 0.6, 0.3, 0.7, 0.2, 0.8, 0.1, 0.9];
    let meilleur = null;
    for (const f of essais) {
      const y = bb[1] + (bb[3] - bb[1]) * f;
      const xs = [];
      for (const r of rings) for (let i = 0; i < r.length - 1; i++) {
        const [x1, y1] = r[i], [x2, y2] = r[i + 1];
        if ((y1 <= y) !== (y2 <= y)) xs.push(x1 + (y - y1) * (x2 - x1) / (y2 - y1));
      }
      xs.sort((p, q) => p - q);
      let larg = -1, cx = null;
      for (let i = 0; i + 1 < xs.length; i += 2) {
        if (xs[i + 1] - xs[i] > larg) { larg = xs[i + 1] - xs[i]; cx = (xs[i] + xs[i + 1]) / 2; }
      }
      if (cx !== null) { meilleur = { x: cx, y }; break; }
    }
    return meilleur || { x: (bb[0] + bb[2]) / 2, y: (bb[1] + bb[3]) / 2 };
  }

  function chargerParcelles(geojson, code) {
    const parcelles = [];
    for (const feat of geojson.features) {
      const p = feat.properties;
      if (!String(p.id).startsWith(code)) {
        throw new Error(`Le fichier ne correspond pas à la commune ${code} (id ${p.id}).`);
      }
      if (!p.contenance || !feat.geometry) continue;
      const rings = anneaux(feat.geometry);
      if (!rings.length) continue;
      const bb = bbox(rings);
      parcelles.push({
        id: p.id,
        ref: `${p.prefixe || "000"}${p.section} ${parseInt(p.numero, 10)}`,
        surface: parseInt(p.contenance, 10),
        rings, bb,
        pt: pointInterieur(rings, bb),
      });
    }
    return parcelles;
  }

  // Longueur de recouvrement colinéaire entre les segments ab et cd
  function recouvrement(a, b, c, d) {
    const dx = b[0] - a[0], dy = b[1] - a[1];
    const L = Math.hypot(dx, dy);
    if (L < 1e-12) return 0;
    const ux = dx / L, uy = dy / L;
    const dist = p => Math.abs((p[0] - a[0]) * uy - (p[1] - a[1]) * ux);
    if (dist(c) > EPS_COLIN || dist(d) > EPS_COLIN) return 0;
    let t1 = (c[0] - a[0]) * ux + (c[1] - a[1]) * uy;
    let t2 = (d[0] - a[0]) * ux + (d[1] - a[1]) * uy;
    if (t1 > t2) [t1, t2] = [t2, t1];
    return Math.max(0, Math.min(L, t2) - Math.max(0, t1));
  }

  function bordureCommune(pa, pb) {
    let total = 0;
    for (const ra of pa.rings) for (let i = 0; i < ra.length - 1; i++) {
      const a = ra[i], b = ra[i + 1];
      const x0 = Math.min(a[0], b[0]) - EPS_COLIN, x1 = Math.max(a[0], b[0]) + EPS_COLIN;
      const y0 = Math.min(a[1], b[1]) - EPS_COLIN, y1 = Math.max(a[1], b[1]) + EPS_COLIN;
      for (const rb of pb.rings) for (let j = 0; j < rb.length - 1; j++) {
        const c = rb[j], d = rb[j + 1];
        if (Math.max(c[0], d[0]) < x0 || Math.min(c[0], d[0]) > x1 ||
            Math.max(c[1], d[1]) < y0 || Math.min(c[1], d[1]) > y1) continue;
        total += recouvrement(a, b, c, d);
        if (total > BORDURE_MIN) return total;
      }
    }
    return total;
  }

  // Voisinage par grille spatiale ; async pour laisser l'interface respirer
  async function construireVoisins(parcelles, onProgress) {
    const n = parcelles.length;
    const voisins = Array.from({ length: n }, () => new Set());
    let minx = Infinity, miny = Infinity, maxx = -Infinity, maxy = -Infinity;
    for (const p of parcelles) {
      minx = Math.min(minx, p.bb[0]); miny = Math.min(miny, p.bb[1]);
      maxx = Math.max(maxx, p.bb[2]); maxy = Math.max(maxy, p.bb[3]);
    }
    const NC = 200, cw = (maxx - minx) / NC || 1, ch = (maxy - miny) / NC || 1;
    const grille = new Map();
    const cellules = p => [
      Math.max(0, Math.floor((p.bb[0] - EPS_COLIN - minx) / cw)), Math.min(NC - 1, Math.floor((p.bb[2] + EPS_COLIN - minx) / cw)),
      Math.max(0, Math.floor((p.bb[1] - EPS_COLIN - miny) / ch)), Math.min(NC - 1, Math.floor((p.bb[3] + EPS_COLIN - miny) / ch)),
    ];
    parcelles.forEach((p, i) => {
      const [cx0, cx1, cy0, cy1] = cellules(p);
      for (let cx = cx0; cx <= cx1; cx++) for (let cy = cy0; cy <= cy1; cy++) {
        const k = cx * NC + cy;
        if (!grille.has(k)) grille.set(k, []);
        grille.get(k).push(i);
      }
    });
    for (let i = 0; i < n; i++) {
      const p = parcelles[i];
      const [cx0, cx1, cy0, cy1] = cellules(p);
      const cand = new Set();
      for (let cx = cx0; cx <= cx1; cx++) for (let cy = cy0; cy <= cy1; cy++)
        for (const j of grille.get(cx * NC + cy) || []) if (j > i) cand.add(j);
      for (const j of cand) {
        const q = parcelles[j];
        if (q.bb[0] > p.bb[2] + EPS_COLIN || q.bb[2] < p.bb[0] - EPS_COLIN ||
            q.bb[1] > p.bb[3] + EPS_COLIN || q.bb[3] < p.bb[1] - EPS_COLIN) continue;
        if (bordureCommune(p, q) > BORDURE_MIN) { voisins[i].add(j); voisins[j].add(i); }
      }
      if (onProgress && i % 500 === 0) { onProgress(i / n); await new Promise(r => setTimeout(r, 0)); }
    }
    return voisins;
  }

  function parcellesSeules(parcelles, cible, tol) {
    const mini = cible * (1 - tol), maxi = cible * (1 + tol);
    const out = [];
    parcelles.forEach((p, i) => { if (p.surface >= mini && p.surface <= maxi) out.push([i]); });
    return out;
  }

  // Ensembles connexes de 2..maxN parcelles dont la somme est dans la plage
  function groupesContigus(parcelles, voisins, cible, tol, maxN, limite = 3000000) {
    const mini = cible * (1 - tol), maxi = cible * (1 + tol);
    const surf = parcelles.map(p => p.surface);
    const trouves = new Map(), vus = new Set();
    let explores = 0, tronque = false;
    function etendre(groupe, total) {
      if (tronque) return;
      const cle = groupe.slice().sort((a, b) => a - b).join(",");
      if (vus.has(cle)) return;
      vus.add(cle);
      if (++explores > limite) { tronque = true; return; }
      if (groupe.length >= 2 && total >= mini && total <= maxi) trouves.set(cle, groupe.slice().sort((a, b) => a - b));
      if (groupe.length >= maxN) return;
      const cand = new Set();
      for (const g of groupe) for (const v of voisins[g]) cand.add(v);
      for (const g of groupe) cand.delete(g);
      for (const c of cand) if (total + surf[c] <= maxi) etendre(groupe.concat(c), total + surf[c]);
    }
    for (let i = 0; i < parcelles.length; i++) if (surf[i] <= maxi) etendre([i], surf[i]);
    return { groupes: [...trouves.values()], tronque };
  }

  // Ne garde que les solutions minimales : écarte tout groupe qui contient déjà une solution plus petite
  function sansInclus(resultats) {
    const gardes = [];
    for (const g of resultats.slice().sort((a, b) => a.length - b.length)) {
      const ens = new Set(g);
      const inclus = gardes.some(k => k.size < ens.size && [...k].every(x => ens.has(x)));
      if (!inclus) gardes.push(ens);
    }
    return gardes.map(k => [...k].sort((a, b) => a - b));
  }

  function urlCadastre(p, zoom = 18) {
    return `https://cadastre.data.gouv.fr/map?style=vector&parcelleId=${p.id}#${zoom}/${p.pt.y.toFixed(6)}/${p.pt.x.toFixed(6)}`;
  }
  function liens(ps) {
    const c = ps[0].pt;
    return {
      maps: `https://www.google.com/maps?q=${c.y.toFixed(6)},${c.x.toFixed(6)}`,
      bing: `https://www.bing.com/maps?cp=${c.y.toFixed(6)}~${c.x.toFixed(6)}&lvl=19&style=a&sp=point.${c.y.toFixed(6)}_${c.x.toFixed(6)}_${encodeURIComponent(ps.map(p => p.ref).join(" + "))}`,
      cadastre: ps.map(p => ({ ref: p.ref, url: urlCadastre(p) })),
    };
  }

  const API = { normaliser, chargerParcelles, construireVoisins, parcellesSeules, groupesContigus, sansInclus, liens, urlCadastre, pointInterieur, bordureCommune };
  if (typeof module !== "undefined" && module.exports) module.exports = API; else root.Core = API;
})(typeof self !== "undefined" ? self : this);
