"""Checks for the matroid corollaries and the random-graph theorem."""
import itertools, json, math, random
import numpy as np, networkx as nx
from verify import indep_counts, roots
from verify_new import forest_counts
from matroid_tools import forests_Kp, pg_f, ag_f
TOL = 1e-9
def qint(k, q): return (q**k - 1)//(q - 1)

def region_check(f, g, d):
    """Theorem 3.x with g_k lower extension bounds: |z|<=max (k+1)/g_k and shifted disk."""
    z = roots(f)
    rat = [(k+1)/g[k] for k in range(d)]
    R0 = max(rat)
    rho = max(rat[:d-1]) if d >= 2 else 0.0
    R = max(rho, rat[d-1])
    okA = all(abs(w) <= R0 + TOL for w in z)
    okB = all(abs(w + R - rho) <= R + TOL for w in z)
    return okA and okB, (max(abs(z)) if len(z) else 0, R0)

def gf2_rank(vecs):
    rows = list(vecs); r = 0
    for bit in range(32):
        piv = None
        for i in range(r, len(rows)):
            if rows[i] >> bit & 1: piv = i; break
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i] >> bit & 1: rows[i] ^= rows[r]
        r += 1
    return r

out = {}
# (1) simple binary matroids: random subsets of PG(r-1,2) points (nonzero vectors of F_2^r)
random.seed(5); cnt = dict(objects=0, ok=0); slack = []
for t in range(300):
    r = random.randint(2, 5); pts = list(range(1, 2**r))
    n = random.randint(r, min(len(pts), 14)); E = random.sample(pts, n)
    if gf2_rank(E) < r: continue
    f = [0]*(r+1)
    for k in range(r+1):
        for S in itertools.combinations(E, k):
            if gf2_rank(S) == k: f[k] += 1
    g = [max(r-k, n - qint(k, 2)) for k in range(r)]
    ok, (mx, R0) = region_check(f, g, r)
    cnt["objects"] += 1; cnt["ok"] += ok; slack.append(mx/R0)
out["simple_binary_matroids"] = dict(cnt, max_ratio_true_over_bound=max(slack))
# (2) projective and affine geometries: exact extension counts
pg = dict(objects=0, ok=0)
for q in [2,3,4,5]:
    for r in range(2, 7):
        if qint(r, q) > 4000: continue
        f = pg_f(r, q); n = qint(r, q)
        g = [n - qint(k, q) for k in range(r)]
        ok, _ = region_check(f, g, r); pg["objects"] += 1; pg["ok"] += ok
        ag = ag_f(r, q); N = q**(r-1)
        g2 = [N] + [N - q**(k-1) for k in range(1, r)]
        ok2, _ = region_check(ag, g2, r); pg["objects"] += 1; pg["ok"] += ok2
out["projective_affine"] = pg
# (3) graphic matroids of simple graphs (atlas, m<=13) with closure bound C(k+1,2)
gm = dict(objects=0, ok=0, strictly_better_than_rank=0)
for G in nx.graph_atlas_g()[1:]:
    m = G.number_of_edges()
    if not (1 <= m <= 13): continue
    p = G.number_of_nodes(); c = nx.number_connected_components(G); r = p - c
    f = forest_counts(G)
    g = [max(r-k, m - math.comb(k+1, 2)) for k in range(r)]
    ok, (mx, R0) = region_check(f, g, r)
    gm["objects"] += 1; gm["ok"] += ok; gm["strictly_better_than_rank"] += R0 < r - 1e-12
out["graphic"] = gm
# (4) complete graphs K_p, p<=14: |z|<=1 and |z+(p-1)/(2p-3)|<=1
kp = dict(objects=0, ok=0, maxmod={})
for p in range(3, 15):
    f = forests_Kp(p); z = roots(f)
    ok = all(abs(w) <= 1 + TOL for w in z) and all(abs(w + (p-1)/(2*p-3)) <= 1 + TOL for w in z)
    kp["objects"] += 1; kp["ok"] += ok; kp["maxmod"][p] = round(float(max(abs(z))), 4)
out["complete_graph_forests"] = kp
# (5) random graphs G(n,p): region with sigma_{t,s}; empirical frequency of the events
rg = {}
random.seed(17)
for (n, pr) in [(12, 0.3), (12, 0.5), (14, 0.5), (14, 0.7)]:
    N = n*(n-1)//2; eps = 0.05
    t = math.sqrt(N*math.log(2/eps)/2); s = math.sqrt((n-1)*math.log(2*n/eps)/2)
    m0 = max(0.0, N*pr - t); d0 = max(0.0, (n-1)*pr - s)
    sigma = max((n - 1 - 2*m0/n)/2, (n - 2 - d0)/3)
    c = n - sigma; events = 0; holds = 0; trials = 400
    for k in range(trials):
        G = nx.gnp_random_graph(n, pr, seed=random.randint(0, 10**9))
        degs = [d for _, d in G.degree()]
        ev = (G.number_of_edges() >= m0) and (min(degs) >= d0)
        events += ev
        if ev:
            z = roots(indep_counts(G))
            holds += all(abs(1 + c*w) <= n*abs(w) + 1e-9 for w in z)
    rg[f"n={n},p={pr}"] = dict(event_freq=events/trials, guaranteed=1-eps, region_holds_on_event=holds==events,
                               reach=round(1/(n-c), 4))
out["random_graphs"] = rg
print(json.dumps(out, indent=1)); json.dump(out, open("summary_matroid.json", "w"), indent=1)
