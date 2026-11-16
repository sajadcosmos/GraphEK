"""Numerical checks for the new results: pure complexes (matroids), pure filters
(well-dominated and well-totally-dominated graphs), average-degree Apollonius disk."""
import itertools, json, random, math
import numpy as np, networkx as nx
from verify import indep_counts, dom_counts, roots
TOL = 1e-7

def total_dom_counts(G):
    V = list(G.nodes()); n = len(V); idx = {v:i for i,v in enumerate(V)}
    op = [0]*n
    for u,v in G.edges(): op[idx[u]] |= 1<<idx[v]; op[idx[v]] |= 1<<idx[u]
    full = (1<<n)-1; cnt = [0]*(n+1); fam = []
    for S in range(1<<n):
        cov = 0; s = S
        while s:
            b = s & -s; cov |= op[b.bit_length()-1]; s ^= b
        if cov == full: cnt[bin(S).count("1")] += 1; fam.append(S)
    return cnt, fam

def dom_family(G):
    V = list(G.nodes()); n = len(V); idx = {v:i for i,v in enumerate(V)}
    cl = [1<<i for i in range(n)]
    for u,v in G.edges(): cl[idx[u]] |= 1<<idx[v]; cl[idx[v]] |= 1<<idx[u]
    full = (1<<n)-1; fam = []
    for S in range(1<<n):
        cov = 0; s = S
        while s:
            b = s & -s; cov |= cl[b.bit_length()-1]; s ^= b
        if cov == full: fam.append(S)
    return fam

def minimal_sizes(fam):
    fs = set(fam); sizes = set()
    for S in fam:
        s = S; minimal = True
        while s:
            b = s & -s; s ^= b
            if (S ^ b) in fs: minimal = False; break
        if minimal: sizes.add(bin(S).count("1"))
    return sizes

def check_pure_filter_inner(cnt, n, g):
    r = roots(cnt); r = r[abs(r) > 1e-9]
    N = n - g; c = (N+1)/2
    ok = all(N*abs(z) >= 1 - TOL for z in r) and all(abs(1 + c*z) <= N*abs(z) + TOL for z in r)
    return ok, r

def forest_counts(G):
    E = list(G.edges()); m = len(E); n = G.number_of_nodes(); nodes = list(G.nodes())
    idx = {v:i for i,v in enumerate(nodes)}
    cnt = [0]*(m+1)
    for mask in range(1<<m):
        parent = list(range(n)); ok = True; k = 0
        def find(x):
            while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
            return x
        for i in range(m):
            if mask >> i & 1:
                k += 1
                a, b = find(idx[E[i][0]]), find(idx[E[i][1]])
                if a == b: ok = False; break
                parent[a] = b
        if ok: cnt[k] += 1
    while cnt and cnt[-1] == 0: cnt.pop()
    return cnt

def check_pure_complex(cnt, ground):
    d = len(cnt)-1; r = roots(cnt)
    okA = all(abs(z) <= d + TOL for z in r)
    okB = all(abs(z + (d+1)/2) <= d + TOL for z in r) if d >= 2 else True
    okC = all(abs(1 + (ground+1)/2*z) <= ground*abs(z) + TOL for z in r)
    return okA and okB and okC

def main():
    out = {}
    atlas = [G for G in nx.graph_atlas_g()[1:] if G.number_of_nodes() >= 2]
    # well-dominated / well-totally-dominated
    wd = dict(graphs=0, ok=0); wtd = dict(graphs=0, ok=0); wd_examples = []
    gap = []
    for G in atlas:
        n = G.number_of_nodes()
        fam = dom_family(G); sz = minimal_sizes(fam)
        if len(sz) == 1:
            g = sz.pop()
            if g < n:
                cnt = dom_counts(G); ok, r = check_pure_filter_inner(cnt, n, g)
                wd["graphs"] += 1; wd["ok"] += ok
                if len(r): gap.append(min(abs(r))*(n-g))
                wd_examples.append((n, g, [float(abs(z)) for z in r]))
        if min(d for _,d in G.degree()) >= 1:
            cnt, fam = total_dom_counts(G); sz = minimal_sizes(fam)
            if len(sz) == 1:
                g = sz.pop()
                if g < n:
                    ok, _ = check_pure_filter_inner(cnt, n, g); wtd["graphs"] += 1; wtd["ok"] += ok
    wd["min_ratio_|z|(n-g)"] = min(gap) if gap else None
    out["well_dominated"] = wd; out["well_totally_dominated"] = wtd
    # average-degree theorem on atlas + random
    def avg_ok(G):
        n = G.number_of_nodes(); degs = [d for _,d in G.degree()]
        dbar = sum(degs)/n; dl = min(degs)
        sigma = max((n-1-dbar)/2, (n-2-dl)/3); c = n - sigma
        r = roots(indep_counts(G))
        return all(abs(1 + c*z) <= n*abs(z) + TOL for z in r), (n+1+dbar)/2 - (n+1+dl)/2
    av = dict(graphs=0, ok=0, strict_improvement=0)
    for G in atlas:
        ok, imp = avg_ok(G); av["graphs"] += 1; av["ok"] += ok; av["strict_improvement"] += imp > 1e-12
    random.seed(11)
    for t in range(1500):
        n = random.randint(8, 14); G = nx.gnp_random_graph(n, random.choice([0.2,0.4,0.6,0.8]), seed=t)
        ok, imp = avg_ok(G); av["graphs"] += 1; av["ok"] += ok; av["strict_improvement"] += imp > 1e-12
    out["average_degree"] = av
    # matroids: uniform U_{r,n} and graphic matroids of atlas graphs with m <= 13
    um = dict(matroids=0, ok=0)
    for n in range(2, 21):
        for r in range(1, n+1):
            cnt = [math.comb(n, k) for k in range(r+1)]
            um["matroids"] += 1; um["ok"] += check_pure_complex(cnt, n)
    gm = dict(matroids=0, ok=0)
    for G in atlas:
        if 1 <= G.number_of_edges() <= 13:
            cnt = forest_counts(G); gm["matroids"] += 1; gm["ok"] += check_pure_complex(cnt, G.number_of_edges())
    out["uniform_matroids"] = um; out["graphic_matroids"] = gm
    print(json.dumps(out, indent=1))
    json.dump(out, open("summary_new.json", "w"), indent=1)
    json.dump(wd_examples, open("wd_examples.json", "w"))

if __name__ == "__main__":
    main()
