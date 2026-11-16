"""Numerical verification of the zero-location theorems for independence and
domination polynomials on (i) every graph of order <= 7 (networkx atlas) and
(ii) random / structured families of larger order.  Writes summary JSON."""
import itertools, json, math, random, sys
import numpy as np, networkx as nx

def indep_counts(G):
    V = list(G.nodes()); n = len(V); idx = {v:i for i,v in enumerate(V)}
    nb = [0]*n
    for u,v in G.edges(): nb[idx[u]] |= 1<<idx[v]; nb[idx[v]] |= 1<<idx[u]
    cnt = [0]*(n+1)
    # enumerate independent sets by recursion
    def rec(i, mask, size, forb):
        if i == n:
            cnt[size] += 1; return
        rec(i+1, mask, size, forb)
        if not (forb >> i) & 1:
            rec(i+1, mask | (1<<i), size+1, forb | nb[i])
    rec(0, 0, 0, 0)
    while len(cnt) > 1 and cnt[-1] == 0: cnt.pop()
    return cnt

def max_indep_sizes(G):
    sizes = set()
    for c in nx.find_cliques(nx.complement(G)): sizes.add(len(c))
    return sizes

def dom_counts(G):
    V = list(G.nodes()); n = len(V); idx = {v:i for i,v in enumerate(V)}
    cl = [1<<i for i in range(n)]
    for u,v in G.edges(): cl[idx[u]] |= 1<<idx[v]; cl[idx[v]] |= 1<<idx[u]
    full = (1<<n)-1; cnt = [0]*(n+1)
    for S in range(1<<n):
        cov = 0; s = S; k = 0
        while s:
            b = s & -s; i = b.bit_length()-1; cov |= cl[i]; s ^= b; k += 1
        if cov == full: cnt[k] += 1
    return cnt

def roots(c):
    c = list(c)
    while c and c[-1] == 0: c.pop()
    if len(c) <= 1: return np.array([])
    return np.roots(c[::-1])

TOL = 1e-7
def check_indep_all(G, I, rts, n, delta):
    """Theorem C: |z| >= 1/n and |1 + c z| <= n|z| with c=(n+1+delta)/2."""
    c = (n+1+delta)/2
    ok1 = all(abs(z) >= 1/n - TOL for z in rts)
    ok2 = all(abs(1 + c*z) <= n*abs(z) + TOL for z in rts)
    return ok1, ok2

def wc_params(n, alpha, Delta):
    s = Delta+1
    rho = max([(k+1)/max(alpha-k, n-k*s) for k in range(alpha-1)] or [0])
    Rlast = alpha/max(1, n-(alpha-1)*s)
    R = max(rho, Rlast)
    return rho, R

def check_wc(rts, n, alpha, Delta):
    rho, R = wc_params(n, alpha, Delta)
    okA = all(abs(z) <= alpha + TOL for z in rts)
    okB = all(abs(z + (alpha+1)/2) <= alpha + TOL for z in rts) if alpha >= 2 else True
    okC = all(abs(z + R - rho) <= R + TOL for z in rts)
    okD = all(abs(z) <= R + TOL for z in rts) if rho <= R else True
    return okA, okB, okC, rho, R

def check_dom(rts, n, iso):
    R = max(n-iso, (n-1)/2); rho = (n-1)/2
    return all(abs(z + R - rho) <= R + TOL for z in rts) and all(abs(z) <= R + TOL for z in rts)

def main():
    out = {"atlas": {}, "wellcovered": [], "random": {}}
    graphs = nx.graph_atlas_g()[1:]
    stats = dict(graphs=0, indep_ok=0, wc=0, wc_ok=0, dom_ok=0, dom_graphs=0)
    wc_records = []
    inner_gain = []   # how far the inner region pushes beyond 1/n along +real axis
    for G in graphs:
        n = G.number_of_nodes()
        if n == 0: continue
        stats["graphs"] += 1
        delta = min(d for _,d in G.degree()); Delta = max(d for _,d in G.degree())
        I = indep_counts(G); alpha = len(I)-1; r = roots(I)
        a, b = check_indep_all(G, I, r, n, delta)
        if a and b: stats["indep_ok"] += 1
        else: print("INDEP FAIL", n, G.edges(), I)
        if max_indep_sizes(G) == {alpha}:
            stats["wc"] += 1
            okA, okB, okC, rho, R = check_wc(r, n, alpha, Delta)
            if okA and okB and okC: stats["wc_ok"] += 1
            else: print("WC FAIL", n, list(G.edges()), I)
            if len(r):
                wc_records.append(dict(n=n, alpha=alpha, Delta=Delta, maxmod=float(max(abs(r))),
                                       maxre=float(max(r.real)), rho=rho, R=R))
        if n <= 7:
            D = dom_counts(G); iso = sum(1 for _,d in G.degree() if d == 0)
            stats["dom_graphs"] += 1
            if check_dom(roots(D), n, iso): stats["dom_ok"] += 1
            else: print("DOM FAIL", n, list(G.edges()), D)
    out["atlas"] = stats
    out["wellcovered_atlas"] = wc_records
    print(json.dumps(stats))
    # random graphs
    random.seed(2026); rstats = dict(indep=0, indep_ok=0, dom=0, dom_ok=0)
    for trial in range(1500):
        n = random.randint(8, 14); p = random.choice([0.15,0.3,0.5,0.7,0.85])
        G = nx.gnp_random_graph(n, p, seed=random.randint(0,10**9))
        delta = min(d for _,d in G.degree())
        I = indep_counts(G); r = roots(I)
        rstats["indep"] += 1
        if all(check_indep_all(G, I, r, n, delta)): rstats["indep_ok"] += 1
        else: print("RAND INDEP FAIL", n, I)
        if n <= 13:
            D = dom_counts(G); iso = sum(1 for _,d in G.degree() if d == 0)
            rstats["dom"] += 1
            if check_dom(roots(D), n, iso): rstats["dom_ok"] += 1
            else: print("RAND DOM FAIL", n, D)
    out["random"] = rstats; print(json.dumps(rstats))
    # structured well-covered families: coronas H o K1 and clique unions
    wstats = dict(corona=0, corona_ok=0, cliques=0, cliques_ok=0)
    for trial in range(400):
        h = random.randint(2, 9); H = nx.gnp_random_graph(h, random.choice([0.2,0.5,0.8]), seed=trial)
        G = nx.corona_product(H, nx.empty_graph(1)) if hasattr(nx,'corona_product') else None
        if G is None:
            G = H.copy()
            for v in list(H.nodes()): G.add_edge(v, ('p', v))
        n = G.number_of_nodes(); Delta = max(d for _,d in G.degree())
        I = indep_counts(G); alpha = len(I)-1; r = roots(I)
        assert alpha == h
        okA, okB, okC, rho, R = check_wc(r, n, alpha, Delta)
        wstats["corona"] += 1; wstats["corona_ok"] += okA and okB and okC
    for a_ in range(1, 7):
        for s in range(1, 7):
            G = nx.disjoint_union_all([nx.complete_graph(s) for _ in range(a_)])
            n = G.number_of_nodes(); Delta = s-1
            I = indep_counts(G); alpha = len(I)-1; r = roots(I)
            okA, okB, okC, rho, R = check_wc(r, n, alpha, Delta)
            wstats["cliques"] += 1; wstats["cliques_ok"] += okA and okB and okC
    out["structured"] = wstats; print(json.dumps(wstats))
    json.dump(out, open("summary.json","w"), indent=1)

if __name__ == "__main__":
    main()
