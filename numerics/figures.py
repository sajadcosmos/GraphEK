import numpy as np, networkx as nx, random, json
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from verify import indep_counts, dom_counts, roots, max_indep_sizes
plt.rcParams.update({"font.family":"serif","font.size":9,"axes.linewidth":0.6})
ACC = "#1f4e79"; GREY="#888888"

def circle(ax, c, r, **kw):
    t = np.linspace(0, 2*np.pi, 400); ax.plot(c + r*np.cos(t), r*np.sin(t), **kw)

# ---- Figure 1: well-covered independence roots, alpha = 2 and 3 ----
random.seed(7)
pools = {2: [], 3: []}
for G in nx.graph_atlas_g()[1:]:
    I = indep_counts(G); a = len(I)-1
    if a in pools and max_indep_sizes(G) == {a}: pools[a].append(roots(I))
# add random well-covered graphs of order 8-10
for trial in range(6000):
    n = random.randint(8, 10); G = nx.gnp_random_graph(n, random.choice([0.4,0.55,0.7]), seed=trial)
    I = indep_counts(G); a = len(I)-1
    if a in pools and max_indep_sizes(G) == {a}: pools[a].append(roots(I))
fig, axs = plt.subplots(1, 2, figsize=(6.4, 3.0))
for ax, a in zip(axs, [2, 3]):
    R = np.concatenate(pools[a])
    circle(ax, 0, a, color=GREY, lw=0.8, ls="--", label=r"$|z|=\alpha$")
    circle(ax, -(a+1)/2, a, color=ACC, lw=1.0, label=r"$|z+\frac{\alpha+1}{2}|=\alpha$")
    ax.scatter(R.real, R.imag, s=3, color="black", alpha=0.6, lw=0)
    ax.axvline((a-1)/2, color=ACC, lw=0.5, ls=":")
    ax.set_aspect("equal"); ax.set_xlim(-a-0.6, a+0.6); ax.set_ylim(-a-0.6, a+0.6)
    ax.set_title(rf"$\alpha={a}$: {len(pools[a])} well-covered graphs", fontsize=9)
    ax.axhline(0, color="#ccc", lw=0.4); ax.axvline(0, color="#ccc", lw=0.4)
axs[0].legend(loc="lower left", fontsize=7, frameon=False)
fig.tight_layout(); fig.savefig("../figures/fig_wellcovered.pdf"); fig.savefig("../figures/fig_wellcovered.png", dpi=200)
counts = {a: len(pools[a]) for a in pools}

# ---- Figure 2: domination roots of all graphs of order 7 ----
n = 7; R = []
for G in nx.graph_atlas_g()[1:]:
    if G.number_of_nodes() == n:
        r = roots(dom_counts(G)); R.extend(r[abs(r) > 1e-9])
R = np.array(R)
fig, ax = plt.subplots(figsize=(3.6, 3.4))
circle(ax, 0, n, color=GREY, lw=0.8, ls="--", label=r"$|z|=n$")
circle(ax, -(n+1)/2, n, color=ACC, lw=1.0, label=r"$|z+\frac{n+1}{2}|=n$")
ax.scatter(R.real, R.imag, s=2, color="black", alpha=0.5, lw=0)
ax.set_aspect("equal"); ax.set_xlim(-n-1, n+1); ax.set_ylim(-n-1, n+1)
ax.axhline(0, color="#ccc", lw=0.4); ax.axvline(0, color="#ccc", lw=0.4)
ax.legend(loc="lower left", fontsize=7, frameon=False)
ax.set_title(f"Domination roots, all graphs of order {n}", fontsize=9)
fig.tight_layout(); fig.savefig("../figures/fig_domination.pdf"); fig.savefig("../figures/fig_domination.png", dpi=200)
ndom = int(sum(1 for G in nx.graph_atlas_g()[1:] if G.number_of_nodes()==n))

# ---- Figure 3: inner zero-free region for independence roots, n = 7, delta = 2 and 4 ----
fig, axs = plt.subplots(1, 2, figsize=(6.4, 3.0))
for ax, dl in zip(axs, [2, 4]):
    W = []
    for G in nx.graph_atlas_g()[1:]:
        if G.number_of_nodes() == n and min(d for _, d in G.degree()) == dl:
            W.extend(roots(indep_counts(G)))
    W = np.array(W)
    c = (n+1+dl)/2
    # boundary |1 + c z| = n |z| is a circle (Apollonius); sample it
    th = np.linspace(0, 2*np.pi, 600)
    t = (c*np.cos(th) + np.sqrt(c**2*np.cos(th)**2 + n**2 - c**2))/(n**2 - c**2)
    ax.plot(t*np.cos(th), t*np.sin(th), color=ACC, lw=1.0, label=r"$|1+cz|=n|z|$")
    circle(ax, 0, 1/n, color=GREY, lw=0.8, ls="--", label=r"$|z|=1/n$")
    ax.scatter(W.real, W.imag, s=4, color="black", alpha=0.6, lw=0)
    lim = 1.15*max(1/(n-c), 1.0)
    ax.set_xlim(-0.65, 1.05); ax.set_ylim(-0.6, 0.6); ax.set_aspect("equal")
    ax.axhline(0, color="#ccc", lw=0.4); ax.axvline(0, color="#ccc", lw=0.4)
    ax.set_title(rf"$n=7,\ \delta={dl}$ (all such graphs)", fontsize=9)
    # shade excluded region
    ax.fill(t*np.cos(th), t*np.sin(th), color=ACC, alpha=0.08)
axs[0].legend(loc="lower left", fontsize=7, frameon=False)
fig.tight_layout(); fig.savefig("../figures/fig_inner.pdf"); fig.savefig("../figures/fig_inner.png", dpi=200)
json.dump(dict(wc_counts=counts, dom_graphs_order7=ndom), open("fig_counts.json","w"))
print(counts, ndom)
