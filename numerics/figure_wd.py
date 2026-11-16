import numpy as np, networkx as nx
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
from verify import dom_counts, roots
from verify_new import dom_family, minimal_sizes
plt.rcParams.update({"font.family":"serif","font.size":9,"axes.linewidth":0.6})
ACC="#1f4e79"; GREY="#888888"
n=7; pools={2:[],3:[]}
for G in nx.graph_atlas_g()[1:]:
    if G.number_of_nodes()!=n: continue
    sz=minimal_sizes(dom_family(G))
    if len(sz)==1:
        g=sz.pop()
        if g in pools:
            r=roots(dom_counts(G)); pools[g].extend(r[abs(r)>1e-9])
fig,axs=plt.subplots(1,2,figsize=(6.4,3.1))
for ax,g in zip(axs,[2,3]):
    W=np.array(pools[g]); N=n-g; c=(N+1)/2
    th=np.linspace(0,2*np.pi,600)
    t=(c*np.cos(th)+np.sqrt(N**2-c**2*np.sin(th)**2))/(N**2-c**2)
    ax.fill(t*np.cos(th),t*np.sin(th),color=ACC,alpha=0.10)
    ax.plot(t*np.cos(th),t*np.sin(th),color=ACC,lw=1.0,label=r"$|1+\frac{N+1}{2}z|=N|z|$")
    ax.plot(np.cos(th)/N,np.sin(th)/N,color=GREY,lw=0.8,ls="--",label=r"$|z|=1/N$")
    ax.scatter(W.real,W.imag,s=4,color="black",alpha=0.6,lw=0)
    ax.set_aspect("equal"); ax.set_xlim(-3.2,1.2); ax.set_ylim(-2.0,2.0)
    ax.axhline(0,color="#ccc",lw=0.4); ax.axvline(0,color="#ccc",lw=0.4)
    ax.set_title(rf"well-dominated, $n=7$, $\gamma={g}$ ($N={N}$)",fontsize=9)
axs[0].legend(loc="lower left",fontsize=7,frameon=False)
fig.tight_layout(); fig.savefig("../figures/fig_welldominated.pdf"); fig.savefig("../figures/fig_welldominated.png",dpi=200)
print({g:len(v) for g,v in pools.items()})
