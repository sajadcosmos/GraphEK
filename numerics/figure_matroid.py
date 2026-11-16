import numpy as np, matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
from verify import roots
from matroid_tools import forests_Kp, pg_f
plt.rcParams.update({"font.family":"serif","font.size":9,"axes.linewidth":0.6})
ACC="#1f4e79"; GREY="#888888"
def circ(ax,c,r,**kw):
    t=np.linspace(0,2*np.pi,400); ax.plot(c+r*np.cos(t),r*np.sin(t),**kw)
fig,axs=plt.subplots(1,2,figsize=(6.4,3.1))
ax=axs[0]
for p in range(5,13):
    z=roots(forests_Kp(p)); ax.scatter(z.real,z.imag,s=6,color="black",alpha=0.7,lw=0)
p=12; circ(ax,0,1,color=GREY,lw=0.8,ls="--",label=r"$|z|=1$")
circ(ax,-(p-1)/(2*p-3),1,color=ACC,lw=1.0,label=r"$|z+\frac{p-1}{2p-3}|=1$, $p=12$")
ax.set_aspect("equal"); ax.set_xlim(-1.7,1.1); ax.set_ylim(-1.2,1.2)
ax.axhline(0,color="#ccc",lw=0.4); ax.axvline(0,color="#ccc",lw=0.4)
ax.set_title(r"forest polynomials of $K_p$, $5\leq p\leq 12$",fontsize=9); ax.legend(loc="lower left",fontsize=6.5,frameon=False)
ax=axs[1]; r,q=4,2
z=roots(pg_f(r,q)); R=r/q**(r-1); rho=(r-1)/(q**(r-2)*(q+1))
ax.scatter(z.real,z.imag,s=14,color="black",lw=0,label="zeros")
circ(ax,0,R,color=GREY,lw=0.8,ls="--",label=r"$|z|=r/q^{r-1}$")
circ(ax,-(R-rho),R,color=ACC,lw=1.0,label="shifted disk")
ax.set_aspect("equal"); ax.set_xlim(-0.95,0.6); ax.set_ylim(-0.65,0.65)
ax.axhline(0,color="#ccc",lw=0.4); ax.axvline(0,color="#ccc",lw=0.4)
ax.set_title(r"independence polynomial of $PG(3,2)$",fontsize=9); ax.legend(loc="lower left",fontsize=6.5,frameon=False)
fig.tight_layout(); fig.savefig("../figures/fig_matroid.pdf"); fig.savefig("../figures/fig_matroid.png",dpi=200)
