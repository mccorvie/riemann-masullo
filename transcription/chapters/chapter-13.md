## PDF page 521

CHAPTER 13

**Zeros of Hecke $L$-functions**

13.1.    Recollections on the Explicit Formulas                                 522
13.2.    Holomorphic families of test functions                                 522
13.3.    Main Theorems on the location of the zeros                             522
13.3.1.  The Divisor of the Hecke $L$-function $L$ on $\Omega(C_F)$                        522

521

## PDF page 522

522                    CHAPTER 13.   ZEROS OF HECKE L-FUNCTIONS

In this Chapter, we show how to deduce information about the zeros of Hecke $L$-functions of an arbitrary number field $F$, from the Trace Formula proved in Theorem 12.5.1.1.

**13.1.  Recollections on the Explicit Formulas**

**13.2.  Holomorphic families of test functions**

**13.3.  Main Theorems on the location of the zeros**

Let $F$ be a number field.

We will then be showing how to use the Trace Formula from Theorem 12.5.1.1 to deduce information on the zeros of the Hecke $L$-functions of $F$.

**13.3.1.  The Divisor of the Hecke $L$-function $L$ on $\Omega(C_F)$.** We record here below the statement of the Trace Formula, established in Theorem 12.5.1.1

THEOREM 13.3.1.1 (Trace Formula). *Let $F$ be a number field.* $^{1}$

*We define, on the set $\{c \in \Omega(C_F) : L(c) = 0\}$, the counting function $N_{\mathrm{spec}}(c)$ assigned by the formula:*

$$
N_{\mathrm{spec}}(c) := \min\left\{N(c),\,[F:\mathbf{Q}]\right\} \tag{13.3.1.1}
$$

*where $N(c)$ is the multiplicity of the zero $c$ of the Hecke $L$-function $L(c)$.*

*Let $\varphi \in \mathcal{D}(C_F)$ be a test function. Assume, upon choosing a continuous homomorphic section $\tau$ to the idelic norm, that we have, for all integers $0 \le k \le [F:\mathbf{Q}]-1$:*

$$
\left(\frac{\partial^{k}}{\partial s^{k}}\int_{\mathbf{R}_{>0}}\chi(\tau(t))t^{s}\left(\int_{C_{F}^{1}}\varphi(\tau(t)g)\chi(g)\,\mathrm{d}\bar{\mu}_{1}(g)\right)\frac{\mathrm{d}t}{t}\right)_{s=-ix_{0}(\chi)}=0 \tag{13.3.1.2}
$$

*for all $\chi \in \widehat{C_F}$, with $x_{0}(\chi) \in \mathbf{R}$ the unique real number such that $\chi(\tau(t)) = t^{ix_{0}(\chi)}$ as smooth functions on $\mathbf{R}_{>0}$.*

*Then the sums on each side of the identity:*

$$
\sum_{c \in \Omega(C_{F}):\,L(c)=0,\,\sigma(c)=1/2} N_{\mathrm{spec}}(c)\int_{C_{F}}\varphi(g)c(g)|g|_{F}^{-1/2}\,\mathrm{d}\bar{\mu}(g)=\int_{C_{F}}\varphi(g)|g|_{F}^{-1/2}\,\mathrm{d}\bar{\mu}(g)+\int_{C_{F}}\varphi(g)|g|_{F}^{1/2}\,\mathrm{d}\bar{\mu}(g) \tag{13.3.1.3}
$$

$$
-\sum_{v \in S_{F,\infty}}\int'_{F_v^\times,\alpha_{v,0}}\frac{\varphi(g)|g|_{v}^{1/2}}{|1-g|_{v}}\,\mathrm{d}\mu_{v}(g) \tag{13.3.1.4}
$$

$$
-\sum_{v \in S_{F,f}}\log(q_{v})\int'_{F_v^\times,\alpha_{v,0}}\frac{\varphi(g)|g|_{v}^{1/2}}{|1-g|_{v}}\,\mathrm{d}\mu_{v}(g) \tag{13.3.1.5}
$$

*converge, and their formation is continuous with respect to the subspace topology on the $[F:\mathbf{Q}]$-codimensional linear subspace $A \subset \mathcal{D}(C_F)$ defined by the vanishing conditions from* (13.3.1.2). *They define the same continuous functional on $A$.*

Upon combining Theorem 13.3.1.1 and Theorem **??**, we obtain the following:

THEOREM 13.3.1.2 (Divisor of $L(s,\chi)$). $^{2}$

$^{3}$

---

$^{1}$Correct statement.

$^{2}$Insert statement.

$^{3}$State and prove the Main Theorems, also explaining how to deduce them by approximation $\varphi \to e^{-s|\log(t)|}$ as $\mathrm{Re}(s) > 1$.
