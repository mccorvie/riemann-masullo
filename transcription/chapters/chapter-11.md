## PDF page 475

**CHAPTER 11**

**The Shell Structure**

11.1. The Shell Structure 475

11.1.1. General convergence criteria 475

11.1.2. S-local carvings 480

11.2. The pieces of the puzzle: Paley-Wiener levels and Orbital Markushevich Bases 483

11.2.1. Paley-Wiener Levels 487

11.2.2. Orbital Markushevich Bases on the Paley-Wiener Levels 489

11.3. Orbital Kernels and Orbital Traces 491

11.3.1. Calculation of the Orbital Kernels by global to S-local degeneration on the orbital basis elements 491

11.3.1.1. Divisorial stratification of the ideles 491

11.3.2. Calculation of the Orbital Traces 495

**11.1. The Shell Structure**

The purpose of this subsection is to show that over the unbounded, bounded “below”, closed subsets

$$
C^{\ge 1/\Lambda}_F := \{g \in C_F : |g|_F \ge 1/\Lambda\}
$$

for $\Lambda > 0$ a fixed real number, we may let the non-Archimedean “components” of a Schwartz-Bruhat function on the adele $\mathbf A_F$ degenerate from $1_{\mathcal O_{F_v}}$ to $1_{\mathcal O_{F_v}^\times}$, in a manner that is convergent in $L^p(C^{\ge 1/\Lambda}_F,\bar\mu)$ for every $p \ge 1$.$^1$

**11.1.1. General convergence criteria.** We will be using this to construct operators from the truncations$^2$

$$
M_{(1/\Lambda,+\infty)} W^{s,2}_a \mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))
$$

to truncated subspaces of the $S$-local spaces:

$$
W^{s,2}_a \mathrm{H}_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})).
$$

The Geometric Schauder Bases will enable us to control the loss of information of this “degeneration process”.

We begin with a few general convergence criteria.

LEMMA 11.1.1.1. *We let $\{f_k\}_{k\ge 0} \subset \mathcal S(\mathbf A_F)$ be a sequence of Schwartz-Bruhat functions on $\mathbf A_F$. Assume that for every $g \in \mathrm{GL}_1(\mathbf A_F)$, $\lim_{k\ge 0} f_k(g)$ exists. Then, as a function of $g \in \mathrm{GL}_1(\mathbf A_F)$*

$$
f(g) := \lim_{k\to +\infty} f_k(g) \tag{11.1.1.1}
$$

*is Borel-measurable over $\mathrm{GL}_1(\mathbf A_F)$.*

---
$^1$Return here.

---
$^2$Return here.

475

## PDF page 476

**476** · **CHAPTER 11. THE SHELL STRUCTURE**

*Proof.* Each $f_k$, being a Schwartz-Bruhat function on $\mathbf A_F$, is continuous when pre-composed with the continuous map $\mathrm{GL}_1(\mathbf A_F) \to \mathbf A_F$, which is in turn the composition of the continuous identity map $\mathrm{GL}_1(\mathbf A_F) \to \mathbf A_F^\times$, with $\mathbf A_F^\times$ endowed with the subspace topology, followed by the topological embedding $\mathbf A_F^\times \subset \mathbf A_F$. As such, it is Borel measurable over $\mathrm{GL}_1(\mathbf A_F)$. By [Ru-2, p.15, Corollaries, (a)] countable limit of complex-valued Borel measurable functions is Borel measurable. $\square$

PROPOSITION 11.1.1.2. *We let $\{f_k\}_{k\ge 0} \subset \mathcal S(\mathbf A_F)$ be a sequence of Schwartz-Bruhat functions on $\mathbf A_F$. Let $\eta$ be a positive Radon measure on $\mathrm{GL}_1(\mathbf A_F)$, and $Z \subset \mathrm{GL}_1(\mathbf A_F)$ a Borel-measurable subset. Let $r \ge 1$ be a real number. Assume that for every $g \in Z$, $f(g) := \lim_{k\to +\infty} f_k(g)$ exists, and that there exists a Borel-measurable function $\alpha : F^\times Z \to \mathbf R_{\ge 0}$ such that:*

*(1) There exists a fractional ideal $I_Z \subset F$ such that for every $g \in Z$, $\sum_{\xi \in I_Z \cap F^\times} \alpha(\xi g)$ is absolutely convergent, and its value $J_F(\alpha)(g)$ is, as a function of $g \in Z$, Borel-measurable and an element of $L^r(Z,\eta|_Z)$.*

*(2) We have, for every $g \in F^\times Z$ and every integer $k \ge 0$*

$$
\sum_{\xi \in F^\times} |f_k(\xi g)| \le J_F(\alpha)(g). \tag{11.1.1.2}
$$

*Then*

*(1) for all $g \in Z$, the series*

$$
\sum_{\xi \in F^\times} f(\xi g) \tag{11.1.1.3}
$$

*is absolutely convergent. The function $\Phi_F(f)$ defined as the sum of the series in (11.1.1.3) over $Z$, and identically zero over $\mathrm{GL}_1(\mathbf A_F)-Z$, is Borel measurable over $\mathrm{GL}_1(\mathbf A_F)$.*

*(2) $\Phi_F(f)$ is an element of $L^r(Z,\eta|_Z)$, and we have*

$$
\Phi_F(f) = \lim_{k\to +\infty} \Phi_F(f_k) \tag{11.1.1.4}
$$

*with respect to the norm topology on $L^r(Z,\eta|_Z)$.*

Remark 11.1.1.3. We note that the orbit of the Borel set $Z \subset \mathrm{GL}_1(\mathbf A_F)$ under the free and proper left-translation action of $F^\times$ on $\mathrm{GL}_1(\mathbf A_F)$ from Proposition 11.1.1.2, is also a Borel set, since $F^\times Z$ is a countable union of Borel sets.

*Proof.* (1) : We let $g \in Z$ be fixed, and we denote by $\delta_{\{g\}}$ the finite, positive Radon measure on $\mathrm{GL}_1(\mathbf A_F)$ determined under [Fol, Thm.7.2] by the assignment of the functional

$$
\delta_{\{g\}} : C_c(\mathrm{GL}_1(\mathbf A_F)) \to \mathbf C
$$

defined by $\delta_{\{g\}}(f) := f(g)$.

Since the continuous action of $F^\times$ on $\mathrm{GL}_1(\mathbf A_F)$ by left-translation is free and discrete, the orbit $F^\times g = \{\xi g\}_{\xi \in F^\times}$ is a discrete subset of $\mathrm{GL}_1(\mathbf A_F)$. We endow it with the following Radon measure. We consider the $\mathbf C$-linear space $C_c(F^\times g)$ of continuous compactly supported functions, and define:

$$
\Delta_{\{g\}} : C_c(F^\times g) \to \mathbf C
$$

by $\Delta_{\{g\}}(\varphi) := \sum_{\xi \in F^\times} \varphi(\xi g)$. By [Fol, Thm.7.2], $\Delta_{\{g\}}$ determines a unique complex Radon measure on $F^\times g$, which we denote $\mu_g$. The Radon measure $\mu_g$ is real, positive, and it agrees with the counting measure on $F^\times g$ by uniqueness (see [Bou-II, INT VII.31, §2, Prop.4(a)], applied to $X = F^\times g$ endowed with the discrete topology, $H = F^\times$ as a discrete topological group acting freely and properly on $X$ by left-translation), since it is $F^\times$-invariant (in the sense of [Bou-II, INT VII.2, §1, Def.1(a)]).

## PDF page 477

**11.1. THE SHELL STRUCTURE** · **477**

Each function $f_k \in \mathcal S(\mathbf A_F)$ is continuous over $F^\times g$ with respect to the discrete topology, and it is an element of $L^r(F^\times g,\mu_g)$ for every real number $r \ge 1$ by Lemma 2.2.2.1(2).

By Fatou’s Lemma (see [Fol, Thm.2.18]), we have

$$
\sum_{\xi \in F^\times} |f(\xi g)| = \int_{F^\times g} |f(h)|\,\mathrm{d}\mu_g(h) \le \liminf_{k\to +\infty} \int_{F^\times g} |f_k(h)|\,\mathrm{d}\mu_g(h). \tag{11.1.1.5}
$$

By assumption (2), the rightmost side of (11.1.1.5) is bounded above by $J_F(\alpha)(g)$, which proves that the series in (11.1.1.3) is absolutely convergent pointwise over $Z$.

We now choose an exhaustion of $\mathrm{GL}_1(\mathbf A_F)$ by compact subsets $\{K_m\}_{m\ge 0}$, i.e. a sequence of compact subsets $K_m \subset \mathrm{GL}_1(\mathbf A_F)$ such that $K_m \subset \mathrm{Int}(K_{m+1})$ and $\mathrm{GL}_1(\mathbf A_F) = \bigcup_{m\ge 0} K_m$. Such exhaustion exists since $\mathrm{GL}_1(\mathbf A_F)$ is locally compact, Hausdorff and second-countable. For each integer $m \ge 0$, we choose a continuous compactly supported function $\varphi_m \in C_c(\mathrm{GL}_1(\mathbf A_F))$ whose support is contained in $K_{m+1}$, and such that $\varphi_m(K_m) = 1$. Such sequence $\{\varphi_m\}_{m\ge 0} \subset C_c(\mathrm{GL}_1(\mathbf A_F))$ exists by [Fol, Thm.4.15].

It satisfies $\lim_{m\to +\infty} \varphi_m(g) = 1$ pointwise over $\mathrm{GL}_1(\mathbf A_F)$ as Borel-measurable functions. The series $\sum_{\xi \in F^\times} (\varphi_m f)(\xi g)$ is absolutely convergent for every integer $m \ge 0$ and for every $g \in Z$, since it is bounded above by $\sum_{\xi \in F^\times} |f(\xi g)|$, which converges by the foregoing.

We now observe that the sum

$$
\Phi_m(g) := \sum_{\xi \in F^\times} (\varphi_m f)(\xi g) \tag{11.1.1.6}
$$

is, for each $g \in Z$, finite, since $\mathrm{supp}(\varphi_m f) \subset K_{m+1}$, and $F^\times g \cap K_{m+1}$ is finite, since $F^\times g$ is discrete and $K_{m+1}$ is compact in $\mathrm{GL}_1(\mathbf A_F)$.

We let $U_0$ be an arbitrary open subset of $\mathrm{GL}_1(\mathbf A_F)$ with compact closure. The function $\Phi_m$ from (11.1.1.6) is, over $U_0 \cap Z$, of the form

$$
\Phi_m(\cdot) = \sum_{i=1}^N (\varphi_m f)(\xi_i\cdot) \tag{11.1.1.7}
$$

where $N$ depends only on $m$ and $U_0$, and $\{\xi_1,\dots,\xi_N\}$ is the finite set of elements of $F^\times$ comprising the intersection $F^\times \cap (U_0^{-1} K_{m+1})$, the finiteness being ensured by the compactness of the closure of $U_0^{-1} K_{m+1}$, which holds since $(\overline{U}_0)^{-1}K_{m+1}$ is compact by [DE, Lemma 1.1.3(d)]. It follows that $\Phi_m$ is, over $U_0 \cap Z$, a finite sum of Borel-measurable functions (since the left-translation action by $F^\times$ on $\mathrm{GL}_1(\mathbf A_F)$ is continuous). Here we are using the foregoing applied to the Schwartz-Bruhat functions $f_k(\xi_i\cdot)$ in place of $f_k$, and to $f(\xi_i\cdot)$ in place of $f$, to deduce that each $f(\xi_i\cdot)$, for $1 \le i \le N$, is also Borel-measurable over $Z$.

Being $U_0$ arbitrary, as an open subset of $\mathrm{GL}_1(\mathbf A_F)$ with compact closure, and being $\mathrm{GL}_1(\mathbf A_F)$ locally compact Hausdorff, it follows that $\Phi_m$ is Borel-measurable over $Z$, because there exists a covering $\{U_{0,i}\}_{i\in I}$ by open subsets of $\mathrm{GL}_1(\mathbf A_F)$ with compact closure, such that for each $i \in I$, $\Phi_m$ is Borel-measurable over $U_{0,i} \cap Z$.

By Dominated Convergence, applied to the sequence $\{\varphi_m f\}_{m\ge 0} \subset L^1(F^\times g,\mu_g)$, dominated by $\xi g \mapsto |f(\xi g)|$, we deduce that $\Phi_m \to \Phi_F(f)$ pointwise over $Z$, and hence $\Phi_F(f)$ is Borel-measurable over $Z$ (endowed with the subspace topology inherited from $\mathrm{GL}_1(\mathbf A_F)$, and hence the induced $\sigma$-algebra of Borel sets) by Lemma 11.1.1.1 (see also [Ru-2, p.15, Corollaries, (a)]). Since $Z$ is a Borel set of $\mathrm{GL}_1(\mathbf A_F)$, the extension by zero of $\Phi_F(f)$ to a complex-valued function on $\mathrm{GL}_1(\mathbf A_F)$ is also Borel-measurable.

(2) : Since $|\Phi_F(f_k)| \le J_F(\alpha)$ over $Z$ by (11.1.1.11), we have $\Phi_F(f) \in L^r(Z,\eta|_Z)$ by assumption (1). By (11.1.1.11) and Dominated Convergence, applied, for every $g \in Z$, to $\{f_k\}_{k\ge 0} \subset L^1(F^\times g,\mu_g)$, the limit of the sequence $\{\Phi_F(f_k)\}_{k\ge 0}$ in the $L^r(F\times g,\mu_g)$-norm topology, is $\Phi_F(f)$.

This means that $\Phi_F(f_k) \to \Phi_F(f)$ pointwise over $Z$.

## PDF page 478

**478** · **CHAPTER 11. THE SHELL STRUCTURE**

By (11.1.1.11) and the assumption that $J_F(\alpha) \in L^r(Z,\eta|_Z)$, we have, by another application of Dominated Convergence, applied to the sequence of functions $\{\Phi_F(f_k)\}_{k\ge 0} \subset L^r(Z,\eta|_Z)$ whose pointwise limit is $\Phi_F(f)$, and which are all dominated by $J_F(\alpha)$ over $Z$, that $\Phi_F(f_k) \to \Phi_F(f)$ in $L^r(Z,\eta|_Z)$. $\square$

We now call $T := \tau(\mathbf R_{>0})$, recalling that we have chosen a continuous homomorphic section $\tau$ to the idelic norm. $T$ is a closed subgroup of $\mathrm{GL}_1(\mathbf A_F)$ (see Lemma A.2.2.9(1)).

COROLLARY 11.1.1.4. *We let $\{f_k\}_{k\ge 0} \subset \mathcal S(\mathbf A_F)$ be a sequence of Schwartz-Bruhat functions on $\mathbf A_F$. Assume:*

*(1) for every $g \in \mathrm{GL}_1(\mathbf A_F)$, $f(g) := \lim_{k\to +\infty} f_k(g)$ exists.*

*(2) for each $g \in \mathrm{GL}_1(\mathbf A_F)$, there exists a function $\alpha_g : F^\times g \to \mathbf R_{\ge 0}$ and a fractional ideal $I_g \subset F$, such that*

*(a) The series $\sum_{\xi \in I_g \cap F^\times} \alpha_g(\xi)$ is absolutely convergent.*

*(b) We have, for every $g \in T\cdot E^1_F$, every $\xi \in F^\times$ and every integer $k \ge 0$*

$$
\sum_{\xi \in F^\times} |f_k(\xi g)| \le \sum_{\xi \in I_g \cap F^\times} \alpha_g(\xi). \tag{11.1.1.8}
$$

*Then, for each $g \in T\cdot E^1_F$, the series*

$$
\sum_{\xi \in F^\times} f(\xi g) \tag{11.1.1.9}
$$

*is absolutely convergent, the limit $\lim_{k\to +\infty} \Phi_F(f_k)(g)$ exists, and we have, as functions over $C_F$*

$$
\Phi_F(f) = \lim_{k\to +\infty} \Phi_F(f_k) \tag{11.1.1.10}
$$

*pointwise over $C_F$.*

We note that the upper bound to the series in (11.1.1.8) from Corollary 11.1.1.4(2) depends on $g \in C_F$.

*Proof.* We apply Proposition 11.1.1.2 to the Borel set $Z := \{g\}$, and $\eta := \delta_{\{g\}}$, the Dirac measure on $\mathrm{GL}_1(\mathbf A_F)$ concentrated at $\{g\}$. By (2.a) and (2.b), conditions (1) and (2) of Proposition 11.1.1.2 are satisfied with $r = 1$, and hence the series in (11.1.1.12) is absolutely convergent, and (11.1.1.13) holds with respect to the norm topology on $L^1(\{g\},\delta_{\{g\}})$, which is to say that $\Phi_F(f_k) \to \Phi_F(f)$ pointwise over $\mathrm{GL}_1(\mathbf A_F)$. Being each function $\Phi_F(f_k)$ and $\Phi_F(f)$, invariant under the left-translation action of $F^\times$ on $\mathrm{GL}_1(\mathbf A_F)$, the identity in (11.1.1.13) holds as functions over $C_F$. $\square$

We recall that we have chosen a continuous homomorphic section $\tau : \mathbf R_{>0} \to \mathrm{GL}_1(\mathbf A_F)$ to the idelic norm, and that such choice defines a closed subgroup $T := \tau(\mathbf R_{>0}) \subset \mathrm{GL}_1(\mathbf A_F)$, and provides the isomorphism of abelian topological groups

$$
\theta_{F,\tau} : \mathbf R_{>0} \times \mathrm{GL}_1(\mathbf A_F)^1 \xrightarrow{\;\simeq\;} T\cdot \mathrm{GL}_1(\mathbf A_F)^1 = \mathrm{GL}_1(\mathbf A_F)
$$

*from (A.2.2.12).*

We observe that the subset $T\cdot E^1_F \subset \mathrm{GL}_1(\mathbf A_F)$ is a Borel set, with $E^1_F$ the idelic fundamental domain of (A.2.3.14). Indeed, $T$ can be written as an increasing countable union of compact subsets, and $E^1_F$ is relatively compact, presenting $T\cdot E^1_F$ as an increasing countable union of relatively compact subsets with non-empty interior within $\mathrm{GL}_1(\mathbf A_F)$ (see Proposition A.2.3.10(1)), each of which is therefore a Borel set.

COROLLARY 11.1.1.5. *We let $\{f_k\}_{k\ge 0} \subset \mathcal S(\mathbf A_F)$ be a sequence of Schwartz-Bruhat functions on $\mathbf A_F$. Assume:*

*(1) for every $g \in \mathrm{GL}_1(\mathbf A_F)$, $f(g) := \lim_{k\to +\infty} f_k(g)$ exists.*

## PDF page 479

**11.1. THE SHELL STRUCTURE** · **479**

*(2) There exists a Borel-measurable function $\alpha : \mathrm{GL}_1(\mathbf A_F) \to \mathbf R_{\ge 0}$ and a fractional ideal $I \subset F$ such that:*

*(a) For every $g \in \mathrm{GL}_1(\mathbf A_F)$, the series $\sum_{\xi \in I \cap F^\times} \alpha(\xi g)$ is absolutely convergent, and its sum $J_F(\alpha)(g)$ is, as a function of $g \in \mathrm{GL}_1(\mathbf A_F)$, Borel-measurable and an element of $L^1(T\cdot E^1_F,(\delta_x \otimes \mu_1))$ for every $x \in T$.*

*(b) We have, for every integer $k \ge 0$*

$$
\sum_{\xi \in F^\times} |f_k(\xi g)| \le J_F(\alpha)(g) \tag{11.1.1.11}
$$

*over $T\cdot E^1_F$.*

*Then, for every character $\omega \in \widehat{C^1_F}$, and each $g \in \mathrm{GL}_1(\mathbf A_F)$, the integral*

$$
\Phi_{F,\omega}(f)(g) := \int_{E^1_F} \sum_{\xi \in F^\times} f(\xi g h)\,\omega(gh)\,\mathrm{d}\mu_1(h) \tag{11.1.1.12}
$$

*is absolutely convergent, the limit $\lim_{k\to +\infty} \Phi_{F,\omega}(f_k)(g)$ exists, and we have, as functions over $C_F/C^1_F$*

$$
\Phi_{F,\omega}(f) = \lim_{k\to +\infty} \Phi_{F,\omega}(f_k) \tag{11.1.1.13}
$$

*pointwise over $C_F/C^1_F$.*

*Proof.* We apply Proposition 11.1.1.2 to the choice $Z = T\cdot E^1_F$ and, for each $x \in T$, to $\eta := \delta_x \otimes \mu_1$. Since $|c(gh)| = |c(g)|$ for every $h \in E^1_F$ as per (11.1.1.12), since $E^1_F \subset \mathrm{GL}_1(\mathbf A_F)^1$, then the integral defining $\Phi_{F,\omega}(f)(g)$ in (11.1.1.12) is absolutely convergent by Proposition 11.1.1.2(2), since we have

$$
\int_{E^1_F} \sum_{\xi \in F^\times} f(\xi g h)\,c(gh)\,\mathrm{d}\mu_1(h) = c(x) \int_{E^1_F} \sum_{\xi \in F^\times} f(\xi x g_0)\,c(g_0)\,\mathrm{d}\mu_1(g_0) = c(x) \int_{T\cdot E^1_F} \Phi_F(f)(g')\,c(g'x^{-1})\,\mathrm{d}(\delta_x\otimes\mu_1)(g') \tag{11.1.1.14}
$$

writing $g = xg_0$ for unique $x \in T$ and $g_0 \in \mathrm{GL}_1(\mathbf A_F)$, for then renaming $g_0h$ as $g_0$ by $\mathrm{GL}_1(\mathbf A_F)^1$-invariance of $\mu_1$. We may assume $g_0$ is in $E^1_F$, since $\mathrm{GL}_1(\mathbf A_F)^1 = \bigcup_{\xi \in F^\times} \xi E^1_F$ by Proposition A.2.3.10, the union being disjoint.

Since $|c(g'x^{-1})| = 1$, Proposition 11.1.1.2(2) implies that $\Phi_F(f) \in L^1(T\cdot E^1_F,(\delta_x\otimes\mu_1))$ and hence the integral in the rightmost side of (11.1.1.14) is absolutely convergent.

Since we have, by Proposition D.1.2.4 [Bou-II, INT VII.52, §3, Thm.4(c)]

$$
\Phi_{F,\omega}(f_k)(g) = \int_{E^1_F} \Phi_F(f_k)(gh)\,\omega(gh)\,\mathrm{d}\mu_1(h)
$$

as $E^1_F$ is a fundamental domain for the continuous action of $F^\times$ by left translation on $\mathrm{GL}_1(\mathbf A_F)^1$, we have

$$
\Phi_{F,\omega}(f)(x) - \Phi_{F,\omega}(f_k)(x) = \omega(x) \int_{E^1_F} (\Phi_F(f_k)(g') - \Phi_F(f)(g'))\,\omega(g'x^{-1})\,\mathrm{d}(\delta_x\otimes\mu_1)(g')
$$

and hence

$$
\|\Phi_{F,\omega}(f) - \Phi_{F,\omega}(f_k)\|_{L^1(T_{v_0},\delta_x)} \le |c(x)|\,\|\Phi_F(f) - \Phi_F(f_k)\|_{L^1(T\cdot E^1_F,(\delta_x\otimes\mu_1))} \tag{11.1.1.15}
$$

then Proposition 11.1.1.2(2) implies that $\Phi_{F,\omega}(f_k) \to \Phi_{F,\omega}(f)$ pointwise over $T$.

Since both $\Phi_F(f)$ and $\Phi_F(f_k)$, for every integer $k \ge 0$, are $F^\times$-invariant functions over $\mathrm{GL}_1(\mathbf A_F)$, and the $L^1(E,\mu_1)$-norm of $\Phi_F(f)(x\cdot) - \Phi_F(f_k)(x\cdot)$ is preserved under left-translation by $\mathrm{GL}_1(\mathbf A_F)^1$, (11.1.1.15) implies that $\Phi_{F,\omega}(f_k) \to \Phi_{F,\omega}(f)$ pointwise over $\mathrm{GL}_1(\mathbf A_F) = T\cdot \mathrm{GL}_1(\mathbf A_F)^1$, and since both $\Phi_{F,\omega}(f_k)$ and $\Phi_{F,\omega}(f)$ are $F^\times$-invariant, we deduce that the mode of convergence in (11.1.1.13) is pointwise as functions over $C_F$. By $C^1_F$-invariance of each $\Phi_{F,\omega}(f_k)$ and $\Phi_{F,\omega}(f)$, the mode of convergence is also pointwise over $C_F/C^1_F$. $\square$

## PDF page 480

**480** · **CHAPTER 11. THE SHELL STRUCTURE**

**11.1.2. S-local carvings.** We are ready to establish the main result of this section.

For $F$ a number field, $\chi \in \widehat{C_F}$ a continuous character, $S$ a finite set of places of $F$ containing all the Archimedean places, and such that $\chi$ is unramified outside $S$, and $\mathrm{Pic}(\mathcal O_{F,S}) = 1$ (which implies $\mathrm{Pic}(\mathcal O_{F,S'}) = 1$ for all finite sets of places of $F$ containing $S$), we introduce the following notation.

We define the countable set:

$$
I_S := \{S' \subset \Sigma_F : S' \text{ is finite, } S \cap S' = \varnothing\} \tag{11.1.2.1}
$$

partially ordered by inclusion. We denote by $i$ the arbitrary element of $I_S$, and write $S_i$ for the finite set of places of $F$ corresponding to $i \in I_S$.

THEOREM 11.1.2.1 (Existence of S-local carvings on the 0-line).$^3$ *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character, $S$ a finite set of places of $F$ containing all the Archimedean places, and such that $\chi$ is unramified outside $S$. Assume $S$ is large enough so as to have $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.*

*Let $s,\Lambda$ be real numbers, $\Lambda > 0$. Assume:*

$$
s \ge 2\,[F:\mathbf Q]. \tag{11.1.2.2}
$$

*We define, for every $i \in I_S$ and for $\rho \in \{\rho_{\Lambda,+},\rho_\Lambda\}$:*

$$
W^{s,2}_{0,\rho} P_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \tag{11.1.2.3}
$$

*to be the closure in $W^{s,2}(C_F)(\chi|_{C^1_F})$ of $M_\rho P_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset W^{s,2}(C_F)(\chi|_{C^1_F})$.*

*Then:*

*(1) The set-theoretic limit:*

$$
\lim_{k\ge 0} W^{s,2}_{0,\rho} P_{S_k} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset W^{s,2}(C_F)(\chi|_{C^1_F}) \tag{11.1.2.4}
$$

*for $\{S_k\}_{k\ge 0} \subset I_S$ a choice of cofinal sequence, exists, it is a closed linear subspace of $M_\rho W^{s,2}(C_F)(\chi|_{C^1_F})$, and it is independent of the choice of cofinal sequence in $I_S$.*

*(2) Let $i,i' \in I_S$ be distinct, with $S_i \subset S_{i'}$ and such that there exists a prime number $p$ such that no place $v \in S_i$ divides $p$, and at least one place in $S_{i'}$ does. Then we have the inclusions of closed linear subspaces:*

$$
W^{s,2}_0 P_{S_{i'}} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset W^{s,2}_0 P_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \tag{11.1.2.5}
$$

*and:*

$$
W^{s,2}_{0,\rho} P_{S_{i'}} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset W^{s,2}_{0,\rho} P_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)). \tag{11.1.2.6}
$$

*The inclusion in (11.1.2.5) is strict, and for any non-decreasing sequence $\{\Lambda_k\}_{k\ge 0} \subset \mathbf R_{>0}$ such that $\lim_{k\ge 0} \Lambda_k = +\infty$, there exists a subsequence $\{\Lambda_{k_m}\}_{m\ge 0}$ such that, for every integer $m \ge 0$ and for the choice $\Lambda = \Lambda_{k_m}$, the inclusion in (11.1.2.6) is strict.*

*(3) The closed subspace from (11.1.2.4) is the closure in $M_\rho W^{s,2}(C_F)(\chi|_{C^1_F})$ of the linear subspace generated by the functions of $g \in C_F$:*

$$
\rho(g) \sum_{\xi \in F^\times} (f \otimes \prod_{v\notin S} 1_{\mathcal O_{F_v}^\times})(\xi g) \tag{11.1.2.7}
$$

*for $f \in \mathcal S(\mathbf A_{F,S}) \cap \ker(\delta_0) \cap \ker(\widehat\delta_0)$.*

Remark 11.1.2.2. We recall that a cofinal sequence $\{S_k\}_{k\ge 0} \subset I_S$ consists of the datum of a sequence $\{S_k\}_{k\ge 0} \subset I_S$, i.e. with each $S_k$ a finite subset of finite places of $F$, such that $S_k \subset S_{k+1}$ for each integer $k \ge 0$, and $\bigcup_{k\ge 0} S_k = \Sigma_F - S$.

---
$^3$Return here.

## PDF page 481

**11.1. THE SHELL STRUCTURE** · **481**

*Proof.* (1) : By Proposition 11.2.0.1, each $\mathrm{PV}_{S_i}$ is continuous and with closed range as a linear endomorphism of $W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

In particular, the closure within $W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ of $\mathrm{PV}_{S'} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$, for any $S' \in I_S$, is exactly the closed subspace $\mathrm{PV}_{S'} W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

The topology on $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ induced by

$$
M_\rho : \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset W^{s,2}(C_F)(\chi|_{C^1_F}) \to M_\rho W^{s,2}(C_F)(\chi|_{C^1_F}) \tag{11.1.2.8}
$$

is induced by the seminorm:

$$
\|\phi\|_{s,2,\rho} := \left( \int_{C^{\ge 1/\Lambda}_F} |\phi(g)|^2 (1+|\log|g|_F|^2)^{s/2}\,\mathrm{d}\bar\mu(g) \right)^{1/2}. \tag{11.1.2.9}
$$

To see this, it is enough to observe that since the topology on $W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ is induced by the $\|\cdot\|_{s,2}$-norm on $W^{s,2}(C_F)(\chi|_{C^1_F})$, then the pull-back of the norm $\|\cdot\|_{s,2}$ along $M_\rho$ from (11.1.2.8) is a seminorm $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$, which generates a locally convex topology whose separated completion is closed and dense within $M_\rho W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$, and hence agrees with it.

Such pull-back seminorm is computed as:

$$
\phi \mapsto \|\rho\cdot\phi\|_{s,2} = \left( \int_{C_F} |\rho(g)\phi(g)|^2 (1+|\log|g|_F|^2)^{s/2}\,\mathrm{d}\bar\mu(g) \right)^{1/2}
$$

which gives the formula for $\|\cdot\|_{s,2,\rho}$ in (11.1.2.9), since the indicator function $\rho$ of $C^{>1/\Lambda}_F$, respectively of $C^{(1/\Lambda,\Lambda)}_F$, is its own square.

Since $\{g \in C_F : |g|_F = 1/\Lambda,\Lambda\}$ has $\bar\mu$-measure zero, indeed the formula in (11.1.2.9) for $\|\cdot\|_{s,2,\rho}$ computes the pull-back of $\|\cdot\|_{s,2}$ on $W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ along $M_\rho$ from (11.1.2.8).

Since $\|\cdot\|_{s,2,\rho}$ is a continuous seminorm on $W^{s,2}(C_F)(\chi|_{C^1_F})$, the seminormed topology induced by $\|\cdot\|_{s,2,\rho}$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ is coarser than the $\|\cdot\|_{s,2}$-norm topology.

It follows that the following inclusion:

$$
M_\rho W^{s,2}_0 \mathrm{PV}_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset W^{s,2}_{0,\rho} \mathrm{PV}_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \tag{11.1.2.10}
$$

holds.

The left side in (11.1.2.10) (which, note, equals $M_\rho \mathrm{PV}_{S_i} W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ by continuity of $\mathrm{PV}_{S_i}$) contains $M_\rho P_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ and it is already closed, since $M_\rho$ has closed range by [Cnw-a, Ch.II, §3, Prop.3.2(b), p.37], being an idempotent operator.

It follows that we have, as closed subspaces of $W^{s,2}(C_F)(\chi|_{C^1_F})$:

$$
M_\rho W^{s,2}_0 \mathrm{PV}_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) = W^{s,2}_{0,\rho} \mathrm{PV}_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)). \tag{11.1.2.11}
$$

We now observe that if $S_i \subset S_{i'}$ for $i,i' \in I_S$, then we have:

$$
W^{s,2}_{0,\rho} \mathrm{PV}_{S_{i'}} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset W^{s,2}_{0,\rho} P_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \tag{11.1.2.12}
$$

since $\mathrm{PV}_{S_{i'}} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset \mathrm{PV}_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$, this latter inclusion being a consequence of Theorem 6.3.2.2.

We let $\{S_k\}_{k\ge 0} \subset I_S$ be any cofinal sequence. Then

$$
\bigcap_{k\ge 0} W^{s,2}_{0,\rho} \mathrm{PV}_{S_k} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \tag{11.1.2.13}
$$

is a closed linear subspace of $W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

## PDF page 482

**482** · **CHAPTER 11. THE SHELL STRUCTURE**

For $\{S'_m\}_{m\ge 0}$ another cofinal sequence in $I_S$, we have, for every integer $k \ge 0$, that there exists a large enough integer $m_k \ge 0$ such that $S'_m$ contains $S_k$ for every $m \ge m_k$.

In particular, by (11.1.2.12), the following inclusion holds:

$$
\bigcap_{m\ge 0} W^{s,2}_{0,\rho} \mathrm{PV}_{S'_m} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \subset \bigcap_{k\ge 0} W^{s,2}_{0,\rho} \mathrm{PV}_{S_k} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)). \tag{11.1.2.14}
$$

Upon exchanging the roles of $\{S_k\}_{k\ge 0}$ and $\{S'_m\}_{m\ge 0}$, we deduce that the reverse inclusion holds, and hence:

$$
\bigcap_{m\ge 0} W^{s,2}_{0,\rho} \mathrm{PV}_{S'_m} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) = \bigcap_{k\ge 0} W^{s,2}_{0,\rho} \mathrm{PV}_{S_k} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)). \tag{11.1.2.15}
$$

as closed subspaces of $W^{s,2}(C_F)(\chi|_{C^1_F})$. Formation of the common such closed subspace therefore does not depend on the choice of cofinal sequence in $I_S$, but only on $I_S$ itself.

(2) :$^4$ We now prove that the inclusion in (11.1.2.5) is strict. By Theorem 11.2.0.2, the strong dual of the orthogonal in $W^{s,2}_0 \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ of $W^{s,2}_0 \mathrm{PV}_{S_{i'}} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ is non-trivial, the Theorem exhibiting a Schauder basis (given by the functionals $\eta_{\varepsilon_p}$ as $\varepsilon_p$ varies over the zeros of $(1-q^{-s-it_v}_v)^{-1}$ for $v \in S_{i'}$ of residue characteristic $p$), and since $S_i \subset S_{i'}$ is a strict inclusion, as $i,i'$ are distinct elements of $I_S$, and there exists a prime number $p$ divided by a place in $S_{i'}$ and by no place in $S_i$, the functionals $\eta_{\varepsilon_p}$ separate the points of $W^{s,2}_0 \mathrm{PV}_{S_{i'}} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ from the points of $W^{s,2}_0 \mathrm{PV}_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

All such functionals exist and provide elements of the Schauder bases from Theorem 11.2.0.2, because $s \ge 2\,[F:\mathbf Q]$.

We now prove that for any non-decreasing sequence $\{\Lambda_k\}_{k\ge 0} \subset \mathbf R_{>0}$ such that $\lim_{k\to +\infty} \Lambda_k = +\infty$, there exists a subsequence $\{\Lambda_{k_m}\}_{m\ge 0}$ such that for each choice $\Lambda = \Lambda_{k_m}$, the inclusion in (11.1.2.6) is also strict. If not, then we have:

$$
W^{s,2}_{0,\Lambda_k,+} \mathrm{PV}_{S_{i'}} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) = W^{s,2}_{0,\Lambda_k,+} \mathrm{PV}_{S_i} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \tag{11.1.2.16}
$$

for every integer $k \ge 0$.$^5$

Since $\lim_{k\to +\infty} \Lambda_k = +\infty$, the sequence of operators $\{M_{\rho_{\Lambda_k,+}}\}_{k\ge 0}$ on $W^{s,2}(C_F)(\chi|_{C^1_F})$ tends to the identity with respect to the strong operator topology on $\mathscr{B}(W^{s,2}(C_F)(\chi|_{C^1_F}))$ by [Cnw-a, Ch.I, §2, Cor.2.11, p.11], forcing the inclusion in (11.1.2.5) to not be strict, a contradiction.

(3) : We will now be using Proposition 11.1.1.2. We choose $\tau$ a continuous homomorphic section to the idelic norm on $C_F$, and define $Z := \tau(\mathbf R_{>0})\cdot E^1_F$, with $E^1_F$ the idelic fundamental domain in $\mathrm{GL}_1(\mathbf A_F)^1$ for the discrete left translation action of $F^\times$ (see (A.2.3.14)).

The subset $Z \subset \mathrm{GL}_1(\mathbf A_F)$ is Borel with non-empty interior, and its $F^\times$-translates cover $\mathrm{GL}_1(\mathbf A_F)$ by Theorem A.2.3.10.

We choose $\eta := \mathrm{1}_{(1/\Lambda,+\infty)}\cdot (1+|\log|\cdot|_F|^2)^{s/2}\,\mu$ as positive Radon measure on $\mathrm{GL}_1(\mathbf A_F)$, and choose $r = 2$ in the statement of Proposition 11.1.1.2.

We choose $f \in \mathcal S_0(\mathbf A_F)$ of the form $f = f_\infty \prod_{v\in\Sigma_{F,f}} f_v$ for $f_\infty \in \mathcal S(\mathbf A_{F,S_\infty})$ and $f_v \in \mathcal S(F_v)$ for every $v \in \Sigma_{F,f}$, with $f_v = 1_{\mathcal O_{F_v}}$ for all but finitely many finite places $v$ of $F$ all contained in $S$. We assume that $f_S := f_\infty \otimes \prod_{v\in S\cap\Sigma_{F,f}} f_v \in \mathcal S(\mathbf A_{F,S})$ satisfies $f_S(0) = \widehat{f_S}(0) = 0$.

Note that Schwartz-Bruhat functions of this form $\mathbf C$-linearly span a subspace $W$ within $\mathcal S_0(\mathbf A_F)$ which is linearly mapped onto a dense subspace in $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ by our assumptions on $S$ and by the Fifth Structure Theorem (see Theorem 6.2.1.1).

---
$^4$Return here.

---
$^5$Return here.

## PDF page 483

**11.2. THE PIECES OF THE PUZZLE: PALEY-WIENER LEVELS AND ORBITAL MARKUSHEVICH BASES** · **483**

There exists a fractional ideal $I$ of $F$ depending only on $f$ through the finitely many finite places $v$ of $F$ such that $f_v \ne 1_{\mathcal O_{F_v}}$, and through $f_\infty$, such that, as $1_{\mathcal O_{F_v}}$ is replaces with $1_{\mathcal O_{F_v}^\times}$ for each $v \notin S$, the new fractional ideal $I'$ corresponding to the resulting Schwartz-Bruhat function satisfies $I' \subset I$ strictly. We choose $\alpha$ in Proposition 11.1.1.2 to be the pre-composition of $f_\infty$ with the continuous homomorphic projection $\mathrm{GL}_1(\mathbf A_F) \to \mathrm{GL}_1(\mathbf A_{F,S_\infty})$.

We choose $\{S_k\}_{k\ge 0}$ a cofinal sequence in $I_S$, and define $f_k := P_{S_k}(f)$. For every $g \in \tau(\mathbf R_{>0}) \cdot E^1_F$, the limit $\lim_{k\to +\infty} f_k(g)$ exists, and its value is exactly:

$$
(f_S \otimes \prod_{v \notin S} 1_{\mathcal O_{F_v}^\times})(g).
$$

Proposition 11.1.1.2 therefore applies, and we deduce that the sequence $\{\Phi_F(f_k)\}_{k\ge 0}$ converges in $L^2(\tau(\mathbf R_{>0}) \cdot E^1_F, 1_{(1/\Lambda,+\infty)} \cdot (1 + |\log|\cdot|_F|^2)^{s/2}\mu)$ to the function $\sum_{\xi \in F^\times} 1_{(1/\Lambda,+\infty)}(g)(f_S \otimes \prod_{v \notin S} 1_{\mathcal O_{F_v}^\times})(\xi g)$ of $g \in C_F$.

This is equivalent to saying that the function

$$
\sum_{\xi \in F^\times} 1_{(1/\Lambda,+\infty)}(\xi g)(f_S \otimes \prod_{v \notin S} 1_{\mathcal O_{F_v}^\times})(\xi g) = 1_{(1/\Lambda,+\infty)}(g) \sum_{\xi \in F^\times} (f_S \otimes \prod_{v \notin S} 1_{\mathcal O_{F_v}^\times})(\xi g)
$$

of $g \in C_F$ is an element of $R_{\Lambda,S} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$.

We have shown that, upon calling $\delta_0, \widehat{\delta}_0 \in \mathcal S(\mathbf A_{F,S})'_\beta$ the evaluation at $x = 0$ functional and its $S$-adelic Fourier transform, then as $f_S \in \mathcal S(\mathbf A_{F,S})$ varies over $\ker(\delta_0) \cap \ker(\widehat{\delta}_0)$, the functions $1_{(1/\Lambda,+\infty)} \cdot (f_S \otimes \prod_{v \notin S} 1_{\mathcal O_{F_v}^\times})$ are contained in $R_{\Lambda,S} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$.

Such functions linearly generate a subspace $W_{S,\Lambda} \subset R_{\Lambda,S} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$, whose closure $\overline{W}_{S,\Lambda}$ in $W^{s,2}(C_F)(\chi|_{C^1_F})$ contains the subspace $W_{S,\Lambda,0}$ linearly generated by the functions of $g \in C_F$ of the form:

$$
1_{(1/\Lambda,+\infty)} \cdot (f_S \otimes \prod_{v \notin S} 1_{\mathcal O_{F_v}^\times})
$$

for $f_S \in \mathcal S(\mathbf A_{F,S})$ satisfying only the one vanishing condition $\widehat{f_S}(0) = 0$. If the closure $\overline{W}_{S,\Lambda,0}$ of $W_{S,\Lambda,0}$ in $W^{s,2}(C_F)(\chi|_{C^1_F})$ is not $\overline{W}_{S,\Lambda}$ itself, then the kernel of the continuous linear quotient $\overline{W}_{S,\Lambda} \to \overline{W}_{S,\Lambda}/\overline{W}_{S,\Lambda,0}$ provides a continuous extension of $\widehat{\delta}_0$ to the completion of $\mathcal S(\mathbf A_{F,S})$ with respect to the $L^2$-norm topology induced by the Radon measure $1_{(1/\Lambda,+\infty)} \cdot (1 + |\log|\cdot|_{F,S}|^2)^{s/2}\mu_S$ on $\mathrm{GL}_1(\mathbf A_{F,S})$. However, $\widehat{\delta}_0$ is discontinuous with respect to such topology on $\mathcal S(\mathbf A_{F,S})$, because multiplication by $|\cdot|_{F,S}$ is a discontinuous operator with respect to this topology, since $|\cdot|_{F,S}$ grows polynomially as $g \in \{g \in \mathrm{GL}_1(\mathbf A_{F,S}) : |g|_{F,S} \ge 1/\Lambda\}$ satisfies $|g|_{F,S} \to +\infty$.

We deduce that we have $\overline{W}_{S,\Lambda,0} = \overline{W}_{S,\Lambda}$. Since $\overline{W}_{S,\Lambda}$ is exactly $R_{\Lambda,S} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$, we deduce that (3) holds.

$\square$

$^{6}$

**11.2. The pieces of the puzzle: Paley-Wiener levels and Orbital Markushevich Bases**

We recalled in (10.2.1.3) that we denoted the pairing $\langle\cdot,\cdot\rangle_{s,w}$ from (9.1.1.11) by:

$$
\langle\cdot,\cdot\rangle_{s,2} : W^{s,2}(C_F) \times W^{-s,2}(C_F) \to \mathbf C \tag{11.2.0.1}
$$

for which we refer the reader to (10.2.1.3), where $\langle\cdot,\cdot\rangle_{s,2}$ is assigned by:

$$
\langle\phi, \psi\rangle_{s,2} := \int_{C_F} \phi(g)\psi(g)\,\mathrm{d}\bar\mu(g).
$$

---
$^{6}$Return here.

## PDF page 484

**484** · **CHAPTER 11. THE SHELL STRUCTURE**

We recall that for a finite set of finite places $S_0$ of $F$, we defined the operator:

$$
\mathrm{PV}_{S_0} : \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F)) \to \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F)) \tag{11.2.0.2}
$$

for which we refer the reader to (5.3.1.10).

In Lemma 5.3.1.5, we proved that $\mathrm{PV}_{S_0}$ is a linear topological embedding with closed range, and Theorem 6.3.2.2 describes its range.

Formation of $\mathrm{PV}_{S_0}$ is continuous with respect to the Sobolev topologies induced by the norms $||\cdot||_{W^{s,2}_a}$ on $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$, and so $\mathrm{PV}_{S_0}$ extends to a unique continuous linear endomorphism on $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ for every pair of real numbers $a, s$ with $s \ge 0$, and it remains a linear topological embedding with closed range, which is given by the norm-completion of $\mathrm{PV}_{S_0} \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$.

We will therefore write, with no potential for ambiguity:

$$
W^{s,2}_a \mathrm{PV}_{S_0} \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F)) = \mathrm{PV}_{S_0} W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F)). \tag{11.2.0.3}
$$

We collect these properties of the operators $\mathrm{PV}_{S_0}$ into the following:

Proposition 11.2.0.1. *Let $F$ be a number field, $S_0$ a finite set of places of $F$. Let $s \ge 0$ be a real number. Then $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F)) \subset W^{s,2}_0(C_F)$ is dense.*

*The operator $\mathrm{PV}_{S_0}$ on $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ defined in (5.3.1.10) satisfies the following properties:*

(1) *It is continuous with respect to the topology on $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ induced by the norm $||\cdot||_{W^{s,2}_0}$ from (10.1.1.5).*

(2) *Assume $s \ge 2|S_0|$. Its extension by continuity to a linear map:*

$$
\mathrm{PV}_{S_0} : W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F)) \to W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F)) \tag{11.2.0.4}
$$

*is continuous with closed range, and compatible with passage to $C^1_F$-isotypes.*

Proof. The continuous injective linear operator $\mathcal{S}_{\mathrm{E}}(C_F) \to W^{s,2}(C_F)$ is compatible with the duality $\langle \mathcal{S}_{\mathrm{E}}(C_F), \mathcal{S}_{\mathrm{E}}(C_F)'_\beta\rangle$ on the source, and the duality $\langle\cdot,\cdot\rangle_{s,2}$ on the target.

By Theorem 10.2.1.1 applied with $a = 0$, and by [CF, Ch.VIII, §2, Thm.2, p.212], the orthogonal of the closure of $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ in $W^{s,2}(C_F)$ with respect to $\langle\cdot,\cdot\rangle_{s,2}$ is trivial. By [NB, Thm.8.9.2(b)], $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ is dense in $W^{s,2}(C_F)$ with respect to the weakened topology $\sigma(W^{s,2}(C_F), W^{-s,2}(C_F))$. By [Jar, Ch.8, §8.2, Prop.5, p.149], it is dense.

(1) : Since $\mathrm{PV}_{S_0}$ from (5.3.1.9) is the finite composition of the operators $P_v$ from (5.3.1.1), all continuous endomorphisms of $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ compatible with passage to $C^1_F$-isotypes, and with closed range by Lemma 5.3.1.5, we may and do assume $S_0 = \{v\}$, for a single finite place $v$ of $F$.

In this case and by (5.3.1.1), we have:

$$
P_v(\Phi_F(f)) = \Phi_F(P_v(f))
$$

which is in turn the function on $C_F$ obtained from the global adelic Schwartz-Bruhat function $f(x) - f(\pi_v^{-1}x)$, as a function of $x \in \mathbf A_F$, for $\pi_v$ any choice of uniformizer at $v$.

It is therefore enough to show that the operator $f \mapsto \rho_F(\pi_v, f)$, with $\rho_F$ the continuous left-translation action of $\mathrm{GL}_1(\mathbf A_F)$ on $\mathcal S(\mathbf A_F)$, descends to a continuous endomorphism of $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$, compatible with passage to $C^1_F$-isotypes, and continuous with respect to the normed topology on $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ defined by the norm $||\cdot||_{W^{s,2}_a}$. Since $\pi_v^{\mathbf Z}$ acts on $\mathcal S(\mathbf A_F)$ through the continuous left-translation action of the closed subgroup $F^\times_v \subset \mathrm{GL}_1(\mathbf A_F)$ through the insertion continuous group homomorphism with closed range into the $v$-indexed “coordinate” of $\mathrm{GL}_1(\mathbf A_F)$, the assertions follow by continuity of the left-translation action of $\mathrm{GL}_1(\mathbf A_F)$ with respect to the topology induced by the norm $||\cdot||_{W^{s,2}_a}$.

(2) : Since $\mathrm{PV}_{S_0}$ is the finite composition of the continuous operators $P_v$ from (5.3.1.1), obtained as continuous extensions to $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ from (1), and since each $P_v$ is compatible with passage

## PDF page 485

**11.2. THE PIECES OF THE PUZZLE: PALEY-WIENER LEVELS AND ORBITAL MARKUSHEVICH BASES** · **485**

to $C^1_F$-isotypes, then so is $\mathrm{PV}_{S_0}$, and it is enough to check that each $P_v$ has closed range. This follows from continuity of the linear functionals:

$$
\phi \mapsto \int_{C_F} \phi(g)\chi(g)|g|^\varepsilon_F (\log|g|_F)^m\,\mathrm{d}\bar\mu(g)
$$

for $0 \le m \le |S_0|-1$, as $\varepsilon$ ranges over the zeros of $\prod_{v \in S_0} L_v(\chi_v|\cdot|^s_v)^{-1}$. Indeed, the range of $\mathrm{PV}_{S_0}$ is the intersection of their kernels. To see this, we use denseness of $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ in $W^{s,2}(C_F)$, which was shown in the foregoing, to replace $W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ with $W^{s,2}(C_F)$, and $\mathrm{PV}_{S_0}$ with the finite composition of the operators $P_v : \phi \mapsto \phi(x) - \phi(\pi_v^{-1}x)$ for each $v \in S_0$, for then proceeding as in the proof of the same assertion for the functionals $D^m_t$ from (10.2.1.9) from the proof of Theorem 10.2.1.1, using the Approximation Principle from Theorem 9.3.2.1.

$\square$

We record here below a result that is analogous to Theorem 10.2.1.1, identifying a Markushevich basis for the orthogonal to

$$
\mathrm{PV}_{S_0} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F)) \subset W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F) = W^{s,2}(C_F)
$$

where $\mathrm{PV}_{S_0} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ is the closed subspace defined in (11.2.0.3), and orthogonality is defined with respect to the duality pairing $\langle\cdot,\cdot\rangle_{s,2}$ from (9.1.1.11), whose definition we recalled in (10.2.1.3).

Theorem 11.2.0.2 (Global Orbital Markushevich Bases on the 0-line). *Let $F$ be a number field, $s \ge 0$ a real number. Let $S_0$ be a finite set of finite places of $F$, $\chi \in \widehat{C_F}$ a continuous character, unramified at all the places of $S_0$. The functions, for each rational prime $p$ such that some $v \in S_0$ has residue characteristic $p$:*

$$
\eta_{\chi,\varepsilon}(g) := \chi(g)|g|^\varepsilon_F (\log|g|_F)^m \tag{11.2.0.5}
$$

such that:

(1) *$\varepsilon$ is a zero of the entire function $\prod_{v \in S_0} L_v(\chi_v|\cdot|^s_v)^{-1} = \prod_{v\mid p, v \in S_0} (1 - q_v^{-s-it_v})$, for $t_v \in \mathbf R$ the unique real number contained in $[0, 2\pi/\log(q_v))$ with $q_v := |\pi_v|^{-1}_v$, such that $\chi|\cdot|^{-it_v}_F \in (\pi_v^{\mathbf Z})^\perp \subset \widehat{C_F}$, of multiplicity $N(\varepsilon)$.*

(2) $m \ge 0$ is an integer satisfying $m \le N_s(\varepsilon)-1$ with:

$$
N_s(\varepsilon) = \min\left\{N(\varepsilon), \left[\frac{s-1}{2}+1\right]\right\} \tag{11.2.0.6}
$$

*are elements of $W^{-s,2}(C_F)(\overline{\chi}|_{C^1_F})$. If $s \ge 2|S_0|$, then any enumeration is a Markushevich basis for the orthogonal*

$$
\mathrm{PV}_{S_0} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))^\perp
$$

*in $W^{-s,2}(C_F)$ with respect to the pairing $\langle\cdot,\cdot\rangle_{s,2}$ from (10.2.1.3), endowed with the subspace topology of the strong topology.*

Remark 11.2.0.3. We note that, in light of Lemma 4.2.1.3(2), there is no ambiguity as to how to topologize the orthogonal $\mathrm{PV}_{S_0} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))^\perp$ in $W^{-s,2}(C_F)$ with respect to the pairing $\langle\cdot,\cdot\rangle_{s,2}$ from (10.2.1.3), since the subspace topology of the strong topology is equivalent to the strong topology on the continuous dual of the quotient $W^{s,2}(C_F)(\chi|_{C^1_F})/W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ endowed with the quotient topology.

Terminology 11.2.0.1 (Orbital Markushevich Bases on the 0-line). We refer to the Markushevich Bases identified in Theorem 11.2.0.2 for $\mathrm{PV}_{S_0} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))^\perp$ endowed with the subspace topology of the strong topology on $W^{s,2}(C_F)(\chi|_{C^1_F})'_\beta$, as the Orbital Markushevich Bases on the 0-line.

## PDF page 486

**486** · **CHAPTER 11. THE SHELL STRUCTURE**

Proof. We write $\omega := \chi|_{C^1_F} \in \widehat{C^1_F}$. We choose a continuous homomorphic section $\tau$ to the idelic norm, and identify $C_F/C^1_F$ with $\mathbf R_{>0}$ as a Hausdorff locally compact abelian group by means of $|\cdot|_F$. The following diagram:

(11.2.0.7)

```latex
\begin{tikzcd}
\mathrm{PV}_{S_0} \mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_0(\mathbf A_F)) \arrow[d] & \times & \mathcal{S}_{\mathrm{E}}(\mathbf R_{>0})'_\beta \arrow[r] & \mathbf C \arrow[d, equal] \\
W^{s,2}_a \mathrm{PV}_{S_0} \mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_0(\mathbf A_F)) & \times & W^{-s,2}(C_F)(\omega) \arrow[u] \arrow[r] & \mathbf C
\end{tikzcd}
```

is commutative, where the top horizontal arrow is the duality pairing $\langle\cdot,\cdot\rangle_{\mathcal{S}_{\mathrm{E}}(\mathbf R_{>0}), \mathcal{S}_{\mathrm{E}}(\mathbf R_{>0})'_\beta}$, noting that by Theorem 6.3.2.2, $\mathrm{PV}_{S_0} \mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_0(\mathbf A_F))$ is closed as a subspace of $\mathcal{S}_{\mathrm{E}}(C_F)(\omega)$.

By commutativity of (11.2.0.7), the argument is formally analogous to the argument for Theorem 10.2.1.1, upon replacing Theorem 6.3.2.1 with Theorem 6.3.2.2 to deduce that the set of continuous functionals on $W^{s,2}(C_F)(\omega)$ represented under the isometry $T_s$ from (10.2.1.3) by the elements of $W^{-s,2}(C_F)(\overline{\omega})$ from (11.2.0.5) is topologically free, for then using the Bounded Approximation Principle of Lemma 9.3.2.1 as in the proof of Theorem 10.2.1.1 to deduce the required denseness properties for the linear subspaces linearly generated by the set of elements from (11.2.0.5) in $W^{-s,2}(C_F)(\overline{\omega})$, and its bi-orthogonal set in $W^{s,2}(C_F)(\omega)$.

$\square$

In analogy with Proposition 10.2.1.3 and Corollary 10.2.1.4, we record here the following properties of the Orbital Markushevich basis on the 0-line identified in Theorem 11.2.0.2, for the orthogonal

$$
\mathrm{PV}_{S_0} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))^\perp
$$

in $W^{-s,2}(C_F)$ with respect to the pairing $\langle\cdot,\cdot\rangle_{s,2}$ from (10.2.1.3).

We further refer the reader to Terminology 10.2.1.2 for the terminology on Markushevich bases in force throughout the remainder of this subsection.

Proposition 11.2.0.4. *Let $F$ be a number field, $s > 1$ a real number. Let $S_0$ be a finite set of finite places of $F$, $\chi \in \widehat{C_F}$ a continuous character, unramified at all the places of $S_0$.*

*There exists a real number $C > 0$ such that the functions:*

$$
\eta_{\chi,\varepsilon,m}(g) := \chi(g)|g|^\varepsilon_F (\log|g|_F)^m \tag{11.2.0.8}
$$

*as $\varepsilon$ ranges over the zeros of the entire function $\prod_{v \in S_0} L_v(\chi_v|\cdot|^s_v)^{-1} = \prod_{v\mid p, v \in S_0} (1 - q_v^{-s-it_v})$, with $0 \le m \le N(\varepsilon)-1$, where $N_s(\varepsilon)$ is the function defined in (11.2.0.6), all satisfy:*

$$
\{\chi(g)|g|^\varepsilon_F (\log|g|_F)^m\}_{\varepsilon,m} \subset B_C := \{\phi \in W^{-s,2}(C_F)(\chi|_{C^1_F}) : 1/C \le ||\phi||_{-s,2} \le C\}. \tag{11.2.0.9}
$$

*In particular, the set of functions from (11.2.0.8) is not contained in the open ball in $W^{-s,2}(C_F)(\chi|_{C^1_F})$ of radius $1/C$.*

Proof. If $s > 1$, then:

$$
||\eta_{\chi,\varepsilon,m}||_{-s,2} = \left(\int_{C_F} |\log|g|_F|^{2m} (1 + |\log|g|_F|^2)^{-s/2}\,\mathrm{d}\bar\mu(g)\right)^{1/2}
$$

by Proposition 9.1.2.5, and so $||\eta_{\chi,\varepsilon,m}||_{-s,2}$ can only attain finitely many values, none of which is zero. There therefore exists a real number $C > 0$ such that $1/C$ is a strict lower bound for their minimum, and $C$ is a strict upper bound for their maximum.

$\square$

In analogy with Corollary 10.2.1.4, we have the following:

Corollary 11.2.0.5. *Let $F$ be a number field, $s > 1$ a real number. Let $S_0$ be a finite set of finite places of $F$, $\chi \in \widehat{C_F}$ a continuous character, unramified at all the places of $S_0$.*

Assume $s \ge 2|S_0|$.

## PDF page 487

**11.2. THE PIECES OF THE PUZZLE: PALEY-WIENER LEVELS AND ORBITAL MARKUSHEVICH BASES** · **487**

*Any enumeration of the set of functions:*

$$
\eta_{\chi,\varepsilon,m}(g) := \chi(g)|g|^\varepsilon_F (\log|g|_F)^m \tag{11.2.0.10}
$$

*as $\varepsilon$ ranges over the zeros of the entire function $\prod_{v \in S_0} L_v(\chi_v|\cdot|^s_v)^{-1} = \prod_{v\mid p, v \in S_0} (1 - q_v^{-s-it_v})$, with $0 \le m \le N(\varepsilon)-1$, where $N_s(\varepsilon)$ is the function defined in (11.2.0.6), is a normalized Markushevich basis for the orthogonal*

$$
\mathrm{PV}_{S_0} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))^\perp
$$

*in $W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))'_\beta = W^{s,2}(C_F)(\chi|_{C^1_F})'_\beta$, topologized with the subspace topology of the strong topology.*

Proof. There exists a real number $C > 0$ such that the set of functions $\{\eta_{\chi,\varepsilon,m}\}_{\varepsilon,m}$ is contained in the collar $B_C$ from (11.2.0.9) of Proposition 11.2.0.4.

In particular, as per Proposition 11.2.0.4 combined with Theorem 11.2.0.2, any enumeration of $\{\eta_{\chi,\varepsilon,m}\}_{\varepsilon_p,m}$, a normalized Markushevich basis for $\mathrm{PV}_{S_0} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))^\perp$, the orthogonal being formed with respect to the duality $\langle\cdot,\cdot\rangle_{s,2}$ from (10.2.1.3), and topologized with the subspace topology inherited from the norm topology on $W^{-s,2}(C_F)(\overline{\chi}|_{C^1_F})$, which is equivalent to the strong topology on $W^{s,2}(C_F)(\chi|_{C^1_F})'_\beta$ under the isometry $T_s$ from (9.1.2.14).

$\square$

**11.2.1. Paley-Wiener Levels.** Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $\varphi \in \mathcal D(C_F)$ be a test function.

In this subsection we analyze a class of large closed subspaces of $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$, within which the trace of $P^{\mathrm{geom}}_a \circ A(\varphi)$ is concentrated, i.e. the trace

$$
\mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi))
$$

for $\rho$ a $(\Lambda,\varepsilon)$-cutoff, is mostly concentrated, as $\Lambda \to +\infty$ in the regime $\varepsilon\Lambda = o(1)$.

The main result of this subsection, Theorem 11.2.1.2, indeed shows that the restriction of the nuclear operator $P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi)$ to such growing family of closed subspaces of $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$, tends to $P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi)$ in the sense of nuclear operators, therefore reducing the calculation of the trace of $P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi)$ to the trace of each of the restrictions of $P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi)$. The calculation will, in turn, be possible upon further assuming $a = 1/2$ and $s \ge 2[F:\mathbf Q]$, showing which is the subject of the remainder of this Chapter and the next.

Definition 11.2.1.1 (Absolute Paley-Wiener Levels). Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $S_\chi$ be the finite set of finite places of $F$ at which $\chi$ is ramified. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Assume $S_\chi \subset S$ and $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.

Let $\chi_S$ be the unique continuous character of $J_{F,S}$ obtained by descending by $\widehat{\mathcal O}^\times_{F,\Sigma_F-S}$-invariance the restriction of $\chi$ to $C_{F,S}$.

Let $\Lambda_0 > 0$ be a real number. Let $s, a$ be real numbers, $s \ge 0$.

We define:

(1) the closed subspaces:

$$
W^{s,2}_a \mathrm{PW}_{\Lambda_0}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S})) \subset W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S})) \tag{11.2.1.1}
$$

and:

$$
W^{s,2}_a \mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \tag{11.2.1.2}
$$

to be the closure of $|\cdot|^a_{F,S} \mathrm{PW}_{\Lambda_0}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$ in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$, respectively of $|\cdot|^a_F \mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$.

## PDF page 488

**488** · **CHAPTER 11. THE SHELL STRUCTURE**

We refer to $W^{s,2}_a \mathrm{PW}_{\Lambda_0}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$, respectively $W^{s,2}_a \mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ as the absolute Paley-Wiener Level of time $\Lambda_0$ in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$, respectively in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$.

(2) The continuous operator:

$$
P^{\mathrm{PW}}_{S,\Lambda_0,a} : W^{s,2}(C_F)(\chi|_{C^1_F}) \to W^{s,2}_a \mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \tag{11.2.1.3}
$$

to be the orthogonal projector onto the closed subspace $W^{s,2}_a \mathrm{HS}_{\Lambda_0}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \subset W^{s,2}(C_F)(\chi|_{C^1_F})$.

We refer to $P^{\mathrm{PW}}_{\Lambda_0,a}$ as the Paley-Wiener truncation at time $\Lambda_0$.

(3) For any test function $\varphi \in \mathcal D(C_F)$ supported over $C^{\ge 1}_F$, we refer to $P^{\mathrm{geom}}_a \circ A(\varphi) \circ P^{\mathrm{PW}}_{S,\Lambda_0,a}$ as the absolute Paley-Wiener condensation of $P^{\mathrm{geom}}_a \circ A(\varphi)$ at time $\Lambda_0$.

Theorem 11.2.1.2 (Absolute Paley-Wiener Condensation of the Geometric Trace - strong convergence). *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $\varphi \in \mathcal D(C_F)$ be a test function. Assume $\varphi$ is supported over $C^{\ge 1}_F$. Let $\Lambda_0 > 0$ be a real number. Let $s, a$ be real numbers, $s \ge 0$.*

*We choose a finite set $S$ of places of $F$ containing all the Archimedean places and all the finitely many finite places at which $\chi$ is ramified. We assume $S$ is so large so as to have $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.*

Then:

(1) *$P^{\mathrm{PW}}_{S,\Lambda_0,a} \to P^{\mathrm{geom}}_a$ with respect to the strong operator topology, as $\Lambda_0 \to +\infty$.*

(2) For every $(\Lambda,\varepsilon)$-cutoff $\rho$, we have:

$$
P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi) \circ P^{\mathrm{PW}}_{S,\Lambda_0,a} \to P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi) \tag{11.2.1.4}
$$

*in the sense of nuclear operators on $W^{s,2}(C_F)(\chi|_{C^1_F})$. In particular, we have:*

$$
\lim_{\Lambda_0 \to +\infty} \mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi) \circ P^{\mathrm{PW}}_{S,\Lambda_0,a}) = \mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi)). \tag{11.2.1.5}
$$

Proof. (1) : By Proposition 7.3.2.2(1) and Corollary C.3.5.5(1), we indeed have $P^{\mathrm{PW}}_{\Lambda_0,a} \to P^{\mathrm{geom}}_a$ with respect to the strong operator topology, since the directed union of the $W^{s,2}_a \mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ in $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ is sequentially dense, being $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ sequentially dense in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$, and being $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ sequentially dense in $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ by Proposition 7.3.2.2(1).

(2) : Both assertions follow from Corollary C.3.5.5(2) and (3).

$\square$

The following is an analog of Definition 11.2.1.1:

Definition 11.2.1.3 (Invariant Paley-Wiener Levels). Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $S_\chi$ be the finite set of finite places of $F$ at which $\chi$ is ramified. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Assume $S_\chi \subset S$ and $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.

Let $\chi_S$ be the unique continuous character of $J_{F,S}$ obtained by descending by $\widehat{\mathcal O}^\times_{F,\Sigma_F-S}$-invariance the restriction of $\chi$ to $C_{F,S}$.

Let $\Lambda_1 > 0$ be a real number. Let $s, a$ be real numbers, $s \ge 0$.

We define:

(1) the closed subspaces:

$$
W^{s,2}_a \mathrm{PW}^{\mathrm{inv}}_{\Lambda_1}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S})) \subset W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S})) \tag{11.2.1.6}
$$

and:

$$
W^{s,2}_a \mathrm{PW}^{\mathrm{inv}}_{S,\Lambda_1}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \subset W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \tag{11.2.1.7}
$$

to be the closure of $|\cdot|^a_{F,S} \mathrm{PW}^{\mathrm{inv}}_{\Lambda_1}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$ in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$, respectively of $|\cdot|^a_F \mathrm{PW}^{\mathrm{inv}}_{S,\Lambda_1}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$.

## PDF page 489

**11.2. THE PIECES OF THE PUZZLE: PALEY-WIENER LEVELS AND ORBITAL MARKUSHEVICH BASES** · **489**

We refer to $W^{s,2}_a \mathrm{PW}^{\mathrm{inv}}_{\Lambda_1}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$, respectively $W^{s,2}_a \mathrm{PW}^{\mathrm{inv}}_{S,\Lambda_1}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ as the invariant Paley-Wiener Level of time $\Lambda_1$ in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$, respectively in $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$.

(2) The continuous operator:

$$
Q^{\mathrm{PW}}_{S,\Lambda_1,a} : W^{s,2}(C_F)(\chi|_{C^1_F}) \to W^{s,2}_a \mathrm{PW}^{\mathrm{inv}}_{S,\Lambda_1}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \tag{11.2.1.8}
$$

to be the orthogonal projector onto the closed subspace $W^{s,2}_a \mathrm{PW}^{\mathrm{inv}}_{S,\Lambda_1}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \subset W^{s,2}(C_F)(\chi|_{C^1_F})$.

We refer to $Q^{\mathrm{PW}}_{S,\Lambda_1,a}$ as the invariant Paley-Wiener truncation at time $\Lambda_1$.

(3) For any test function $\varphi \in \mathcal D(C_F)$ supported over $C^{\ge 1}_F$, we refer to $P^{\mathrm{geom}}_a \circ A(\varphi) \circ Q^{\mathrm{PW}}_{S,\Lambda_1,a}$ as the invariant Paley-Wiener condensation of $P^{\mathrm{geom}}_a \circ A(\varphi)$ at time $\Lambda_1$.

The following is an analog of Theorem 11.2.1.2:

Theorem 11.2.1.4 (Invariant Paley-Wiener Condensation of the Geometric Trace - strong convergence). *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $\varphi \in \mathcal D(C_F)$ be a test function. Assume $\varphi$ is supported over $C^{\ge 1}_F$. Let $\Lambda_1 > 0$ be a real number. Let $s, a$ be real numbers, $s \ge 0$.*

*We choose a finite set $S$ of places of $F$ containing all the Archimedean places and all the finitely many finite places at which $\chi$ is ramified. We assume $S$ is so large so as to have $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.*

Then:

(1) *$Q^{\mathrm{PW}}_{S,\Lambda_1,a} \to P^{\mathrm{geom}}_a$ with respect to the strong operator topology, as $\Lambda_1 \to +\infty$.*

(2) For every $(\Lambda,\varepsilon)$-cutoff $\rho$, we have:

$$
P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi) \circ Q^{\mathrm{PW}}_{S,\Lambda_1,a} \to P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi) \tag{11.2.1.9}
$$

*in the sense of nuclear operators on $W^{s,2}(C_F)(\chi|_{C^1_F})$. In particular, we have:*

$$
\lim_{\Lambda_1 \to +\infty} \mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi) \circ Q^{\mathrm{PW}}_{S,\Lambda_1,a}) = \mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a} \circ A(\varphi)). \tag{11.2.1.10}
$$

Proof. Since, by (7.3.2.20) from Proposition 7.3.2.4(4), we have $P^{\mathrm{PW}}_{S,\Lambda_1,a} \le Q^{\mathrm{PW}}_{S,\Lambda_1^{|S|},a}$, both assertions follow from Theorem 11.2.1.2.

$\square$

**11.2.2. Orbital Markushevich Bases on the Paley-Wiener Levels.** Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $p$ a prime number, and $S_p$ the finite set of all finite places of $F$ whose residue characteristic is $p$. Assume that $\chi$ is unramified at every place of $F$ contained in $S_p$.

We let $\varphi \in \mathcal D(C_F)$ be a test function.

We discuss here an analog of Theorem 10.3.1.1 for the operator induced by $A(\varphi)$ on $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ for $a = 0$, on the subquotients:

$$
\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F}) := W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))/\mathrm{PV}_{S_p} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))
$$

for $S_p$ the finite set of finite places of $F$ comprising all the finite places $v$ dividing the fixed prime number $p$.

Recall that $A(\varphi)$ is the regularized action by continuous left-translation of $C_F$ on $W^{s,2}_a \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ defined in Definition 9.3.1.1, i.e. the action of the test function $\varphi$ by convolution, and $\mathrm{PV}_{S_p}$ is Weil's Principal Value Operator (see §5.3.1, and specifically Definition 5.3.1.2 and Definition 5.3.1.4).

The continuous convolution $\mathcal D(C_F)$-module structure on $W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ is inherited by the closed subspace $\mathrm{PV}_{S_p} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$, which was, recall, defined in (11.2.0.3) in light of closedness of the range of the continuous linear operator $\mathrm{PV}_{S_p}$ on $W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ from (11.2.0.2).

We define, for any real number $s \ge 0$:

$$
\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F}) := W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))/\mathrm{PV}_{S_p} W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \tag{11.2.2.1}
$$

endowed with the quotient topology. $\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F})$ is therefore a separable Hilbert space.

## PDF page 490

**490** · **CHAPTER 11. THE SHELL STRUCTURE**

We further refer the reader to (7.4.0.2), observing that $\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F})$ is the completion of $\mathscr{E}_{S_p}(\chi|_{C^1_F})$ with respect to the quotient of the normed topology on $W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$; see also Theorem 7.4.2.1.

Theorem 11.2.2.1 (Orbital Nuclearity on the 0-line). *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $s > 1$ be a real number. Assume:*

$$
s \ge 2[F:\mathbf Q]. \tag{11.2.2.2}
$$

*Let $p$ be a prime number and let $S_p$ be the set of those finite places of $F$ whose residue characteristic is $p$. Assume $\chi$ is unramified at every finite place of $F$ contained in $S_p$.*

The $\mathcal D(C_F)$-module structure:

$$
A : \mathcal D(C_F) \to \mathscr{L}_\beta(\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F})) \tag{11.2.2.3}
$$

*is valued in the Banach space of nuclear operators $S_1(\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F}))$ on $\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F})$, and is continuous with respect to the Hausdorff locally convex topology on the source, and the trace-norm topology on the target.*

*In particular, composition with the trace functional on $S_1(\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F}))$ is a distribution on $C_F$, whose value at $\varphi \in \mathcal D(C_F)$ is:*

$$
\mathrm{Trace}_{s,p}\, A(\varphi) = \sum_{\varepsilon_p} N_s(\varepsilon_p) \int_{C_F} \varphi(g)\chi(g)|g|^{\varepsilon_p}_F\,\mathrm{d}\bar\mu(g) \tag{11.2.2.4}
$$

*where $N_s$ is the counting function defined in (11.2.0.6), i.e.*

$$
N_s(\varepsilon_p) = \min\left\{N(\varepsilon_p), \left[\frac{s-1}{2}+1\right]\right\} \tag{11.2.2.5}
$$

*where $[x]$ is the largest integer $N \ge 0$ satisfying $N \le x$, and $\varepsilon_p$ varies over the zeros of the entire function $\prod_{v \in S_p} L_v(\chi|\cdot|^s_F)^{-1}$, where $L_v(\chi|\cdot|^s_F)$ is the local Euler factor at $v$ of the Hecke $L$-function $L(s,\chi)$.*

Proof. Since $W^{s,2}(C_F)$ and $W^{s,2}_0 \mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ are reflexive Banach spaces, being Hilbert spaces, then by [Tre, p.484] $A(\varphi)$ is nuclear if and only if its adjoint $A(\varphi)'$, a continuous linear endomorphism of $(\mathscr{E}^s_{0,S_p})'_\beta$, is nuclear. Its trace-norm is computed by $||A(\varphi)||_{\mathrm{Tr}} = ||A(\varphi)'||_{\mathrm{Tr}}$.

We choose an enumeration for the elements:

$$
B := \{\eta_{\chi,\varepsilon_p,m}\}_{(\varepsilon_p,m)} \subset \mathscr{E}^s_{0,S_p}(\chi|_{C^1_F})'_\beta
$$

which, by Theorem 11.2.0.2 is a Markushevich basis for $\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F})'_\beta$. By Corollary 11.2.0.5, $B \subset \mathscr{E}^s_{0,S_p}(\chi|_{C^1_F})'_\beta$ is bounded, and the bi-orthogonal set $B' := \{\psi_{\chi,\varepsilon_p,m}\}_{(\varepsilon_p,m)}$ is also bounded.

We compute:

$$
\rho'_F(g, \eta_{\chi,\varepsilon_p,m})(h) = \chi(gh)|gh|^{\varepsilon_p}_F (\log|gh|_F)^m \tag{11.2.2.6}
$$

$$
= \chi(g)\chi(h)|g|^{\varepsilon_p}_F |h|^{\varepsilon_p}_F (\log|g|_F + \log|h|_F)^m \tag{11.2.2.7}
$$

$$
= \chi(g)\chi(h)|g|^{\varepsilon_p}_F |h|^{\varepsilon_p}_F \sum_{0 \le k \le m} \binom{m}{k} (\log|g|_F)^k (\log|h|_F)^{m-k} \tag{11.2.2.8}
$$

$$
= \chi(g)|g|^{\varepsilon_p}_F \sum_{0 \le k \le m} \binom{m}{k} (\log|g|_F)^k \{\chi(h)|h|^{\varepsilon_p}_F (\log|h|_F)^{m-k}\} \tag{11.2.2.9}
$$

$$
= \chi(g)|g|^{\varepsilon_p}_F \sum_{0 \le k \le m} \binom{m}{k} (\log|g|_F)^k \eta_{\chi,\varepsilon_p,m-k}(h) \tag{11.2.2.10}
$$

Upon integrating over $g \in C_F$ the test function $\varphi \in \mathcal D(C_F)$, we obtain a single linear endomorphism of $W_{\varepsilon_p} := \bigoplus_{0 \le m \le N_s(\varepsilon_p)-1} \mathbf C \eta_{\chi,\varepsilon_p,m}$ whose matrix with respect to the basis $\{\eta_{\chi,\varepsilon_p,m}\}$ is triangular, and of the same form of the transpose of (10.3.1.17) from the proof of Theorem 10.3.1.1(1).

## PDF page 491

**11.3. ORBITAL KERNELS AND ORBITAL TRACES** · **491**

Its trace is:

$$
N_s(\varepsilon_p)\int_{C_F}\chi(g)\varphi(g)\lvert g\rvert^{\varepsilon_p}_F\,\mathrm{d}\bar\mu(g). \tag{11.2.2.11}
$$

The series:

$$
A(\varphi)'=\sum_{(\varepsilon_p,m)}\langle A(\varphi)'\eta_{\chi,\varepsilon_p,m},\cdot\rangle_{s,2}\psi_{\chi,\varepsilon_p,m} \tag{11.2.2.12}
$$

converges in $S_p(\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F})'_\beta)$ for every real number $p\ge 1$ by the same argument as in the proof of Theorem 10.3.1.1(1), leading to the expression in (11.2.2.4) by continuity of the trace functional on $S_1(\mathscr{E}^s_{0,S_p}(\chi|_{C^1_F}))$, combined with the calculation of the value in (11.2.2.11) for the trace of the finite rank partial sums of the series (11.2.2.12). $\square$

REMARK 11.2.2.2. Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $s>1$ be a real number. Assume:

$$
s\ge 2[F:\mathbf Q]. \tag{11.2.2.13}
$$

Let $p$ be a prime number such that $\chi$ is unramified at every finite place of $F$ whose residue characteristic is $p$. We observe that $\mathrm{Trace}_{s,p}\,A(\varphi)$, computed in Theorem 11.2.2.1, is independent of $s$ (so long as $s$ satisfies (11.2.2.13)). Indeed, $N_s(\varepsilon_p)=N(\varepsilon_p)$ for all such $s$, since $N(\varepsilon_p)\le [F:\mathbf Q]$ for all primes $p$.

**11.3. Orbital Kernels and Orbital Traces**

**11.3.1. Calculation of the Orbital Kernels by global to $S$-local degeneration on the orbital basis elements.**

11.3.1.1. *Divisorial stratification of the ideles.* The next step now is to split $k_{\mathrm{geom},I,\varphi}(x,y)$ into an infinite sum of pieces indexed by the places of $F$:

$$
k_{\mathrm{geom},I,\varphi}(x,y)=k_{S,\varphi}(x,y)+\sum_{p\nmid S}k_{p,\varphi}(x,y)
$$

and let the pieces $k_{p,\varphi}(x,y)$ act on certain subspaces of $W^{b,2}_I(\lvert\cdot\rvert^{1/2}_F \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal{S}_0(\mathbf A_F)))$ to understand them.

This subsection is aimed at conveying the main ideas on how to accomplish this, i.e. how to split the geometric kernel.

We start by identifying an interesting stratification of the global ideles $\mathrm{GL}_1(\mathbf A_F)$, which is found only on $\mathrm{GL}_1(\mathbf A_F)$ as opposed to its quotient $C_F$, since it is defined by leveraging crucially the restricted product nature of $\mathrm{GL}_1(\mathbf A_F)$.

This stratification will adapt itself nicely to the structure of the Schwartz-Bruhat functions representing the global adelic $\theta$-functions in

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal{S}_0(\mathbf A_F)).
$$

Recall that there exists a finite set of finite places $S$ of $F$ satisfying the following conditions:

(1) $S$ contains all the ramified places of $F$ and all the Archimedean places.

(2) $S$ contains all the places of $F$ at which $\chi$ is ramified.

(3) $\mathrm{Pic}(\mathcal O_{F,S})=1$.

such that any such $\theta$-function $\phi$ can be realized as being of the form, as a function of $x\in C_F$:

$$
\phi(x)=\Phi_{F,\chi|_{C^1_F}}(f)(x)
$$

## PDF page 492

**492** · **CHAPTER 11. THE SHELL STRUCTURE**

where

$$
f=f_S\otimes\bigotimes_{v\notin S}1_{\mathcal O_{F_v}} \tag{11.3.1.1}
$$

for some $f_S\in \mathcal{S}(\mathbf A_{F,S})$.

This is the last of the five Structure Theorems, proved at the end of Chapter 5 of this work.

The stratification of the global ideles $\mathrm{GL}_1(\mathbf A_F)$ that we are about to define will weld itself perfectly well with the non-Archimedean “transversal” (i.e. tensor component) $\bigotimes_{v\notin S}1_{\mathcal O_{F_v}}$ which all the global Schwartz-Bruhat functions on $\mathbf A_F$ representing the $\chi|_{C^1_F}$-homogeneous global $\theta$-functions can be made to share in common.

The guiding principle is simple: since $\mathcal O_{F_v}^\times\subset F_v^\times$ is compact and open, hence so it is in $F_v$, and we have

$$
1_{\mathcal O_{F_v}^\times}\cdot 1_{\mathcal O_{F_v}}=1_{\mathcal O_{F_v}^\times}
$$

as Schwartz-Bruhat functions on $F_v$. Under the local Mellin transform, $Z_v(1_{\mathcal O_{F_v}^\times},c)$ and $Z_v(1_{\mathcal O_{F_v}},c)$ are related by “Weil’s Identity”:

$$
\mu_v(\mathcal O_{F_v}^\times)\cdot Z_v(1_{\mathcal O_{F_v}^\times},\chi_v\lvert\cdot\rvert^s_v)=L_v(\chi_v\lvert\cdot\rvert^s_v)^{-1}Z_v(1_{\mathcal O_{F_v}},\chi_v\lvert\cdot\rvert^s_v)
$$

as meromorphic functions on $\Omega(F_v^\times)(\chi_v)$.

Multiplication by $1_{\mathcal O_{F_v}^\times}$ of $1_{\mathcal O_{F_v}}$ has the effect of replacing the local $Z$-function $Z_v(1_{\mathcal O_{F_v}},\chi_v\lvert\cdot\rvert^s_v)$ with the product by the reciprocal local Euler factor $L_v(\chi_v\lvert\cdot\rvert^s_v)$.

Note also that the infinite product of the volumes $\mu_v(\mathcal O_{F_v}^\times)$ over all the finite places $v$ of $F$ is a finite product (these volumes are $1$ for all but finitely many $v$’s) and therefore converges to the square root of the absolute different.

We define

$$
\rho_v:=\bigotimes_{w\in S}1_{F_w}\otimes\bigotimes_{w\notin S,w\ne v}1_{F_v}\otimes 1_{\mathcal O_{F_v}^\times}.
$$

This is a smooth function on $\mathrm{GL}_1(\mathbf A_F)$ (since $\mathcal O_{F_v}^\times\subset F_v$ is a compact open subset).

We define, for any finite subset $T$ of finite places of $F$ such that $S\cap T=\varnothing$:

$$
\rho_T:=\prod_{v\in T}\rho_v. \tag{11.3.1.2}
$$

For any increasing chain of finite subsets $T_k$ of finite places of $F$, as $k\ge 0$ varies over the nonnegative integers, and such that $T_{k+1}-T_k$ contains only one place, then the functions $\{\rho_{T_k}\}_{k\ge 0}$ define on $\mathrm{GL}_1(\mathbf A_F)$ a stratification by open and closed subsets, which we call the divisorial stratification.

Each stratum is:

$$
\mathrm{GL}_1(\mathbf A_F)_{T_k}=\{g\in\mathrm{GL}_1(\mathbf A_F):\rho_{T_k}(g)=1\}=\{g\in\mathrm{GL}_1(\mathbf A_F)_{T_k}:g_v\in\mathcal O_{F_v}^\times\text{ for all }v\in T_k\}
$$

and the complement to each stratum into the next is of the following form:

$$
\mathrm{GL}_1(\mathbf A_F)_{T_k}-\mathrm{GL}_1(\mathbf A_F)_{T_{k+1}}=\{g\in\mathrm{GL}_1(\mathbf A_F):g_v\in\mathcal O_{F_v}^\times\text{ for all }v\in T_k,\,g_v\in\bigcup_{m\in\mathbf Z,m\ne 0}\pi_v^m\mathcal O_{F_v}^\times\text{ for }v\in T_{k+1}-T_k\}.
$$

At last, we will term the primary divisorial stratification the stratification $\{\mathrm{GL}_1(\mathbf A_F)_{P_k}\}_{k\ge 0}$ of the global ideles $\mathrm{GL}_1(\mathbf A_F)$ where we assume:

(1) $S$ is saturated (it contains all the finite places of $F$ of a given residue characteristic, if it contains one of them).

(2) Each finite set of finite places $P_k$ is saturated, and obtained as a union of finitely many of the $T_m$’s.

(3) $\{P_k\}_{k\ge 0}$ is the finest (under the refinement partial ordering) among such stratifications.

## PDF page 493

**11.3. ORBITAL KERNELS AND ORBITAL TRACES** · **493**

More directly, we define $P_k$ to be the pre-image under the map $\lvert\mathrm{Spec}(\mathcal O_F)\rvert\to\lvert\mathrm{Spec}(\mathbf Z)\rvert$ of the subset $T_k$, and therefore the stratum $\mathrm{GL}_1(\mathbf A_F)_{P_k}$ is the pre-image under the norm map $\mathrm{GL}_1(\mathbf A_F)\to\mathrm{GL}_1(\mathbf A_{\mathbf Q})$ of the $k$th divisorial stratum on $\mathrm{GL}_1(\mathbf A_{\mathbf Q})$. Explicitly, we have

$$
\mathrm{GL}_1(\mathbf A_F)_{P_k}=\{g\in\mathrm{GL}_1(\mathbf A_F):g_v\in\mathcal O_{F_v}^\times\text{ for all }v\in\bigcup_{p\in T_k}S_p\}
$$

where $T_k$ denotes, here, the finite set of the first $k$ rational primes. In other words, $\mathrm{GL}_1(\mathbf A_F)_{P_k}$ is the pre-image of the $k$th stratum $\mathrm{GL}_1(\mathbf A_{\mathbf Q})_{T_k}$ of the divisorial stratification on $\mathrm{GL}_1(\mathbf A_{\mathbf Q})$ under the norm map $\mathrm{GL}_1(\mathbf A_F)\to\mathrm{GL}_1(\mathbf A_{\mathbf Q})$.

The complement to each stratum of $\{\mathrm{GL}_1(\mathbf A_F)_{P_k}\}_{k\ge 0}$ into the next is of the following form:

$$
\mathrm{GL}_1(\mathbf A_F)_{P_k}-\mathrm{GL}_1(\mathbf A_F)_{P_{k+1}}=\bigcup_{Q\subset P_{k+1}-P_k}\{g\in\mathrm{GL}_1(\mathbf A_F):g_v\in\mathcal O_{F_v}^\times\text{ for all }v\in P_k,\,g_v\in\bigcup_{m\in\mathbf Z,m\ne 0}\pi_v^m\mathcal O_{F_v}^\times\text{ for }v\in Q\}
$$

where $Q$ varies over all nonempty finite subsets of $P_{k+1}-P_k$.

The primary divisorial stratification on $\mathrm{GL}_1(\mathbf A_F)$ adapts itself nicely to the Schwartz-Bruhat functions $f$ on $\mathbf A_F$ of the form in (11.3.1.1). Indeed, upon calling:

$$
\alpha_k:=1_{\mathrm{GL}_1(\mathbf A_F)_{P_k}}
$$

the indicator function of the $k$th stratum of the primary divisorial stratification on $\mathrm{GL}_1(\mathbf A_F)$, we have

$$
\alpha_k\cdot(f_S\otimes\bigotimes_{v\notin S}1_{\mathcal O_{F_v}})=f_S\otimes\bigotimes_{v\in S-P_k}1_{\mathcal O_{F_v}}\otimes\bigotimes_{v\in P_k}1_{\mathcal O_{F_v}^\times}
$$

and hence multiplication by $\alpha_k$ replaces the Zeta function of $f$ with the product of $Z(f,\chi\lvert\cdot\rvert^s_F)$ by the finitely many reciprocal Euler factors of $L(s,\chi)$ at the non-Archimedean places $v$ of $F$ indexed by $P_k$ (the reciprocal of the product of the volumes of the local units is $1$ because $S$ is now assumed to contain all the ramified places of $F$!).

We call such multiplication process “restriction” from one stratum to the next, of the primary divisorial filtration.

In particular, and this is the main observation of this subsection: *the $(k+1)$st iteration of the restriction to the strata of the primary divisorial filtration is obtained from the $k$th, on the forward side of the Mellin transform, by multiplication by*

$$
\prod_{v\in S_{p_{k+1}}}L_v(\chi_v\lvert\cdot\rvert^s_v)^{-1}.
$$

Now recall the main idea: “degenerate” a global adelic $\theta$-function into an $S$-local one, by representing it as the image of a global Schwartz-Bruhat function

$$
f=f_S\otimes\bigotimes_{v\notin S}1_{\mathcal O_{F_v}}
$$

and then replacing each $1_{\mathcal O_{F_v}}$ by $1_{\mathcal O_{F_v}^\times}$. Here $S$ is large enough (it satisfies the assumptions we stated so far throughout this subsection, and it is fixed). Note that replacing $1_{\mathcal O_{F_v}}$ by $1_{\mathcal O_{F_v}^\times}$ has the effect of sending $f$ to the function of $x\in\mathbf A_F$:

$$
x\mapsto f(x)-f(\pi_v^{-1}x)
$$

with $\pi_v$ any choice of uniformizer at the non-Archimedean place $v$. We repackage this operation into an operator $\mathrm{PV}_v$, which turns out to descend to the space of global adelic $\theta$-functions.

We denote by $\mathrm{PV}_{P_k}$ the composition of the $\mathrm{PV}_v$ as $v$ varies over the places in $P_k$.

If we let $f$ (equivalently $f_S$) vary, we obtain that all the resulting global adelic $\theta$-functions restricted to the $k$th stratum are contained in

$$
\mathrm{PV}_{P_k}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal{S}_0(\mathbf A_F))
$$

## PDF page 494

**494** · **CHAPTER 11. THE SHELL STRUCTURE**

and all the global adelic $\theta$-functions restricted to the $(k+1)$st stratum are contained in the yet smaller and closed subspace

$$
\mathrm{PV}_{S_{p_{k+1}}}\mathrm{PV}_{P_k}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal{S}_0(\mathbf A_F))=\mathrm{PV}_{P_{k+1}}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal{S}_0(\mathbf A_F)).
$$

But now the subquotient:

$$
\mathrm{PV}_{P_k}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal{S}_0(\mathbf A_F))/\mathrm{PV}_{P_{k+1}}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal{S}_0(\mathbf A_F)) \tag{11.3.1.3}
$$

carries a Schauder basis that is analogous to the exponential system from the toy example (see Example 1.8.1.1)!

(1) Using the indicator functions $\alpha_k$, $k\ge 0$ of the strata of the divisorial filtration on the global ideles, we chop the kernel function $k_{\mathrm{geom},I,\varphi}$ along the strata of the primary divisorial filtration on $\mathrm{GL}_1(\mathbf A_F)$. Consider the successive differences

$$
k_{p_k}(x,y):=(\alpha_{k+1}-\alpha_k)k_{\mathrm{geom},I,\varphi}(x,y) \tag{11.3.1.4}
$$

(this will be what we called $k_{p_k,\varphi}(x,y)$) and write them down explicitly by letting them act on (lifts of the) Schauder basis elements on the subquotients (11.3.1.3), upon incorporating the effect of multiplication by $\lvert\cdot\rvert^{1/2}_F$ (here I am omitting several items. The subquotients used to this effect incorporate a support condition on the Fourier transform of the comprising global Schwartz-Bruhat functions $f$. They carry such Schauder bases because they are all realized as copies of twisted forms of the exponential system itself, and we can always arrange such support condition to hold (by compactness of the quotients $C_F/\pi_v^{\mathbf Z}$ for each $v\notin S$, in a nutshell). The version of the subquotients from (11.3.1.3) incorporating such support condition is termed Paley-Wiener Levels in the paper. The support condition aims at making multiplication by $\lvert\cdot\rvert^a_F$ for any $a>0$, continuous on the closure of the subspace generated by the Schwartz-Bruhat functions $f$ satisfying such support condition on their Fourier transform. We are going to omit all of this from this overview. These elements are not difficult, and they are quite natural: they only make for a very long story).

(2) Smoothen the “partial kernels” $k_{p_k,\varphi}$ along the diagonal (using a version of the Hardy-Littlewood Maximal Theorem) and compute their own mass along the diagonal, by using their explicit form as a limit of finite rank operators, obtained by using the basis.

The answer we get is:

$$
\sum_{\varepsilon_p}N(\chi\lvert\cdot\rvert^{\varepsilon_p}_F)\int_{C_F}\varphi(g)\chi(g)\lvert g\rvert^{\varepsilon_p-1/2}_F\,\mathrm{d}\bar\mu(g)
$$

where the sum is over the complex numbers $\varepsilon_p$ such that $\chi\lvert\cdot\rvert^{\varepsilon_p}_F$ is a zero of the entire function $\prod_{v\in S_p}L_v^{-1}$ (we call $N(\chi\lvert\cdot\rvert^{\varepsilon_p}_F)$ its multiplicity) with $\chi\lvert\cdot\rvert^{\varepsilon_p}_F$ contained in the connected component $\Omega(C_F)(\chi|_{C^1_F})$.

Once again (as in the toy example) the Poisson Summation Formula also gives us that such trace equals:

$$
\sum_{v\in S_p}\frac{\log(q_v)}{\mu_v(\mathcal O_{F_v}^\times)}\sum_{k\in\mathbf Z}\varphi(\pi_v^k)
$$

and so if $\varphi$ is supported strictly over $C_F^{(1,\lvert\pi_v^{-1}\rvert_v)}$ then this gives zero!

If $\varphi$ is fixed and compactly supported over $(1,+\infty)$, then outside of finitely many places $v$, indeed $\varphi$ will be supported on $C_F^{(1,\lvert\pi_v^{-1}\rvert_v)}$ because $\lvert\pi_v^{-1}\rvert_v=q_v$ grows to $+\infty$ as the residue characteristic

## PDF page 495

**11.3. ORBITAL KERNELS AND ORBITAL TRACES** · **495**

of $p$ grows, and so for all but finitely many $v$, the compact support of $\varphi$ will be contained in the relatively compact regions $C_F^{(1,\lvert\pi_v^{-1}\rvert_v)}$.

In other words, for all but finitely many finite places $v$ of $F$, the “partial kernels” $k_{p,\varphi}$ contribute zero to the mass of the geometric kernel.

**11.3.2. Calculation of the Orbital Traces.**

THEOREM 11.3.2.1 (Orbital Traces on the Paley-Wiener Levels). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $\varphi\in\mathcal D(C_F)$ be a test function. Let $S$ be a finite set of places of $F$ containing all the Archimedean places, all the places at which $F$ is ramified over $\mathbf Q$, all the places at which $\chi$ is ramified, and such that $\varphi$ is invariant under the continuous left-translation action of the image in $C_F$ of the closed subgroup $\prod_{v\notin S}\mathcal O_{F_v}^\times\subset\mathrm{GL}_1(\mathbf A_F)$. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$. Let $a=1/2$, $s>1$ a real number, $I=[-\alpha,\alpha]$ a compact interval, with $\alpha\ge 0$ a real number. Assume $\varphi$ is supported over $C^{>1}_F$. Let $\tau:\mathbf R_{>0}\to\mathrm{GL}_1(\mathbf A_F)$ be a choice of continuous homomorphic section to the idelic norm. Then:*

$$
\sum_{\xi\in F^\times}\int_{g\in E^1_F}((\alpha_{k+1}-\alpha_k)k^\Delta_{\mathrm{geom},a,I,s,\varphi})(\tau(t),\xi g\tau(t))\,\mathrm{d}\mu_1(g)\,\frac{\mathrm{d}t}{t}=\frac{\log(q_v)}{\mu_v(\mathcal O_{F_v}^\times)}\sum_{k\in\mathbf Z}\varphi(\pi_v^k) \tag{11.3.2.1}
$$

*where the $\Delta$-subscript denotes the indented kernel of $k_{\mathrm{geom},a,I,s,\varphi}$ along the piece-wise constant indentation given by the function:*

$$
u_0(x,y):=\sum_{\xi\in F^\times}\int_{g\in E^1_F}1_{\tau(\mathbf R_{>0})}(\xi gx)\otimes 1_{\tau(\mathbf R_{>0})}(\xi gy). \tag{11.3.2.2}
$$

Proof. We observe that $k^\Delta_{\mathrm{geom},a,I,s,\varphi}(\tau(t),\xi g\tau(t))$ vanishes unless $\xi\in F^\times$ maps to a uniformizer in $F_v^\times$ for some $v\in P_{k+1}-P_k$. We denote the set of such $\xi$’s as $\Xi_k$. In particular, the subset $\{\xi g\tau(t),\,t\in\mathbf R_{>0},\,g\in E^1_F,\,\xi\in\Xi_k\}$ satisfies:

$$
\{\xi g\tau(t),\,t\in\mathbf R_{>0},\,g\in E^1_F,\,\xi\in\Xi_k\}\subset\mathrm{GL}_1(\mathbf A_{F,S'})\times\prod_{v\notin S'}\mathcal O_{F_v}^\times
$$

for $S'$ large enough containing $S$ and $P_{k+1}-P_k$.

We call $\beta_{S'}$ the indicator function of $\mathrm{GL}_1(\mathbf A_{F,S'})\times\prod_{v\notin S'}\mathcal O_{F_v}^\times$ within $\mathrm{GL}_1(\mathbf A_F)$. Multiplication of $(\alpha_{k+1}-\alpha_k)k^\Delta_{\mathrm{geom},a,I,s,\varphi}$ by the indicator function $\alpha_k$ (as a function of the second named variable) for $k\ge k_0$ for a suitable large enough integer $k_0\ge 0$ such that the support of $\alpha_k$ contains $\mathrm{GL}_1(\mathbf A_{F,S'})\times\prod_{v\notin S'}\mathcal O_{F_v}^\times$, preserves the value of the left side of (11.3.2.1). We let $\rho$ be a smooth $(\varepsilon,\Lambda)$-cutoff and multiply $(\alpha_{k+1}-\alpha_k)k^\Delta_{\mathrm{geom},a,I,s,\varphi}$ by $\rho$ as a function of the first named variable.

Then the process of multiplication by $\alpha_k$ in the second named variable converges within $W^s_I(C_F)$ by Theorem 11.1.2.1, and by Proposition 12.2.2.2 the value:

$$
\sum_{\xi\in F^\times}\int_{g\in E^1_F}\rho(\tau(t))((\alpha_{k+1}-\alpha_k)k^\Delta_{\mathrm{geom},a,I,s,\varphi})(\tau(t),\xi g\tau(t))\alpha_{k_1}(\xi g\tau(t))\,\mathrm{d}\mu_1(g)\,\frac{\mathrm{d}t}{t} \tag{11.3.2.3}
$$

equals the value of the trace of the nuclear operator on $W^s_I(C_F)$ which is the unique continuous extension that the kernel $\rho(\tau(t))((\alpha_{k+1}-\alpha_k)k^\Delta_{\mathrm{geom},a,I,s,\varphi})(\tau(t),\xi g\tau(t))\alpha_{k_1}(\xi g\tau(t))$ induces, by defining a continuous integral operator $\mathcal{S}(\mathbf A_F)\to W^s_I(C_F)$ valued in the range of $M_\rho$.

As $k_1\to+\infty$ the effect of this latter on the arbitrary Schwartz-Bruhat function matches the effect of convolution on the resulting $S'$-local Schwartz-Bruhat function, by invariance under of $\prod_{v\notin S}\mathcal O_{F_v}^\times$ of $\varphi$, and with $S'$ determined by $k$ as in the foregoing, so that the indicator function of $\mathrm{GL}_1(\mathbf A_{F,S'})\times\prod_{v\notin S'}\mathcal O_{F_v}^\times$ is the

## PDF page 496

**496** · **CHAPTER 11. THE SHELL STRUCTURE**

limit of the $\alpha_{k_1}$, so long as the Schwartz-Bruhat function is supported over the $k$th stratum of the divisorial filtration.

The images under $\Phi_{F,\chi|_{C^1_F}}$ of such Schwartz-Bruhat functions comprise of the finite union of the orbital Schauder bases at the places $v\in P_{k+1}-P_k$, and the limit process as $k_1\to+\infty$ turns them, after global inversion by Theorem 2.2.3.2, into the corresponding $S'$-local orbital Schauder basis. We can choose these elements to belong to the Paley-Wiener level at time $\lambda'>0$ large enough, and the same method used in the estimates from Theorem 10.3.2.1 shows that such operator is the limit of the finite rank kernels from (11.2.2.12) from the proof of Theorem 11.2.2.1.

This gives us its trace, and hence the value of:

$$
\sum_{\xi\in F^\times}\int_{g\in E^1_F}\rho(\tau(t))((\alpha_{k+1}-\alpha_k)k^\Delta_{\mathrm{geom},a,I,s,\varphi})(\tau(t),\xi g\tau(t))\beta_{S'}(\xi g\tau(t))1_{g\in\mathrm{GL}_1(\mathbf A_{F,S'})^{>\lambda'}}(\xi g\tau(t))\,\mathrm{d}\mu_1(g)\,\frac{\mathrm{d}t}{t} \tag{11.3.2.4}
$$

which, as $\lambda'$ is large enough and for $\Lambda\to+\infty$ in the regime $\varepsilon\Lambda=o(1)$, attains the limit value:

$$
\sum_{\varepsilon_p}N(\chi\lvert\cdot\rvert^{\varepsilon_p}_F)\int_{C_F}\varphi(g)\chi(g)\lvert g\rvert^{\varepsilon_p-1/2}_F\,\mathrm{d}\bar\mu(g) \tag{11.3.2.5}
$$

which is the right side of (7.4.2.1) from Theorem 7.4.2.1. The Theorem follows from the Poisson Summation Formula (see Proposition B.4.1.2). $\square$
