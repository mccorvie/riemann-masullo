## PDF page 395

CHAPTER 9

Hardy-Sobolev topologies

9.1. Sobolev spaces $W^{s,2}(G)$ 395

9.1.1. Sobolev spaces of Hausdorff locally compact abelian groups 396

9.1.2. Sobolev spaces $W^{s,2}$ of $\mathbf{R}_{>0}$-modulated groups 399

9.2. Hardy-Sobolev spaces $W^s_I(G)$ and Paley-Wiener conditions 403

9.2.1. The special case $I=\{b\}$: $b$-line Hardy-Sobolev spaces and Paley-Wiener Theorem 404

9.2.1.1. Duality 409

9.2.2. General base intervals: the Hardy-Sobolev spaces $W^s_I(G)$ 411

9.2.2.1. The Hardy-Sobolev spaces $W^s_I(\mathbf{R}_{>0})$ 412

9.2.2.2. The Hardy-Sobolev spaces $W^s_I(G)$ 416

9.3. Module structures over $\mathcal{D}(G)$ and approximate units 419

9.3.1. Module structure over $\mathcal{D}(G)$ 419

9.3.2. Approximate units 422

9.3.2.1. The case $I=\{b\}$ 422

9.3.2.2. The general case: approximate units in $W^s_I(G)$ 425

9.3.3. Trace of the regular representation on $W^s_I(G)$ 426

9.3.3.1. Cutoffs 426

9.3.3.2. Calculation of the trace of $M_\rho\circ A(\varphi)$ 429

Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\chi$ be a continuous character of $C_F$, respectively of $J_{F,S}$.

In this Chapter, we coarsen the nuclear Fréchet topologies on $\mathcal{S}_\mathrm{E}(C_F)$, $\mathcal{S}_I(J_{F,S})$ and their $C_F^1$-, respectively $J_{F,S}^1$-isotypes, for $I$ an appropriate choice of non-empty connected interval of the real line, as well as the nuclear Fréchet topologies on $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C_F^1},\mathcal{S}_0(\mathbf{A}_F))$, respectively $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{J_{F,S}^1},\mathcal{S}(\mathbf{A}_{F,S}))$, to normed topologies arising by integration along a chosen vertical line within the Riemann surfaces $\Omega(C_F)$, respectively $\Omega(J_{F,S})$, with continuity requirements on finitely many degrees of holomorphic differentiation.

In other words, we form completions of the above Hausdorff locally convex topological $\mathbf{C}$-vector spaces, to Sobolev spaces.

These will serve as the ambients for the trace calculation which is the main subject of study of this work.

**9.1. Sobolev spaces $W^{s,2}(G)$**

We discuss here general constructions of normed topologies on the Hausdorff locally convex topological complex vector spaces $\mathcal{S}_\mathrm{E}(C_F)$ and $\mathcal{S}_I(J_{F,S})$ of Schwartz-Bruhat functions on the idele class group $C_F$, respectively on the $S$-idele class group $J_{F,S}$, with exponential, respectively $I$-exponential decay, for some appropriate chocie of non-empty connected interval $I\subset\mathbf{R}$.

Equivalently, this amounts to constructing continuous norms on $\mathcal{S}_\mathrm{E}(C_F)$, respectively $\mathcal{S}_I(J_{F,S})$, and study the Banach spaces obtained by completion.

**395**

## PDF page 396

**396** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

We will further study the closed subspaces defined as the closures of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C_F^1},\mathcal{S}_0(\mathbf{A}_F))$, respectively $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{J_{F,S}^1},\mathcal{S}(\mathbf{A}_{F,S}))$, for $\chi$ a continuous character of $C_F$, respectively of $J_{F,S}$.

We will be discussing the resulting Banach spaces in the generality of $\mathbf{R}_{>0}$-modulated Hausdorff locally compact abelian groups $G$.

**9.1.1. Sobolev spaces of Hausdorff locally compact abelian groups.** We begin with a definition, following [GR, §1,2], with an eye on [Co, Appendix I, p.59].

DEFINITION 9.1.1.1. Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a choice of Haar measure on $G$, $\mu_{\widehat G}$ the corresponding Plancherel measure. Let $s\in\mathbf{R}$ a real number. We define a Sobolev weight on $G$ to be a continuous function:

$$
w:\widehat G\to[0,+\infty) \tag{9.1.1.1}
$$

such that there exists a real number $C_w>0$ such that:

$$
w(\chi\chi')\le C_w(w(\chi)+w(\chi')) \tag{9.1.1.2}
$$

for all $\chi,\chi'\in\widehat G$. We define $H^s_w(G,\mu_G)$ to be the completion of $C_c(\widehat G)$ with respect to the linear topology induced by the norm:

$$
\lVert f\rVert_{H^s_w(G,\mu_G)}:=\left(\int_{\widehat G}\lvert\widehat f(\chi)\rvert^2(1+w(\chi)^2)^{s/2}\,\mathrm{d}\mu_{\widehat G}(\chi)\right)^{1/2}. \tag{9.1.1.3}
$$

LEMMA 9.1.1.2. *Let $G$ be a Hausdorff locally compact abelian group, $w:\widehat G\to[0,+\infty)$ a Sobolev weight, $s\in\mathbf{R}$ a real number. Then $H^s_w(G,\mu_G)$ is a Hilbert space. If $G$ is second-countable, then $H^s_w(G,\mu_G)$ is a separable Hilbert space.*

PROOF. Since $w$ is continuous, so is $(1+w^2)^{s/2}$: this is so if $s\ge 0$, and since $1+w^2$ is real valued, nonnegative and nowhere vanishing over $\widehat G$, $(1+w^2)^{s/2}$ is continuous for negative $s$ too. As such, $\mu:=(1+w^2)^{s/2}\mu_{\widehat G}$ is a Radon measure on $\widehat G$.

By [Fol, Prop.7.9], we have $H^s_w(G,\mu_G)=L^2(\widehat G,(1+w^2)^{s/2}\mu_{\widehat G})$. We deduce that $H^s_w(G,\mu_G)$ is a Hilbert space for any $s\in\mathbf{R}$. Being $\widehat G$ Hausdorff locally compact, if $G$ is second-countable then so is $\widehat G$. We deduce, by [Fol, Thm.7.8], that $\mu$ is a regular $\sigma$-finite Radon measure on $\widehat G$, and by [Coh, Prop.3.4.5] we deduce that $H^s_w(G,\mu_G)$ is a separable metric space, hence separable as a Hilbert space. $\square$

We refer the reader to [GR, §1,2] for more on the Sobolev spaces $H^s_w(G,\mu_G)$ attached to a Hausdorff locally compact abelian group, and to [FG, §2]. We observe that the Sobolev weight $w$ from Definition 9.1.1.1 is denoted $\gamma$ in [GR, §1(3), Def.1], and that the real number $s$ in [GR, §1], assumed to be only nonnegative in loc.cit., and the results contained therein, is related to our $s$ by doubling, i.e. the space $H^s_\gamma(G)$ from [GR, §1, Def.1] is our $H^{s/2}_w(G,\mu_G)$ for $w=\gamma$.

We have the following basic properties of $H^s_w(G,\mu_G)$:

PROPOSITION 9.1.1.3. *Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a choice of Haar measure on $G$, $\mu_{\widehat G}$ its Plancherel measure on $\widehat G$. Let $s\in\mathbf{R}$ be a real number, and $w:\widehat G\to[0,+\infty)$ a Sobolev weight. Assume $s$ is nonnegative.*

*(1) The inclusion:*

$$
H^s_w(G,\mu_G)\to L^2(G,\mu_G) \tag{9.1.1.4}
$$

*is a continuous linear operator, satisfying, for every $f\in H^s_w(G,\mu_G)$:*

$$
\lVert f\rVert_{L^2(G,\mu_G)}\le\lVert f\rVert_{H^s_w(G,\mu_G)}. \tag{9.1.1.5}
$$

## PDF page 397

**9.1. SOBOLEV SPACES $W^{s,2}(G)$** · **397**

(2) *If $s'>s$, then for any $f\in H^s_w(G,\mu_G)$ we have:*

$$
\lVert f\rVert_{H^s_w(G,\mu_G)}\le\lVert f\rVert_{H^{s'}_w(G,\mu_G)} \tag{9.1.1.6}
$$

and the inclusion $H^{s'}_w(G,\mu_G)\subset H^s_w(G,\mu_G)$ is continuous.

(3) *(Sobolev Embedding) If $(1+w^2)^{-s/2}\in L^1(\widehat G,\mu_{\widehat G})$, then every element of $H^s_w(G,\mu_G)$ is represented by a unique continuous function on $G$ vanishing at infinity, resulting in a canonical linear inclusion:*

$$
H^s_w(G,\mu_G)\to C_0(G). \tag{9.1.1.7}
$$

*There exists a real number $C(w,s)>0$ with the property that, for every $f\in H^s_w(G,\mu_G)$, we have:*

$$
\lVert f\rVert_u\le C(w,s)\,\lVert f\rVert_{H^s_w(G,\mu_G)}. \tag{9.1.1.8}
$$

PROOF. (1) : We have, by [DE, Thm.3.4.8], for every $f\in H^s_w(G,\mu_G)$:

$$
\lVert f\rVert_{L^2(G,\mu_G)}=\lVert\widehat f\rVert_{L^2(\widehat G,\mu_{\widehat G})}=\left(\int_{\widehat G}\lvert\widehat f(\chi)\rvert^2\,\mathrm{d}\mu_{\widehat G}(\chi)\right)^{1/2}\le\left(\int_{\widehat G}\lvert\widehat f(\chi)\rvert^2(1+w(\chi)^2)^{s/2}\,\mathrm{d}\mu_{\widehat G}(\chi)\right)^{1/2}=\lVert f\rVert_{H^s_w(G,\mu_G)}
$$

where we have used the assumption $s\ge 0$ to deduce the inequality $1\le(1+w(\chi)^2)^{s/2}$ as functions on $\widehat G$.

(2) : Since $s'>s$, we have $(1+w(\chi)^2)^{s/2}\le(1+w(\chi)^2)^{s'/2}$ since $s\ge 0$. The inequality in (9.1.1.6) therefore follows from the definition of $\lVert\cdot\rVert_{H^s_w(G,\mu_G)}$, which proves that $H^{s'}_w(G,\mu_G)$ is contained in $H^s_w(G,\mu_G)$ as a linear subspace of $L^2(G,\mu_G)$, and the inclusion $H^{s'}_w(G,\mu_G)\subset H^s_w(G,\mu_G)$ is continuous.

(3) : Let $f\in H^s_w(G,\mu_G)$ be an arbitrary element, and call $u:=\widehat f$. By [Ru, Thm.1.2.4(d)] (see also the proof of [DE, Thm.3.2.1] on [DE, p.65]), we have, for $\mu_G$-almost all $g\in G$:

$$
\lvert u(g)\rvert\le\lVert\widehat u\rVert_{L^1(\widehat G,\mu_{\widehat G})}=\int_{\widehat G}\lvert\widehat u(\chi)\rvert\frac{(1+w(\chi)^2)^{s/4}}{(1+w(\chi)^2)^{s/4}}\,\mathrm{d}\mu_{\widehat G}(\chi)\le\left(\int_{\widehat G}\lvert\widehat u(\chi)\rvert^2(1+w(\chi)^2)^{s/2}\,\mathrm{d}\mu_{\widehat G}(\chi)\right)^{1/2}\left(\int_{\widehat G}\frac{1}{(1+w(\chi)^2)^{s/2}}\,\mathrm{d}\mu_{\widehat G}(\chi)\right)^{1/2}
$$

$$
=\lVert f\rVert_{H^s_w(G,\mu_G)}\lVert(1+w^2)^{-s/2}\rVert^{1/2}_{L^1(\widehat G,\mu_{\widehat G})}.
$$

and we deduce that $u$ is uniformly bounded over $G$. By (1) and [DE, Thm.3.4.8], we have $u\in L^2(G,\mu_G)$. From the above inequalities, we deduce that $\widehat u$ is absolutely $\mu_{\widehat G}$-integrable over $\widehat G$, and so $u$ is an element of $C_0(G)$ by [DE, Thm.3.2.1]. Upon calling $C(w,s):=\lVert(1+w^2)^{-s/2}\rVert^{1/2}_{L^1(\widehat G,\mu_{\widehat G})}$, the above inequalities imply that (9.1.1.8) holds. Formation of $u$ is linear with respect to $f\in H^s_w(G,\mu_G)$, and (9.1.1.8) implies that the resulting linear operator $H^s_w(G,\mu_G)\to C_0(G)$ is continuous. It is injective by [DE, Thm.3.2.1] (see the proof of injectivity on [DE, p.65]). $\square$

REMARK 9.1.1.4. We further refer the reader to [GR, Prop.1,2] for (1) and (2) in Proposition 9.1.1.3.

LEMMA 9.1.1.5. *Let $G$ be a Hausdorff locally compact abelian group. Let $s\ge 0$ be a real number. The pairing:*

$$
C_c(\widehat G)\times C_c(\widehat G)\to\mathbf{C} \tag{9.1.1.9}
$$

## PDF page 398

**398** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

defined by the assignment:

$$
(\phi,\psi)\mapsto\int_{\widehat G}\phi(\chi)\psi(\chi)\,\mathrm{d}\mu_{\widehat G}(\chi) \tag{9.1.1.10}
$$

*extends uniquely to a continuous non-degenerate bi-linear form:*

$$
\langle\cdot,\cdot\rangle_{s,w}:H^s_w(G,\mu_G)\times H^{-s}_w(G,\mu_G)\to\mathbf{C} \tag{9.1.1.11}
$$

inducing a canonical linear isometry

$$
H^s_w(G,\mu_G)'_\beta\to H^{-s}_w(G,\mu_G) \tag{9.1.1.12}
$$

*from the strong dual of $H^s_w(G,\mu_G)$, whose topology is normed by the dual norm, to the Sobolev space $H^{-s}_w(G,\mu_G)$, whose topology is normed by the norm $\lVert\cdot\rVert_{H^{-s}_w(G,\mu_G)}$ from (9.1.1.3).*

PROOF. By [Fol, Thm.6.15], the pairing:

$$\langle\cdot,\cdot\rangle:L^2(\widehat G,\mu)\times L^2(\widehat G,\mu)\to\mathbf{C}$$

defined by:

$$
\langle\phi,\psi\rangle:=\int_{\widehat G}\phi(\chi)\psi(\chi)\,\mu(\chi) \tag{9.1.1.13}
$$

upon choosing the measure space $(X,\mathcal{M},\mu)$ to be $X:=\widehat G$, $\mathcal{M}$ the Borel $\sigma$-algebra, and $\mu_s:=(1+w^2)^{s/2}\mu_{\widehat G}$, with $p=q=2$, is separately continuous and induces an isometry between $L^2(\widehat G,\mu_s)'_\beta=H^s_w(G,\mu_G)'_\beta$ equipped with the dual norm (defined in [Fol, Prop.6.13]) and $L^2(\widehat G,(1+w^2)^{s/2}\mu_{\widehat G})$ itself, which is $H^s_w(G,\mu_G)$.

For every $\phi\in L^2(\widehat G,\mu_s)$ and $\psi\in L^2(\widehat G,\mu_{-s})$, the integral:

$$
\int_{\widehat G}\lvert\phi(\chi)\psi(\chi)\rvert\,\mathrm{d}\mu_{\widehat G}(\chi) \tag{9.1.1.14}
$$

converges, i.e. $\phi\cdot\psi$, as a complex-valued measurable function on $\widehat G$, is absolutely integrable. Indeed, we have:

$$
\int_{\widehat G}\lvert\phi(\chi)\psi(\chi)\rvert\,\mathrm{d}\mu_{\widehat G}(\chi)=\int_{\widehat G}\lvert\phi(\chi)\psi(\chi)\rvert\frac{(1+w(\chi)^2)^{s/4}}{(1+w(\chi)^2)^{s/4}}\,\mathrm{d}\mu_{\widehat G}(\chi)\le\lVert\phi\rVert^{1/2}_{L^2(\widehat G,\mu_s)}\lVert\psi\rVert^{1/2}_{L^2(\widehat G,\mu_{-s})}. \tag{9.1.1.15}
$$

We define $\langle\phi,\psi\rangle_{s,w}$ to be the value of the integral $\int_{\widehat G}\phi(\chi)\psi(\chi)\,\mathrm{d}\mu_{\widehat G}(\chi)$. The notation is justified since the restriction of $\langle\cdot,\cdot\rangle_{s,w}$ to $C_c(\widehat G)\times C_c(\widehat G)$ is the pairing defined in (9.1.1.10).

We have, for all such $\phi,\psi\in L^2(\widehat G,\mu_s)$:

$$
\langle\phi(1+w^2)^{-s/2},\psi\rangle=\langle\phi,\psi(1+w^2)^{-s/2}\rangle=\langle\phi,\psi\rangle_{s,w} \tag{9.1.1.16}
$$

where the products $\phi(1+w^2)^{-s/2}$, respectively $\psi(1+w^2)^{-s/2}$, are as complex-valued measurable functions on $\widehat G$, noting that the pairing $\langle\cdot,\cdot\rangle$ in (9.1.1.16) is defined on $(\phi,\psi(1+w^2)^{-s/2})$, respectively $(\phi(1+w^2)^{-s/2},\psi)$.

By Proposition 9.1.1.3(1), the pairing $\langle\cdot,\cdot\rangle_{s,w}$ is sequentially continuous with respect to each argument, hence indeed separately sequentially continuous with respect to the norm topology defined by $\lVert\cdot\rVert_{H^s_w(G,\mu_G)}$ in each argument, since $\langle\cdot,\cdot\rangle$ is.

Sequential continuity of linear functionals implies continuity, the topology on $H^s_w(G,\mu_G)$ being metric. Since $H^s_w(G,\mu_G)$ is a Banach space, being a Hilbert space by Lemma 9.1.1.2, hence so is its strong dual, normed with the dual norm, and by the Uniform Boundedness Theorem the pairing $\langle\cdot,\cdot\rangle_{s,w}$ is continuous, being separately continuous (see [Bou-TVS, Ch.IV, §4.6, IV.26, Thm.2]). The same conclusion also follows from Proposition C.2.3.11.

The linear endomorphism $C_c(\widehat G)\to C_c(\widehat G)$ sending $\psi$ to $(1+w^2)^{-s/2}\psi$ therefore extends to a continuous linear operator $H^s_w(G,\mu_G)'_\beta\to H^{-s}_w(G,\mu_G)$.

## PDF page 399

**9.1. SOBOLEV SPACES $W^{s,2}(G)$** · **399**

Indeed, for continuous functional $T\in H^s_w(G,\mu_G)'_\beta$, by [Fol, Prop.6.13] there exists a unique $\psi\in H^s_w(G,\mu_G)$ such that $T=T_\psi$, with $T_\psi$ the functional defined as:

$$
T_\psi:\phi\mapsto T_\psi(\phi):=\langle\phi,\psi\rangle.
$$



The functional on $H^s_w(G,\mu_G)$:

$$
(1+w^2)^{-s/2}T
$$

assigned by:

$$
(1+w^2)^{-s/2}T(\phi):=\langle(1+w^2)^{-s/2}\phi,\psi\rangle
$$

is continuous on $H^{-s}(G,\mu_G)$, and hence there exists a unique $\psi_0\in H^{-s}(G,\mu_G)$ representing it. The continuous linear operator $H^s_w(G,\mu_G)'_\beta\to H^{-s}_w(G,\mu_G)$ induced by $\langle\cdot,\cdot\rangle_{s,w}$ sends $T=T_\psi$ to $\psi_0$. We have $\psi_0=(1+w^2)^{s/2}\psi$, and we compute:

$$
\lVert\psi_0\rVert_{H^{-s}_w(G,\mu_G)}=\lVert\psi\rVert_{H^s_w(G,\mu_G)}=\lVert T\rVert_{H^s_w(G,\mu_G)'_\beta} \tag{9.1.1.17}
$$

the last equality being provided by [Fol, Prop.6.13].

The identities in (9.1.1.17) imply that the continuous linear operator from (9.1.1.12) is an isometry, hence injective.

It is bijective on $C_c(\widehat G)$ being $(1+w^2)^{-s/2}$ continuous and nowhere vanishing, with continuous and nowhere vanishing reciprocal. It follows that it has dense range, and it is therefore surjective, being its range closed (as is the range of any linear topological embedding of a complete Hausdorff locally convex topological vector space into another). It is therefore an isometric isomorphism. $\square$

**9.1.2. Sobolev spaces $W^{s,2}$ of $\mathbf{R}_{>0}$-modulated groups.** We will be specializing the Sobolev spaces defined in Definition 9.1.1.1 and discussed in Proposition 9.1.1.3, to the case $G=\widehat{C_F}$, for $F$ a number field, for $\mu_G=\widehat{\bar\mu}$ the Plancherel measure associated to the Haar measure $\bar\mu$ on $C_F$, whose Plancherel measure is $\bar\mu$ by Fourier inversion, and for $w:\widehat G=C_F\to[0,+\infty)$ of the following form:

$$
w(g):=\lvert\log\lvert g\rvert_F\rvert \tag{9.1.2.1}
$$

which indeed satisfies (9.1.1.2) by multiplicativity of $\lvert\cdot\rvert_F$, additivity of $\log:\mathbf{R}_{>0}\to\mathbf{R}$, and the triangle inequality for the Euclidean absolute value $\lvert\cdot\rvert$ on $\mathbf{R}$, which gives $C_w=1$.

Since we are choosing $G=\widehat{C_F}$, and not $G=C_F$, we introduce notation for $H^2_w(G,\mu_G)$, which we will be retaining throughout the remainder of this work.

We do so by discussing the intermediate case of $\mathbf{R}_{>0}$-modulated Hausdorff locally compact abelian groups. We recall from Definition D.2.1.1 (see also §D.3.3). We recall that a Hausdorff locally compact abelian group $G$ is $\mathbf{R}_{>0}$-modulated if it is equipped with a continuous surjective proper homomorphism $\lvert\cdot\rvert_G:G\to\mathbf{R}_{>0}$. The fibre $G^1$ over the neutral element $1\in\mathbf{R}_{>0}$ is therefore compact Hausdorff.

We refer the reader to Theorem D.3.3.7 for more on function spaces of Schwartz-Bruhat functions (with $I$-exponential decay) on $\mathbf{R}_{>0}$-modulated groups.

DEFINITION 9.1.2.1 (Sobolev Spaces of $\mathbf{R}_{>0}$-modulated groups). Let $G$ be an $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$. We let $\mu_G$ be a choice of Haar measure on $G$, and $\mu_{\widehat G}$ its Plancherel measure. Let $s\ge 0$ be a real number. We define:

$$
W^{s,2}(G):=H^s_w(\widehat G,\mu_{\widehat G}) \tag{9.1.2.2}
$$

for $w$ the choice of Sobolev weight from (9.1.2.1). We denote by $\lVert\cdot\rVert_{s,2}$ the norm:

$$
\lVert f\rVert_{s,2}:=\left(\int_G\lvert f(g)\rvert^2(1+\lvert\log\lvert g\rvert_G\rvert^2)^{s/2}\,\mathrm{d}\mu_G(g)\right)^{1/2}. \tag{9.1.2.3}
$$

## PDF page 400

**400** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

We refer to $s$ as the Sobolev degree of $W^{s,2}(G)$.

Before stating the next Lemma, we observe the following. For $G$ an $\mathbf{R}_{>0}$-modulated group, and for any choice $\tau$ of continuous homomorphic section to the module $\lvert\cdot\rvert_G$ (noting that such sections exist by Remark D.2.1.2), we have an isomorphism, induced by the choice of $\tau$, of Hausdorff locally compact abelian groups $G\simeq\mathbf{R}_{>0}\times G^1$, with $G^1:=\ker(\lvert\cdot\rvert_G)$ a compact Hausdorff abelian group.

The choice of Haar measure $\mu_G$ on $G$ is pushed forward to $\frac{\mathrm{d}t}{t}\otimes\mu_1$ for a unique Haar measure $\mu_1$ on $G^1$. This isomorphism is compatible with formation of dual groups (see [DE, Cor.3.6.2] combined with functoriality of formation of the dual group with respect to continuous group homomorphisms), giving an isomorphism of Hausdorff locally compact abelian groups $\widehat G\simeq\widehat{\mathbf{R}_{>0}}\times\widehat{G^1}$ where $\widehat{\mathbf{R}_{>0}}\simeq\mathbf{R}$ upon choosing the basic character $t\mapsto t^{2\pi i}$ to choose the isomorphism $\widehat{\mathbf{R}_{>0}}\simeq\mathbf{R}$.

Since $\widehat{G^1}$ is a discrete abelian group, every continuous $1$-parameter group $\mathbf{R}_{>0}\to\widehat{G^1}$ is constant (since its image is connected and contains the neutral element), and every continuous $1$-parameter group $\mathbf{R}_{>0}\to\widehat G$ has image contained within $\widehat{\mathbf{R}_{>0}}\times 1$, which is the connected component of the neutral element of $\widehat G$.

The $\mathbf{C}$-algebra of differential operators on $\widehat G$ is therefore generated by a single degree-$1$ differential operator, which we call $D$. Under the isomorphism $\widehat{\mathbf{R}_{>0}}\simeq\mathbf{R}$, $D$ matches a generator for the $\mathbf{C}$-algebra of differential operators on $\mathbf{R}$, and we can renormalize $D$ so as to arrange such generator to be $\partial_x$.

We further refer the reader to Definition D.1.6.5 and Definition D.1.6.8 of §D.1.6 from Appendix D, for more on differential operators on Hausdorff locally compact abelian groups.

LEMMA 9.1.2.2. *Let $G$ be an $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$. We let $\mu_G$ be a choice of Haar measure on $G$, and $\mu_{\widehat G}$ its Plancherel measure. Let $s=2N\ge 0$ an even integer. The normed topology on the Hilbert space $W^{s,2}(G)$ is equivalently induced by the finite family of seminorms:*

$$
\{\lVert\cdot\rVert_{s,k,2}\}_{0\le k\le N} \tag{9.1.2.4}
$$

*assigned by, for each $f\in W^{s,2}(C_F)$:*

$$
\lVert f\rVert_{s,k,2}:=\left(\int_{\widehat G}\lvert D^k\widehat f(\chi)\rvert^2\,\mathrm{d}\mu_{\widehat G}(\chi)\right)^{1/2} \tag{9.1.2.5}
$$

*where $D$ is any generator of the $\mathbf{C}$-algebra of differential operators on $\widehat G$.*

PROOF. An equivalent topology on $W^{s,2}(G)$ is induced by the finite family of seminorms:

$$
\{\lVert\cdot\rVert'_{s,k,2}\}_{0\le k\le s/2} \tag{9.1.2.6}
$$

with, for any $f\in W^{s,2}(G)$:

$$
\lVert f\rVert'_{s,k,2}:=\left(\int_G\lvert f(g)\rvert^2\lvert\log\lvert g\rvert_G\rvert^{2k}\,\mathrm{d}\mu_G(g)\right)^{1/2}. \tag{9.1.2.7}
$$

Indeed, by [NB, Thm.5.2.2(e)], each $\lVert\cdot\rVert'_{s,k,2}$ is continuous on $W^{s,2}(G)$, and therefore induces a locally convex topology that is at most as fine as the intrinsic normed topology on $W^{s,2}(G)$. On the other hand, we have:

$$
(1+\lvert\log\lvert g\rvert_G\rvert^2)^{s/2}=\sum_{0\le k\le s/2}\binom{s/2}{k}\lvert\log\lvert g\rvert_G\rvert^{2k} \tag{9.1.2.8}
$$

and hence the following inequality holds for any $f\in W^{s,2}(G)$:

$$
\lVert f\rVert^2_{s,2}\le\left(\sum_{0\le k\le s/2}\binom{s/2}{k}(\lVert f\rVert'_{s,k,2})^2\right)^{1/2}\le C_s\left(\sum_{0\le k\le s/2}\lVert f\rVert'_{s,k,2}\right) \tag{9.1.2.9}
$$

## PDF page 401

**9.1. SOBOLEV SPACES $W^{s,2}(G)$** · **401**

where $C_s>0$ is an absolute constant, which implies by [Bou-TVS, Ch.II, §1.4, II.7, Cor.1] that the topology induced on $W^{s,2}(G)$ by the finite family of seminorms $\{\lVert\cdot\rVert'_{s,k,2}\}_{0\le k\le s/2}$ is at least as fine as the intrinsic norm topology on $W^{s,2}(G)$, and hence the two topologies are equivalent.

The constant $C_s>0$ is obtained as follows: upon calling $a_k^2:=\binom{s/2}{k}$, we let $A>0$ be any real number such that, on the Euclidean space $\mathbf{R}^{1+(s/2)}$, the two norms $\lVert\cdot\rVert_2$ and $\lVert\cdot\rVert_1$, are related by the inequality $\lVert\cdot\rVert_2\le A\lVert\cdot\rVert_1$. Then we have $\lVert(a_k\lVert f\rVert'_{s,k,2})_{0\le k\le s/2}\rVert_2\le A\lVert(a_k\lVert f\rVert'_{s,k,2})_{0\le k\le s/2}\rVert_1=A\sum_{0\le k\le s/2}a_k\lVert f\rVert'_{s,k,2}\le AA_0\sum_{0\le k\le s/2}\lVert f\rVert'_{s,k,2}$ where $A_0:=\sup_{0\le k\le s/2}a_k$. We then define $C_s:=AA_0$.

By [DE, Thm.3.4.8], we have:

$$
\lVert f\rVert'_{s,k,2}=\left(\int_{\widehat G}\lvert\mathcal{F}(f(g)(\log\lvert g\rvert_G)^k)(\chi)\rvert^2\,\mathrm{d}\mu_{\widehat G}(\chi)\right)^{1/2} \tag{9.1.2.10}
$$

for each integer $0\le k\le s/2$, where $\mathcal{F}:L^2(G,\mu_G)\to L^2(\widehat G,\mu_{\widehat G})$ is the Fourier transform, normalized according to the assignment $\phi\mapsto\mathcal{F}(\phi)(\chi):=\int_G\phi(g)\bar\chi(g)\,\mathrm{d}\mu_{\widehat G}(\chi)$.

Upon choosing a continuous homomorphic section $\tau$ to the idelic norm, we normalize the choice of generator $D$ of the $\mathbf{C}$-algebra of differential operators on $\widehat G$, so as to match under the isomorphism of Hausdorff locally compact abelian groups $\widehat G\simeq\mathbf{R}\times\widehat{G^1}$ induced by $\tau$ and by the choice of basic character $t\mapsto t^{2\pi i}$ on $\mathbf{R}_{>0}$, the differential operators $-(2\pi i)^{-1}\partial_x\otimes 1$.

We have, as functions on $\widehat G$:

$$
\mathcal{F}(f(g)(\log\lvert g\rvert_G)^k)(\chi)=\int_{\mathbf{R}_{>0}}t^{-2\pi ix}\left(\int_{G^1}\overline{\chi}(g_0)f(\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\right)(\log(t))^k\frac{\mathrm{d}t}{t} \tag{9.1.2.11}
$$

where $x\in\mathbf{R}$ is a real number uniquely determined by $\chi$ such that $\chi(\tau(t))=t^{-2\pi ix}$ as smooth functions of $t\in\mathbf{R}_{>0}$, and $g_0\in C_F^1$ is the unique element such that $g=\tau(t)g_0$.

We now assume $f\in C_c^\infty(C_F)$. The rightmost integral from (9.1.2.11) then in turn equals, by [Fol, Thm.8.22(d)]:

$$
(-2\pi i)^{-k}\partial_x^k\int_{\mathbf{R}_{>0}}t^{-2\pi ix}\left(\int_{G^1}\overline{\chi}(g_0)f(\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\right)\frac{\mathrm{d}t}{t}=(D^k\widehat f)(\chi). \tag{9.1.2.12}
$$

We further refer the reader to Lemma D.1.6.19.

Upon combining this with (9.1.2.10) we obtain $\lVert f\rVert'_{s,k,2}=\lVert f\rVert_{s,k,2}$ on all $f\in C_c^\infty(G)$ for each integer $0\le k\le s/2$, up to a positive constant multiplier independent of $f$ (and depending only on the normalization of $D$). By continuity of $\lVert\cdot\rVert_{s,k,2}$ and $\lVert\cdot\rVert'_{s,k,2}$ for each $0\le k\le s/2$, the identity $\lVert f\rVert'_{s,k,2}=\lVert f\rVert_{s,k,2}$ remains valid, up to a positive constant multiplier depending only on the normalization of $D$, on all $f\in W^{s,2}(G)$.

This shows that the seminorms $\{\lVert\cdot\rVert_{s,k,2}\}_{0\le k\le s/2}$ generate the same topology defined on $W^{s,2}(G)$ by the norm $\lVert\cdot\rVert_{s,2}$. $\square$

REMARK 9.1.2.3. Lemma 9.1.2.2 holds more generally for all Hausdorff locally compact abelian groups, upon generalizing the definition of $\lVert\cdot\rVert_{s,k,2}$. Namely, upon using all monomial elements of the $\mathbf{C}$-algebra of differential operators of $G$, in place of the sole $D^k$ from (9.1.2.5). This recovers the definition in (9.1.2.5) for $\mathbf{R}_{>0}$-modulated $G$, the kernel $G^1$ of the module $\lvert\cdot\rvert_G$ is compact Hausdorff, with, therefore, discrete dual. The only non-trivial differential operators on $\widehat G$ are therefore contributed by $G/G^1\simeq\mathbf{R}_{>0}$, and generated by $D$, up to a choice of normalization for $D$.

For $G=\mathbf{R}$, the seminorms $\lVert\cdot\rVert_{s,k,2}$ recovers the classical Sobolev seminorms on $\mathbf{R}$, i.e. $\lVert f\rVert_{s,k,2}=\lVert\partial_x^k f\rVert_{L^2(\mathbf{R},\mathrm{d}x)}$ for all $0\le k\le s/2$.

## PDF page 402

**402** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

LEMMA 9.1.2.4. *Let $G$ be an $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$. Let $\mu_G$ be a choice of Haar measure on $G$. Let $s\ge 0$ be a real number. The function of $g\in G$:*

$$
(1+\lvert\log\lvert g\rvert_G\rvert^2)^{-s/2} \tag{9.1.2.13}
$$

*is absolutely integrable if and only if $s>1$.*

PROOF. We call $\phi(g):=(1+\lvert\log\lvert g\rvert_G\rvert^2)^{-s/2}$. The function $\phi$ is continuous over $G$, and invariant under the left-translation action of the compact Hausdorff closed subgroup $G^1$, since $\lvert\cdot\rvert_G$ is.

To check integrability of $\phi$ it therefore suffices to choose a continuous homomorphic section $\tau$ to the module, and analyze the integrability of the continuous function $\psi(t):=\phi(\tau(t))=(1+\lvert\log(t)\rvert^2)^{-s/2}$ on $\mathbf{R}_{>0}$ with respect to the normalized Haar measure $\mathrm{d}t/t$.

Since $\psi(t)=\psi(1/t)$, it is enough to analyze the integrability of $\psi$ over $(1,+\infty)\subset\mathbf{R}_{>0}$ only. We have:

$$
\int_0^1\frac{1}{(1+\lvert\log(t)\rvert^2)^{s/2}}\frac{\mathrm{d}t}{t}=\int_0^{+\infty}\frac{1}{(1+\lvert x\rvert^2)^{s/2}}\,\mathrm{d}x
$$

and the rightmost integral converges if and only if $s>1$. $\square$

PROPOSITION 9.1.2.5. *Let $G$ be an $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$. Let $\mu_G$ be a choice of Haar measure on $G$. The linear topological isomorphism:*

$$
T_s:W^{s,2}(G)'_\beta\to W^{-s,2}(G) \tag{9.1.2.14}
$$

*is an isometry with respect to the dual norm on the source, and the norm $\lVert\cdot\rVert_{-s,2}$ from (9.1.2.3) on the target, equivariant with respect to the adjoint action of the continuous left-translation action $\rho_G$ of $G$ on $W^{s,2}(G)$, and the right-translation action of $G$ on $W^{-s,2}(G)$.*

*Let $s>1$ be a real number. For $t\in\mathbf{R}$ and $m\ge 0$, the continuous function:*

$$
\eta_{t,m}(g):=\lvert g\rvert^{it}(\log\lvert g\rvert_G)^m \tag{9.1.2.15}
$$

*of $g\in G$, is an element of $W^{-s,2}(G)$ if and only if the following condition holds:*

$$
m<\frac{s-1}{2}. \tag{9.1.2.16}
$$

PROOF. By Lemma 9.1.1.5, indeed the linear operator in (9.1.2.14) exists and it is defined in (9.1.1.12) applied to $\widehat G$ and to the Plancherel measure of the Haar measure $\mu_G$, and $w=\lvert\log\lvert\cdot\rvert_G\rvert$. By the Lemma, it is an isometry.

To identify the unique continuous action on $W^{-s,2}(G)$ promoting (9.1.2.14) into an equivariant isometry, we observe that the continuous pairing $\langle\cdot,\cdot\rangle_{s,w}$ from (9.1.1.11) which uniquely determines (9.1.2.14) is invariant upon letting $G$ act through $\rho_G$ on the leftmost argument, and through the right-translation action of $G$ on $W^{-s,2}(G)$, by invariance of the Haar measure $\mu_G$. Since the pairing is nondegenerate, this uniquely identifies the desired action on $W^{-s,2}(G)$ with the continuous right-translation action of $G$ on $W^{-s,2}(G)$.

The function $\eta_{t,m}$ from (9.1.2.15) is continuous on $G$, and it is an element of $W^{-s,2}(G)$ if and only if the integral:

$$
\int_G\lvert\log\lvert g\rvert_G\rvert^{2m}(1+\lvert\log\lvert g\rvert_G\rvert^2)^{-s/2}\,\mathrm{d}\mu_G(g)
$$

is finite. This is the case if and only if $s-2m>1$, which reads $m<\frac{s-1}{2}$. $\square$

PROPOSITION 9.1.2.6. *Let $G$ be an $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$. Let $\mu_G$ be a choice of Haar measure on $G$.*

## PDF page 403

**9.2. HARDY-SOBOLEV SPACES $W^s_I(G)$ AND PALEY-WIENER CONDITIONS** · **403**

Let $s > 1$ be a real number.

*Then every $f\in W^{s,2}(G)$ is absolutely $\mu_G$-integrable. There exists a real number $C_s > 0$ such that:*

$$
\|f\|_{L^1(G,\mu_G)}\le C_s\|f\|_{s,2}. \tag{9.1.2.17}
$$

*In particular, the linear inclusion $W^{s,2}(G)\to L^1(G,\mu_G)$ is continuous.*

Proof. We have:

$$
\int_G |f(g)|\,\mathrm{d}\mu_G(g) = \int_G |f(g)|\frac{(1+|\log|g|_G|^2)^{s/4}}{(1+|\log|g|_G|^2)^{s/4}}\,\mathrm{d}\mu_G(g)
$$

$$
\le \left(\int_G |f(g)|^2(1+|\log|g|_G|^2)^{s/2}\,\mathrm{d}\mu_G(g)\right)^{1/2}\left(\int_G\frac{1}{(1+|\log|g|_G|^2)^{s/2}}\,\mathrm{d}\mu_G(g)\right)^{1/2}
$$

$$
= \|(1+|\log|g|_G|^2)^{-s/2}\|^{1/2}_{L^1(G,\mu_G)}\left(\int_G |f(g)|^2(1+|\log|g|_G|^2)^{s/2}\,\mathrm{d}\mu_G(g)\right)^{1/2}
$$

and since $s > 1$, then $(1+|\log|g|_G|^2)^{-s/2}$ is absolutely $\mu_G$-integrable by Lemma 9.1.2.4. Upon calling $C_s := \|(1+|\log|g|_G|^2)^{-s/2}\|^{1/2}_{L^1(G,\mu_G)}$, we see that (9.1.2.17) holds, and hence the resulting linear inclusion $W^{s,2}(G)\to L^1(G,\mu_G)$ is continuous.

$\square$

**9.2. Hardy-Sobolev spaces $W^s_I(G)$ and Paley-Wiener conditions**

We recall from Appendix D.3.2, that for $G$ a Hausdorff locally compact abelian group, modulated by a proper surjective module homomorphism $|\cdot|_G\colon G\to\mathbf R_{>0}$ whose kernel we denote by $G^1$ (i.e. $\mathbf R_{>0}$-modulated; see §D.3.3) and for $I\subset\mathbf R$ a non-empty connected open interval equal to either $(0,+\infty)$ or $I = \mathbf R$, the Fourier-Mellin transform:

$$
M_I\colon \mathcal S_I(G)\to A\mathcal S(\mathbf C_I)\overline{\otimes}\mathcal S(\widehat{G^1}) \tag{9.2.0.1}
$$

from (D.3.2.2) is a linear topological isomorphism (recall that the Hausdorff locally convex topology on the Schwartz-Bergman space $A\mathcal S(\mathbf C_I)$ was defined as the topology of $L^p$-convergence on vertical lines within $\mathbf C_I$ for functions $\phi$ and $s^N\phi$ for all integers $N\ge 0$, for a, equivalently any, $p > 1$. In particular, the topology is independent of $p\ge 1$, similarly to the independence of $p\ge 1$ of the topology of $L^p$-convergence of functions $f\colon\mathbf R\to\mathbf C$ and $q_1(x)q_2(\partial_x)f$ for any polynomials $q_1,q_2\in\mathbf C[X]$, which is equivalent to the topology of the Schwartz space; see §D.1.10.1, and [KG, Part I,Thm.29,p.72]. We refer the reader to Definition D.3.1.3 and Lemma D.3.1.2).

We recall that $M_I$ was defined, upon describing each continuous quasi-character $c\in\Omega(G)$ as the corresponding unique pair $(s,\omega)$, once a choice of continuous section $\tau$ to the module $|\cdot|_G$ is fixed, for $s\in\mathbf C$ and $\omega\in\widehat{G^1}$:

$$
M_I(\phi)(s,\omega) := \int_{\mathbf R_{>0}} t^s\int_{G^1}\phi(\tau(t)g)\,\mathrm{d}\bar\mu_1(g)\,\frac{\mathrm{d}t}{t}
$$

where $\bar\mu_1$ and $\mathrm{d}t/t$ uniquely determine and are determined, as per Theorem D.1.2.1, by the canonical Haar measure $\mu_G$ on $G$. $M_I(\phi)(s,\omega)$ is holomorphic over $\mathbf C_I$ and Schwartz uniformly on every vertical strip of bounded width contained within $\mathbf C_I$ (see Proposition D.3.2.5).

It is identified with $\mathcal F_{G^1}\overline{\otimes} M_I$ where $\mathcal F_{G^1}$ is the Fourier transform $\mathcal S(G^1)\to\mathcal S(\widehat{G^1})$ and $M_I\colon\mathcal S_I(\mathbf R_{>0})\to A\mathcal S(\mathbf C_I)$ is the Fourier-Mellin transform in the special case $G = \mathbf R_{>0}$ (see Theorem D.3.3.13).

Remark 9.2.0.1. Recall that our choice of Haar measure $\bar\mu$ on $C_F$ is not the canonical measure (see Remark D.2.1.4 and [Weil-e, §3,p.6]), which requires the normalization giving $C^1_F$ volume 1. The canonical measure $\mu_{C_F}$ is $\bar\mu_1(C^1_F)^{-1}\,\bar\mu$.

We made this choice to remain consistent with [CF, Ch.XV,§2.3]. In particular, the operator $L$ from (5.1.1.1) and $M_{\mathbf R}$ on $C_F$ restricted to $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))$ are equal up to the constant multiplier $\bar\mu_1(C^1_F)$.

## PDF page 404

**404** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

Throughout this Chapter we will be mentioning the choice of normalization for the Haar measure on the $\mathbf R_{>0}$-modulated groups under consideration, explicitly.

We refer the reader to Proposition D.3.2.5.

**9.2.1. The special case $I = \{b\}$: $b$-line Hardy-Sobolev spaces and Paley-Wiener Theorem.** As a warmup, we will now be entering a brief interlude, discussing completions of both source and target of $M_I$ from (9.2.0.1) with respect to the Sobolev topologies discussed in Definition 9.1.1.1. We will be terming the corresponding completions of $A\mathcal S(\mathbf C_I)\overline{\otimes}\mathcal S(\widehat{G^1})$ and of its isotypes, Hardy-Sobolev spaces of $G$.

Definition 9.2.1.1 ($b$-line Hardy-Sobolev spaces). Let $b\in\mathbf R$ be a real number, $N\ge 1$ an integer. We define:

(1) The completion $W^{2N,2}_b(\mathbf R_{>0})$ of $\mathcal S_\mathrm{E}(\mathbf R_{>0})$ with respect to the finite family of continuous norms:

$$
\|\cdot\|_{b,k}\colon \mathcal S_\mathrm{E}(\mathbf R_{>0})\to\mathbf R_{\ge 0} \tag{9.2.1.1}
$$

for each $0\le k\le N-1$, defined by:

$$
\|\phi\|_{b,k} := \left(\int_{\mathbf R_{>0}} |\phi(t)\,(\log(t))^k|^2 t^{2b}\,\frac{\mathrm{d}t}{t}\right)^{1/2}. \tag{9.2.1.2}
$$

We refer to the Hilbert space $W^{2N,2}_b(\mathbf R_{>0})$ as the $b$-line Sobolev space of $\mathbf R_{>0}$.

(2) The completion $\mathrm{HS}^{2N,2}_b(\mathbf C)$ of the Schwartz-Bergman space $A\mathcal S(\mathbf C)$ with respect to the metrizable topology induced by the finite family of continuous norms $\{\|\cdot\|^{\mathrm{HS}}_{b,k},\,0\le k\le N\}$:

$$
\|\phi\|^{\mathrm{HS}}_{b,k} := \frac{1}{2\pi}\left(\int_{b-i\infty}^{b+i\infty} |\partial^k_s M(\phi)(s)|^2\,|\mathrm{d}s|\right)^{1/2}. \tag{9.2.1.3}
$$

We refer to the Hilbert space $\mathrm{HS}^{2N,2}_b(\mathbf C)$ as the $b$-line Hardy-Sobolev space.

In the next subsection, §9.2.2, we will rethink $\mathrm{HS}^{2N,2}_b(\mathbf C)$ as the special case of the Hardy-Sobolev space $\mathrm{HS}^{2N,2}_I(\mathbf C)$, to be defined therein, with base interval $I = \{b\}$, to be identified, under the Mellin transform, with the Hardy-Sobolev space $W^{2N,2}_I(\mathbf C)$, for $I = \{b\}$.

Theorem 9.2.1.2 (Paley-Wiener Theorem for Hardy-Sobolev Spaces - I). *Let $a\in\mathbf R$ be a real number, $a > 1$. We denote by $M$ the Mellin transform $M_I\colon\mathcal S_I(\mathbf R_{>0})\to A\mathcal S(\mathbf C_I)$ for $I := (-\infty,+\infty)$. We denote by:*

$$
\mathcal S_\mathrm{E}(\mathbf R_{>0},(1/a,+\infty))\subset\mathcal S_\mathrm{E}(\mathbf R_{>0}) \tag{9.2.1.4}
$$

*the linear subspace of those Schwartz-Bruhat functions on $\mathbf R_{>0}$ of exponential decay, whose support is contained within the interval $(1/a,+\infty)$.*

*Let, for $b\in\mathbf R$ a real number, and $N\ge 1$ an integer. Then:*

(1) *The closure of $\mathcal S_\mathrm{E}(\mathbf R_{>0},(1/a,+\infty))$ in the Sobolev space $W^{2N,2}_b(\mathbf R_{>0})$ is the closed subspace obtained as the closed range of the idempotent multiplication operator $M_{\rho_{a,+}}\colon W^{2N,2}_b(\mathbf R_{>0})\to W^{2N,2}_b(\mathbf R_{>0})$ obtained by multiplying by the indicator function $\rho_{a,+}(t) := \mathrm{1}_{[1/a,+\infty)}(t)$.*

(2) *The Mellin transform $M$ extends by continuity to a linear isometric isomorphism:*

$$
M\colon W^{2N,2}_b(\mathbf R_{>0})\to\mathrm{HS}^{2N,2}_b(\mathbf C) \tag{9.2.1.5}
$$

*where the target is the $b$-line Hardy-Sobolev space.*

## PDF page 405

**9.2. HARDY-SOBOLEV SPACES $W^s_I(G)$ AND PALEY-WIENER CONDITIONS** · **405**

(3) *The closure $\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty))$ of $M(\mathcal S_\mathrm{E}(\mathbf R_{>0},(1/a,+\infty)))$ in $\mathrm{HS}^2_b(\mathbf C)$ satisfies the following property: there exists a commutative diagram of continuous linear operators with linearly short exact rows:*

(9.2.1.6)

```latex
\begin{tikzcd}
0 \arrow[r] & M_{[1/a,1]}W^{2N,2}_b(\mathbf R_{>0}) \arrow[r] \arrow[d, "M"'] & M_{\rho_{a,+}}W^{2N,2}_b(\mathbf R_{>0}) \arrow[r] \arrow[d, "M"'] & M_{\rho_{1,+}}W^{2N,2}_b(\mathbf R_{>0}) \arrow[r] \arrow[d, "M"] & 0 \\
0 \arrow[r] & \mathrm{PW}^{2N,2}_b(\mathbf C,a) \arrow[r] & \mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty)) \arrow[r] & H^{2N,2}(\mathbf C_{<b}) \arrow[r] & 0
\end{tikzcd}
```

*where $M_{[1/a,1]}$ is the multiplication by $\mathrm{1}_{[1/a,1]}$ operator, the leftmost operators in (9.2.1.6) are continuous, with closed range, the rightmost are surjective and open, the vertical arrows are isometric isomorphisms induced by the Mellin transform, and where:*

(1) *$H^{2N,2}(\mathbf C_{<b})$ is the Hardy-Sobolev space of the left half-plane.*

(2) *$\mathrm{PW}^{2N,2}_b(\mathbf C,a)$ is the closed linear subspace of the Hardy-Sobolev space $H^{2N,2}(\mathbf C_{>b})$ of those holomorphic functions $\phi(s)$ over $\mathbf C_{>b}$ that extend to entire functions and satisfy:*

$$
\phi(s) = O\left(\frac{(1-a^{-2\,\mathrm{Re}(s)})^{1/2}}{(\mathrm{Re}(s))^{1/2}}\right). \tag{9.2.1.7}
$$

We refer to $\mathrm{PW}^{2N,2}_b(\mathbf C,a)$ as the $b$-line Paley-Wiener space of weight $a$.

Proof. (1) : The assertion follows from the following: $\mathcal S_\mathrm{E}(\mathbf R_{>0},(1/a,+\infty))$ is sequentially dense within the closed subspace $M_{\rho_{a,+}}W^{2N,2}_b(\mathbf R_{>0})\subset W^{2N,2}_b(\mathbf R_{>0})$. The Hausdorff locally convex topology induced on $\mathcal S_\mathrm{E}(\mathbf R_{>0})$ by the finitely many norms $\{\|\cdot\|_{b,k}\}_{0\le k\le N}$ is equivalent to the normed topology induced by the norm:

$$
\|\cdot\|_{2N,2}\colon \phi\mapsto \|\phi\|_{2N,2} := \left(\int_{\mathbf R_{>0}} |\phi(t)|^2 t^{2b}|1+|\log(t)|^2|^N\,\frac{\mathrm{d}t}{t}\right)^{1/2}
$$

the proof of the equivalence of the two topologies being seen by an argument analogous to that provided for Lemma 9.1.2.2.

We define

$$
\nu_{a,b,N} := \rho_{a,+}\cdot |\cdot|^{2b}_{\mathbf R}\,|1+|\log|\cdot|^2_{\mathbf R}|^N\,\frac{\mathrm{d}t}{t}
$$

a Radon measure on $\mathbf R_{>0}$. The closed subspace $M_{\rho_{a,+}}W^{2N,2}_b(\mathbf R_{>0})$ is isometric to the completion of the linear space of smooth compactly supported functions on $(1/a,+\infty)$ with respect to the $L^2(\mathbf R_{>0},\nu_{a,b,N})$-norm, which shows that $\mathcal S_\mathrm{E}(\mathbf R_{>0},(1/a,+\infty))$ is sequentially dense within $M_{\rho_{a,+}}W^{2N,2}_b(\mathbf R_{>0})$.

(2) : The assertion is a consequence of the formula:

$$
\int_{\mathbf R_{>0}} \phi(t)(\log(t))^k t^{b+ix}\,\frac{\mathrm{d}t}{t} = \partial^k_s M(\phi)(s)|_{b+ix} \tag{9.2.1.8}
$$

(see [Fol, Thm.8.22(d)]) and Plancherel's Theorem (see [DE, Thm.3.4.8] and [Fol, Thm.8.29]), noting that the Plancherel measure associated to $\mathrm{d}t/t$ is $\frac{1}{2\pi}\mathrm{d}x$ (which is seen upon changing the variable $x$ in the definition of the Fourier transform in [Fol, Ch.8,p.249] into $x/2\pi$ and using [Fol, Thm.8.29]).

(3) : Since $\rho_{a,+} = \rho_{1,+} + \mathrm{1}_{(1/a,1]}$, a sum of nonnegative real valued piece-wise continuous functions on $\mathbf R_{>0}$, each multiplication operator $M_\rho$ for $\rho\in\{\rho_{a,+},\rho_{1,+},\mathrm{1}_{(1/a,1]}\}$ is a positive idempotent operator, hence, by [Cnw-a, Ch.II,§3,Prop.3.3], an orthogonal projector. The topmost extension of $\mathbf C$-linear spaces is therefore exact and the leftmost horizontal arrow is an isometric isomorphism onto its image, with closed linearly and topologically complemented range. To prove (3) it is therefore sufficient to show that the Mellin transform induces linear isometric isomorphisms on all three vertical arrows. This is indeed the case for the rightmost vertical arrow, a consequence of Plancherel's Theorem (see [Fol, Thm.8.29]) and [Fol, Thm.8.22(d)], in light of the description of the normed topology on $H^{2N,2}(\mathbf C_{<b})$ as equivalent to the topology generated by the family of seminorms from (9.2.2.2).

## PDF page 406

**406** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

We now show that the Mellin transform

$$
M\colon M_{\rho_{a,+}}W^{2N,2}_b(\mathbf R_{>0})\to\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty))
$$

maps the closed subspace $M_{[1/a,1]}W^{2N,2}_b(\mathbf R_{>0})$ onto $\mathrm{PW}^{2N,2}_b(\mathbf C,a)$.

For any $f\in\mathcal S_\mathrm{E}(\mathbf R_{>0})$, the function $u_a := \mathrm{1}_{[1/a,1]}\cdot f$ is compactly supported and piece-wise smooth. Its support is contained within the interval $[1/a,1]\subset\mathbf R_{>0}$ and its set of singular points is contained in $\{1/a,1\}\subset\mathbf R_{>0}$.

Since the support of $u_a$ is contained within $(0,1]$, then the Fourier transform of $|\cdot|^b_{\mathbf R}u_a$ extends uniquely to an entire function $M(u_a)(b'+s)$ of $s\in\mathbf C$ that is an element of $H^{2N,2}(\mathbf C_{>0})$, equivalently $M(u_a)$ is an element of $H^{2N,2}(\mathbf C_{>b'})$, for any real number $b'$. In particular, for $b' = b$, we deduce that $M(u_a)$ is an element of $H^{2N,2}(\mathbf C_{>b})$. This choice of $b'$ ensures that the leftmost horizontal arrow in the bottom row of the diagram in (9.2.1.6) is defined and injective.

We have:

$$
|M(u_a)(s)| = \left|\int_{-\log(a)}^0 u_a(e^\xi)e^{s\xi}\,\mathrm{d}\xi\right| \tag{9.2.1.9}
$$

$$
\le \left(\int_{-\log(a)}^0 |u_a(\xi)|^2\,\mathrm{d}\xi\right)^{1/2}\left(\int_{-\log(a)}^0 |e^{s\xi}|^2\,\mathrm{d}\xi\right)^{1/2} \tag{9.2.1.10}
$$

$$
= \|u_a\|_{L^2(\mathbf R_{>0},\mathrm{d}t/t)}\frac{(1-a^{-2\,\mathrm{Re}(s)})^{1/2}}{(2\,\mathrm{Re}(s))^{1/2}}. \tag{9.2.1.11}
$$

This shows that $M$, restricted to $M_{[1/a,1]}W^{2N,2}_b(\mathbf R_{>0})$, is valued in $\mathrm{PW}^{2N,2}_b(\mathbf C,a)$.

Let $\phi\in\mathrm{PW}^{2N,2}_b(\mathbf C,a)$ be an arbitrary element. By [Dur, Ch.11,§11.2,Thm.11.4,p.192] applied to $\phi$ and its holomorphic derivatives of order $1\le k\le N$, the boundary value functions $\phi_b$ and $(\partial^k_s\phi)_b$ obtained by asymptotic restriction of $\phi(s)$ to the $b$-line (i.e. by formation of the limit $\lim_{\sigma\to 0^-}(\partial^k_s\phi)(\sigma+b+ix)$, which converges for $\mathrm{d}x$-almost all $x$ and each $0\le k\le N$), is an element of the Sobolev space $W^{2N,2}(\mathbf R)$ (using Fourier Inversion to show that indeed $(\partial^k_s\phi)_b$ represents the weak $k$th derivative of $\phi_b$, since it is the Fourier transform of $|t|^a_{\mathbf R}u(t)\,(\log(t))^k$ for $|\cdot|^b_{\mathbf R}u$ the Fourier anti-transform of $\phi_b$). It follows that the Mellin anti-transform $u$ of $\phi$ is an element of $W^{2N,2}_b(\mathbf R_{>0})$.

By the proof of [Dur, Ch.11,§11.5,Corollary,p.197], $|\cdot|^b_{\mathbf R}u$ is supported over $(0,1]$, and hence so is $u$.

The entire function $a^s\phi(s)$ is now an element of $H^{2N,2}(\mathbf C_{<b})$, and hence the Mellin anti-transform of $a^{-s}\phi(-s)$, i.e. $u(a/t)$ is such that $|\cdot|^b_{\mathbf R}u(a/t)$ is supported over $(0,1]$, by another application of the proof of [Dur, Ch.11,§11.5,Corollary,p.197], which implies that $u$ is supported over $[1/a,+\infty)$. This shows that $u\in M_{[1/a,1]}W^{2N,2}_b(\mathbf R_{>0})$, where $u$ is uniquely determined almost everywhere, and hence $M$ maps $M_{[1/a,1]}W^{2N,2}_b(\mathbf R_{>0})$ onto $\mathrm{PW}^{2N,2}_b(\mathbf C,a)$.

We further refer the reader to the argument in [Yos, Ch.VI,§4,Thm.2,p.164].

We have therefore proved that $M$ is surjective onto $\mathrm{PW}^{2N,2}_b(\mathbf C,a)$, and since $M$ is isometric, we deduce that $\mathrm{PW}^{2N,2}_b(\mathbf C,a)$ is closed in $\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty))$ (which is also a consequence of the Asymptotic Residue Theorem; see Theorem B.3.2.1) and that the bottom leftmost horizontal arrow in (9.2.1.6) is itself an isometric isomorphism onto its closed range.

$\square$

Corollary 9.2.1.3. *Let $a\in\mathbf R$ be a real number, $a > 1$. Let $b\in\mathbf R$ be a real number $N\ge 1$ an integer. We denote by $M$ the Mellin transform $M\colon W^{2N,2}_b(\mathbf R_{>0})\to\mathrm{HS}^{2N,2}_b(\mathbf C)$ provided by Theorem 9.2.1.2(2).*

*Let $\phi\in W^{2N,2}_b(\mathbf R_{>0})$ be the arbitrary element. Then $M(\phi)(s)$ is a holomorphic function on $\mathbf C_{<b}$, square-integrable on all vertical lines of $\mathbf C_{<b}$ with all of its holomorphic derivatives of order $0\le k\le N$.*

## PDF page 407

**9.2. HARDY-SOBOLEV SPACES $W^s_I(G)$ AND PALEY-WIENER CONDITIONS** · **407**

*There exist a holomorphic function $u_1\in H^{2N,2}(\mathbf C_{<b})$ and an entire function $u_2\in H^{2N,2}(\mathbf C_{>b})$, canonically associated to $M(\phi)$, such that:*

$$
u_2(s) = O\left(\frac{(1-a^{-2\,\mathrm{Re}(s)})^{1/2}}{(\mathrm{Re}(s))^{1/2}}\right) \tag{9.2.1.12}
$$

and:

$$
M(\phi) = u_1 + u_2 \tag{9.2.1.13}
$$

as holomorphic functions over $\mathbf C_{<b}$.

Proof. Every element $\phi\in M_{\rho_{a,+}}W^{2N,2}_b(\mathbf R_{>0})$ is, in particular, square-integrable with respect to the Radon measure on $\mathbf R_{>0}$ defined as $|\cdot|^{2b'}_{\mathbf R}\frac{\mathrm{d}t}{t}$ for every real number $b' < b$. By Plancherel's Theorem (see [DE, Thm.3.4.8] and [Fol, Thm.8.29]), this integrability condition reads:

$$
\int_{b'-i\infty}^{b'+i\infty} |M(\phi)(s)|^2|\mathrm{d}s| < +\infty.
$$

Following the proof of Theorem 9.2.1.2(2), we have, for each integer $0\le k\le N-1$:

$$
\int_{\mathbf R_{>0}} \phi(t)(\log(t))^k t^{b'+ix}\,\frac{\mathrm{d}t}{t} = \partial^k_s M(\phi)(s)|_{b'+ix} \tag{9.2.1.14}
$$

by see [Fol, Thm.8.22(d)] and another application of Plancherel's Theorem for all real numbers $b' < b$, and hence we have:

$$
\int_{\mathbf R_{>0}} |\phi(t)(\log(t))^k|t^{2b'}\,\frac{\mathrm{d}t}{t} = \int_{b'-i\infty}^{b'+i\infty} |\partial^k_s M(\phi)(s)|^2\,|\mathrm{d}s| \tag{9.2.1.15}
$$

which implies that $\partial^k_s\phi$ is also square-integrable on all vertical lines of $\mathbf C_{<b}$.

By Theorem 9.2.1.2(3), the functions $u_1 := M(\mathrm{1}_{[1,+\infty)}\cdot\phi)$ and $u_2 := M(\mathrm{1}_{[1/a,1]}\cdot\phi)$ satisfy the desired properties.

$\square$

Corollary 9.2.1.4. *Let $a,b\in\mathbf R$ be real numbers, $a > 1$. We denote by $M$ the Mellin transform $M_I\colon\mathcal S_I(\mathbf R_{>0})\to A\mathcal S(\mathbf C_I)$ for $I := (-\infty,+\infty)$.*

*For every point $z\in\mathbf C_{<b}$, the point-evaluation functional $\delta_z$ and its derivatives $\delta^{(m)}_z$ for $1\le m\le N-1$, are continuous on $\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty))$.*

For every $\phi\in M_{\rho_{a,+}}W^{2N,2}_b(\mathbf R_{>0})$, we have:

$$
\delta^{(m)}_z(M(\phi)(s)) = \int_{\mathbf R_{>0}} \phi(t)(\log(t))^m t^z\,\frac{\mathrm{d}t}{t} \tag{9.2.1.16}
$$

for each integer $0\le m\le N-1$.

Proof. Every point-evaluation functional on the elements of $\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty))$ supported at points $z\in\mathbf C_{<b}$ is bounded. Since the linear topology on $\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty))$ promotes the holomorphic derivative operators $\partial^k_s$ for $0\le k\le N-1$, to continuous linear endomorphisms, the functionals $\delta^{(m)}_z$ are all continuous on $\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty))$ for $0\le m\le N-1$. The formula in (9.2.1.16) is a consequence of Mellin Inversion.

$\square$

We can now incorporate the module-1 subgroup of a Hausdorff locally compact abelian $\mathbf R_{>0}$-modulated group into the assertions of Theorem 9.2.1.2 and Corollary 9.2.1.4.

Theorem 9.2.1.5 (Paley-Wiener Theorem for Hardy-Sobolev Spaces - II). *Let $a\in\mathbf R$ be a real number, $a > 1$. Let $G$ be an $\mathbf R_{>0}$-modulated Hausdorff locally compact abelian group. We denote by $M$ the Mellin transform $M\colon\mathcal S_\mathrm{E}(G)\to A\mathcal S(\mathbf C)\overline{\otimes}\mathcal S(\widehat{G^1})$.*

## PDF page 408

**408** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

We denote by:

$$
\mathcal S_\mathrm{E}(G,(1/a,+\infty))\subset\mathcal S_\mathrm{E}(G) \tag{9.2.1.17}
$$

*the linear subspace of those Schwartz-Bruhat functions on $G$ of exponential decay, whose support is sent by the module homomorphism $|\cdot|_G$ into the interval $(1/a,+\infty)\subset\mathbf R_{>0}$.*

*Let, for $b\in\mathbf R$ a real number, and $N\ge 0$ an integer:*

$$
\|\cdot\|_{b,k}\colon \mathcal S_\mathrm{E}(G)\to\mathbf R_{\ge 0} \tag{9.2.1.18}
$$

*be the continuous norm, for each $0\le k\le N$, defined by, upon choosing a continuous homomorphic section $\tau$ to the module $|\cdot|_G$:*

$$
\|\phi\|_{b,k} := \left(\int_{\mathbf R_{>0}} |\phi(\tau(t)g)\,(\log(t))^k|^2 t^{2b}\,\mathrm{d}\mu_1(g)\,\frac{\mathrm{d}t}{t}\right)^{1/2} \tag{9.2.1.19}
$$

*where $\mu_1$ is the unique volume-1 Haar measure on $G^1$.*

Then:

(1) *The closure of $\mathcal S_\mathrm{E}(G,(1/a,+\infty))$ in the completion $W^{2N,2}_b(G)$ of $\mathcal S_\mathrm{E}(G)$ with respect to the metrizable topology induced by the norms $\{\|\cdot\|_{b,k},\,0\le k\le N\}$ is the closed subspace obtained as the closed range of the idempotent multiplication operator $M_{\rho_{a,+}}\colon W^{2N,2}_b(G)\to W^{2N,2}_b(G)$ obtained by multiplying by the indicator function $\rho_{a,+}(g) := \mathrm{1}_{[1/a,+\infty)}(g)$, $g\in G$.*

(2) *The Mellin transform $M$ extends by continuity to the linear isometric isomorphism:*

$$
M\colon W^{2N,2}_b(G)\to L^2(G^1,\mu_1)\,\widehat{\otimes}_\sigma\mathrm{HS}^{2N,2}_b(\mathbf C) \tag{9.2.1.20}
$$

*where the target is the Hilbert-space tensor product obtained as the normed completion of the algebraic tensor product with respect to the Hilbert-space structure assigned by the inner product:*

$$
\langle u_1\otimes\phi_1,u_2\otimes\phi_2\rangle_\sigma := \langle u_1,u_2\rangle_{L^2(G^1,\mu_1)}\,\langle\phi_1,\phi_2\rangle_{\mathrm{HS}^{2N,2}_b(\mathbf C)} \tag{9.2.1.21}
$$

for $u_1,u_2\in L^2(G^1,\mu_1)$ and $\phi_1,\phi_2\in\mathrm{HS}^{2N,2}_b(\mathbf C)$.

(3) *The closure of $M(\mathcal S_\mathrm{E}(G,(1/a,+\infty)))$ in $L^2(G^1,\mu_1)\,\widehat{\otimes}_\sigma\mathrm{HS}^{2N,2}_b(\mathbf C)$ satisfies the following property. There exists a commutative diagram of continuous linear operators with linearly short exact rows:*

(9.2.1.22)

```latex
\begin{tikzcd}
0 \arrow[r] & M_{[1/a,1]}W^{2N,2}_b(G) \arrow[r] \arrow[d, "M"'] & M_{\rho_{a,+}}W^{2N,2}_b(G) \arrow[r] \arrow[d, "M"'] & M_{\rho_{1,+}}W^{2N,2}_b(G) \arrow[r] \arrow[d, "M"] & 0 \\
0 \arrow[r] & L^2(G^1,\mu_1)\,\widehat{\otimes}_\sigma\mathrm{PW}^{N,2}_b(\mathbf C,a) \arrow[r] & L^2(G^1,\mu_1)\,\widehat{\otimes}_\pi\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty)) \arrow[r] & L^2(G^1,\mu_1)\,\widehat{\otimes}_\sigma H^{N,2}(\mathbf C_{<b}) \arrow[r] & 0
\end{tikzcd}
```

*where $M_{[1/a,1]}$ is the multiplication by $\mathrm{1}_{[1/a,1]}$ operator, the leftmost operators in (9.2.1.22) are continuous, with closed range, the rightmost are surjective and open, the vertical arrows are isometric isomorphisms induced by the Mellin transform.*

Proof. We observe that for $\phi = u\otimes\phi_0$, with $u\in W^{2N,2}_b(\mathbf R_{>0})$ and $\phi_0\in L^2(G^1,\mu_1)$, then $|\phi|^2$ satisfies the assumptions of Theorem D.1.2.1, exhibiting $W^{2N,2}_b(G)$ as the completion of $\mathcal S_\mathrm{E}(G,(1/a,+\infty))\simeq\mathcal S(G^1)\,\widehat{\otimes}_\pi\mathcal S_\mathrm{E}(\mathbf R_{>0},(1/a,+\infty))$ with respect to the tensor topology induced by the norm uniquely determined by the inner product in (9.2.2.46), since such norm restricts on elementary tensors, by Theorem D.1.2.1, to the norm $\|\cdot\|_{b,k}$.

The Theorem is then a consequence of Theorem 9.2.1.2.

$\square$

The following Corollary follows from Theorem 9.2.1.5 and Corollary 9.2.1.3.

Corollary 9.2.1.6. *Let $a\in\mathbf R$ be a real number, $a > 1$. Let $b\in\mathbf R$ be a real number $N\ge 1$ an integer.*

## PDF page 409

**9.2. HARDY-SOBOLEV SPACES $W^s_I(G)$ AND PALEY-WIENER CONDITIONS** · **409**

*We denote by $M$ the Mellin transform $M\colon W^{2N,2}_b(G)\to L^2(G^1,\mu_1)\,\widehat{\otimes}_\sigma\mathrm{HS}^{2N,2}_b(\mathbf C)$ provided by Theorem 9.2.1.5(2).*

*Let $\phi\in W^{2N,2}_b(G)$ be the arbitrary element. Then for each $\omega\in\widehat{G^1}$, the function $M(\phi)(s,\omega)$ is a holomorphic function on $\mathbf C_{<b}$, square-integrable on all vertical lines of $\mathbf C_{<b}$ with all of its holomorphic derivatives of order $0\le k\le N-1$.*

*There exist a holomorphic function $u_1\in H^{2N,2}(\mathbf C_{<b})$ and an entire function $u_2\in H^{2N,2}(\mathbf C_{>b})$, canonically associated to $M(\phi,\omega)$, such that:*

$$
u_2(s) = O\left(\frac{(1-a^{-2\,\mathrm{Re}(s)})^{1/2}}{(\mathrm{Re}(s))^{1/2}}\right) \tag{9.2.1.23}
$$

and:

$$
M(\phi) = u_1 + u_2 \tag{9.2.1.24}
$$

as holomorphic functions over $\mathbf C_{<b}$.

The following is an analog of Corollary 9.2.1.4.

Corollary 9.2.1.7. *Let $G$ be a Hausdorff locally compact $\mathbf R_{>0}$-modulated group. Let $a,b\in\mathbf R$ be real numbers, $a > 1$. We denote by $M$ the Mellin transform $M\colon\mathcal S_\mathrm{E}(G)\to A\mathcal S(\mathbf C)\overline{\otimes}\mathcal S(\widehat{G^1})$.*

*For every point $z\in\mathbf C_{<b}$ and every continuous character $\omega\in\widehat{G^1}$, equivalently every point $c\in\Omega(G)_{<b}$ of the Riemann surface of continuous quasi-characters of $G$, the point-evaluation functional $\delta_{(z,\omega)}$ and its derivatives $\delta^{(m)}_{(z,\omega)}$ for $1\le m\le N-1$, induce continuous functionals on $L^2(G^1,\mu_1)\,\widehat{\otimes}_\sigma\mathrm{HS}^{2N,2}_b(\mathbf C,(1/a,+\infty))$ uniquely determined by the following formula: for every $\phi\in M_{\rho_{a,+}}W^{2N,2}_b(G)$, we have, for a, equivalently any, choice of continuous homomorphic section $\tau$ to the module $|\cdot|_G$:*

$$
\delta^{(m)}_{(z,\omega)}(M(\phi)(s,\omega)) = \int_{\mathbf R_{>0}}\int_{G^1}\omega(g)\phi(\tau(t)g)(\log(t))^m t^z\,\mathrm{d}\mu_1(g)\,\frac{\mathrm{d}t}{t} \tag{9.2.1.25}
$$

for each integer $0\le m\le N-1$.

Proof. This is a consequence of Theorem 9.2.1.5 and Corollary 9.2.1.4.

$\square$

9.2.1.1. *Duality.* We now provide a description of the continuous dual of $W^s_I(G)$ for $G$ a second-countable $\mathbf R_{>0}$-modulated group, $I\subset\mathbf R$ a closed non-empty interval, $s\ge 0$ a real number. We discuss here below the special case $G = \mathbf R_{>0}$.

Proposition 9.2.1.8 (Hardy-Sobolev duality - I). *Let $I\subset\mathbf R$ be a closed non-empty interval, $s\ge 0$ a real number. Assume $I$ is compact, of the form $I = [a,b]$, for $a < b$ real numbers.*

*For every open interval $J\subset\mathbf R$ containing $I$, the pairing:*

$$
\langle\cdot,\cdot\rangle_{I,s}\colon \mathcal S_J(\mathbf R_{>0})\times\mathcal S_J(\mathbf R_{>0})\to\mathbf C \tag{9.2.1.26}
$$

defined by the assignment:

$$
\langle\phi,\psi\rangle_{I,s} := \int_{\mathbf R_{>0}} \phi(t)\psi(t)\,\frac{\mathrm{d}t}{t} \tag{9.2.1.27}
$$

*is continuous and it extends to a continuous duality pairing:*

$$
\langle\cdot,\cdot\rangle_{I,s}\colon W^s_I(\mathbf R_{>0})\times W^{-s}_I(\mathbf R_{>0})\to\mathbf C \tag{9.2.1.28}
$$

*where $W^{-s}_I(\mathbf R_{>0})$ is the completion of $\mathcal S_J(\mathbf R_{>0})$ with respect to the norm:*

$$
\phi\mapsto \|\phi\|_{I,-s} := \left(\int_{\mathbf R_{>0}} |\phi(t)|^2\,w_{I,s}(t)^{-1}\,\frac{\mathrm{d}t}{t}\right)^{1/2} \tag{9.2.1.29}
$$

## PDF page 410

**410** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

with $w_{I,s}(t)$ the function:

$$
w_{I,s}(t) := \max\{t^{2a},t^{2b}\}\,(1+|\log(t)|^2)^{s/2}. \tag{9.2.1.30}
$$

*In particular, the induced linear map:*

$$
T_{I,s}\colon W^s_I(\mathbf R_{>0})'_\beta\to W^{-s}_I(\mathbf R_{>0}) \tag{9.2.1.31}
$$

determined by (9.2.1.28), given explicitly by $T\mapsto w^{-1}_{I,s}\cdot T$.

Proof. By [Fol, Thm.6.15], the pairing:

$$
\langle\cdot,\cdot\rangle\colon L^2(\mathbf R_{>0},\mu_{I,s})\times L^2(\mathbf R_{>0},\mu_{I,s})\to\mathbf C
$$

defined by:

$$
\langle\phi,\psi\rangle := \int_{\mathbf R_{>0}} \phi(t)\psi(t)\,\frac{\mathrm{d}t}{t} \tag{9.2.1.32}
$$

upon choosing the measure space $(X,\mathcal M,\mu)$ to be $X := \mathbf R_{>0}$, $\mathcal M$ the Borel $\sigma$-algebra, and $\mu_s := w_{I,s}\frac{\mathrm{d}t}{t}$, with $p = q = 2$, is separately continuous and induces an isometry between $L^2(\mathbf R_{>0},w_{I,s}\mathrm{d}t/t)'_\beta$ equipped with the dual norm (defined in [Fol, Prop.6.13]) and $L^2(\mathbf R_{>0},w_{I,s}\mathrm{d}t/t)$ itself, which is $W^s_I(\mathbf R_{>0})$.

We write $\mu_{-s} := w^{-1}_{I,s}\frac{\mathrm{d}t}{t}$.

For every $\phi\in L^2(\mathbf R_{>0},\mu_s)$ and $\psi\in L^2(\mathbf R_{>0},\mu_{-s})$, the integral:

$$
\int_{\mathbf R_{>0}} |\phi(t)\psi(t)|\,\frac{\mathrm{d}t}{t} \tag{9.2.1.33}
$$

converges, i.e. $\phi\cdot\psi$, as a complex-valued measurable function on $\mathbf R_{>0}$, is absolutely integrable. Indeed, we have:

$$
\int_{\mathbf R_{>0}} |\phi(t)\psi(t)|\,\frac{\mathrm{d}t}{t} = \int_{\mathbf R_{>0}} |\phi(t)\psi(t)|\frac{w_{I,s}(t)^{1/2}}{w_{I,s}(t)^{1/2}}\,\frac{\mathrm{d}t}{t} \le \|\phi\|^{1/2}_{L^2(\mathbf R_{>0},\mu_s)}\,\|\psi\|^{1/2}_{L^2(\mathbf R_{>0},\mu_{-s})}. \tag{9.2.1.34}
$$

We define $\langle\phi,\psi\rangle_{I,s}$ to be the value of the integral $\int_{\mathbf R_{>0}}\phi(t)\psi(t)\,\frac{\mathrm{d}t}{t}$. The notation is justified since the restriction of $\langle\cdot,\cdot\rangle_{I,s}$ to $\mathcal S_J(\mathbf R_{>0})\times\mathcal S_J(\mathbf R_{>0})$ is the pairing defined in (9.2.1.27).

We have, for all such $\phi,\psi\in L^2(\mathbf R_{>0},\mu_s)$:

$$
\langle\phi w^{-1}_{I,s},\psi\rangle = \langle\phi,\psi w^{-1}_{I,s}\rangle = \langle\phi,\psi\rangle_{I,s} \tag{9.2.1.35}
$$

where the products $\phi w^{-1}_{I,s}$, respectively $\psi w^{-1}_{I,s}$, are as complex-valued measurable functions on $\mathbf R_{>0}$.

The pairing $\langle\cdot,\cdot\rangle_{I,s}$ is sequentially continuous with respect to each argument, hence indeed separately sequentially continuous with respect to the normed topology defined by $\|\cdot\|_{I,s}$ in each argument. Sequential continuity of linear functionals implies continuity, the topology on $W^s_I(\mathbf R_{>0})$ being metric.

Since $W^s_I(\mathbf R_{>0})$ is a Banach space, being a Hilbert space by Lemma 9.2.2.2, hence so is its strong dual, normed with the dual norm, and by the Uniform Boundedness Theorem the pairing $\langle\cdot,\cdot\rangle_{I,s}$ is continuous, being separately continuous (see [Bou-TVS, Ch.IV,§4.6,IV.26,Thm.2]). The same conclusion also follows from Proposition C.2.3.11.

The linear endomorphism $\mathcal S_\mathrm{E}(\mathbf R_{>0})\to\mathcal S_\mathrm{E}(\mathbf R_{>0})$ (i.e. we choose $J = \mathbf R$ for the rest of the argument) sending $\psi$ to $w^{-1}_{I,s}\psi$ therefore extends to a continuous linear operator $W^s_I(\mathbf R_{>0})'_\beta\to W^{-s}_I(\mathbf R_{>0})$.

Indeed, for continuous functional $T\in W^s_I(\mathbf R_{>0})'_\beta$, by [Fol, Prop.6.13] there exists a unique $\psi\in W^s_I(\mathbf R_{>0})$ such that $T = T_\psi$, with $T_\psi$ the functional defined as:

$$
T_\psi\colon\phi\mapsto T_\psi(\phi) := \langle\phi,\psi\rangle.
$$



The functional on $W^s_I(\mathbf R_{>0})$:

$$
w^{-1}_{I,s}\,T
$$

## PDF page 411

**9.2. HARDY-SOBOLEV SPACES $W^s_I(G)$ AND PALEY-WIENER CONDITIONS** · **411**

assigned by:

$$
w^{-1}_{I,s} T(\phi) := \langle w^{-1}_{I,s} \phi, \psi \rangle
$$

is continuous on $W^{-s}_I(\mathbf{R}_{>0})$, and hence there exists a unique $\psi_0 \in W^{-s}_I(\mathbf{R}_{>0})$ representing it. The continuous linear operator $W^s_I(\mathbf{R}_{>0})'_\beta \to W^{-s}_I(\mathbf{R}_{>0})$ induced by $\langle \cdot, \cdot \rangle_{I,s}$ sends $T = T_\psi$ to $\psi_0$. We have $\psi_0 = w_{I,s}\,\psi$, and we compute:

$$
\|\psi_0\|_{W^{-s}_I(\mathbf{R}_{>0})} = \|\psi\|_{I,s} = \|T\|_{W^s_I(\mathbf{R}_{>0})'_\beta} \tag{9.2.1.36}
$$

the last equality being provided by [Fol, Prop.6.13].

The identities in (9.2.1.36) imply that the continuous linear operator from (9.2.1.31) is an isometry, hence injective.

It is bijective on $C_c(\mathbf{R}_{>0})$ being $w^{-1}_{I,s}$ continuous and nowhere vanishing, with continuous and nowhere vanishing reciprocal. It follows that it has dense range, and it is therefore surjective, being its range closed (as is the range of any linear topological embedding of a complete Hausdorff locally convex topological vector space into another). It is therefore an isometric isomorphism. $\square$

**9.2.2. General base intervals: the Hardy-Sobolev spaces $W^s_I(G)$.** We briefly recall here the definition of the Hardy-Sobolev space $H^{2N,2}(\mathbf{C}_{<b})$, for $b \in \mathbf{R}$ a real number, and $N \ge 1$ an integer. This is the $\mathbf{C}$-linear space of holomorphic functions on the half-plane $\mathbf{C}_{<b}$ that are square-integrable with their holomorphic derivatives of order $0 \le k \le N$ on each vertical line of $\mathbf{C}_{<b}$ and such that the resulting $L^2$-norms are bounded uniformly with respect to the abscissa $\sigma < b$, topologized with the metrizable topology generated by the finitely many norms:

$$
\|\cdot\|_{\mathrm{HS},2N,k} : \phi \mapsto \sup_{\sigma < b} \left( \int_{\sigma - i\infty}^{\sigma + i\infty} |\partial^k_s \phi(s)|^2\,|\mathrm{d}s| \right)^{1/2} \tag{9.2.2.1}
$$

for $0 \le k \le N$. We refer to $H^{2N,2}(\mathbf{C}_{<b})$ topologized with this seminormed topology, as the Hardy-Sobolev space of degree $2N$. It is a complex Hilbert space (since the finitely many norms can be reassembled into a single norm inducing a Hilbert space structure on $H^{2N,2}(\mathbf{C}_{<b})$).

We note that the norms, for each $0 \le k \le N$ and as $\sigma$ varies over the real numbers $\sigma < b$:

$$
\|\cdot\|_{\mathrm{HS},2N,k,\sigma} : \phi \mapsto \left( \int_{\sigma - i\infty}^{\sigma + i\infty} |\partial^k_s \phi(s)|^2\,|\mathrm{d}s| \right)^{1/2} \tag{9.2.2.2}
$$

are all continuous on $H^{2N,2}(\mathbf{C}_{<b})$, and hence their collection as $\sigma$ varies over the real numbers $\sigma < b$ induces a Hausdorff locally convex topology on $H^{2N,2}(\mathbf{C}_{<b})$ that is coarser than the topology induced by the finitely many norms from (9.2.2.1).

By [Dur, Ch.11,Cor.2,p.191] and [Dur, Ch.11,§11.4,Thm.11.8,p.195], the Asymptotic Cauchy Integral Formula (see Theorem B.2.2.4) applies, and it implies that $H^{2N,2}(\mathbf{C}_{<b})$ topologized with this coarser topology, is complete, and that a countable subfamily of the seminorms from (9.2.2.2) indexed by a countable subset of $\sigma < b$ such that $b$ is an accumulation point, generates an equivalent Hausdorff locally convex topology, which therefore exhibits $H^{2N,2}(\mathbf{C}_{<b})$, re-topologized in this manner, as a Fréchet space (this can also be seen using [Dur, Ch.11,§11.2,Thm.11.5,p.192]).

The identity map on $H^{2N,2}(\mathbf{C}_{<b})$ with the Hardy-Sobolev topology on the source, and the coarser Fréchet topology defined above on the target, is therefore open by [NB, Thm.14.4.5(b)], and hence a linear topological isomorphism.

We will therefore describe the topology on the Hardy-Sobolev space $H^{2N,2}(\mathbf{C}_{<b})$ by either the finite collection of norms from (9.2.2.1), or by the topology of $L^2$-convergence of holomorphic functions and their $k$th holomorphic derivatives for all $0 \le k \le N$, on all vertical lines strictly contained in $\mathbf{C}_{<b}$ (equivalently on a countable collection of vertical lines strictly contained in $\mathbf{C}_{<b}$ whose abscissas are a countable subset of

## PDF page 412

**412** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

$(-\infty,b)$ with $b$ as an accumulation point). We further refer the reader to Lemma D.3.1.2 and its proof, for a similar equivalence of Hausdorff locally convex topologies, resting upon the Asymptotic Cauchy Integral Formula from Theorem B.2.2.4).

Similar assertions hold on the topology of $H^{2N,2}(\mathbf{C}_{>b})$ and are obtained from the foregoing upon acting on the complex $s$-plane using the bi-holomorphic involution $s \mapsto -s$ (and applying the result to $-b$).

9.2.2.1. *The Hardy-Sobolev spaces $W^s_I(\mathbf{R}_{>0})$.* We will now be revisiting the Hardy-Sobolev spaces $H^{2N,2}(\mathbf{C}_{>b})$ and $H^{2N,2}(\mathbf{C}_{<b})$, allowing general real numbers $s \ge 0$ in place of the even integer degree $2N$, and allowing arbitrary vertical strips of base interval $I$, as opposed to the half-planes $\mathbf{C}_{>b}$ and $\mathbf{C}_{<b}$.

DEFINITION 9.2.2.1 (Sobolev $W^s_I$-spaces of $\mathbf{R}_{>0}$). Let $I \subset \mathbf{R}$ be a non-empty closed interval, $s \ge 0$ a real number.

We define on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ the following norm:

$$
\|\cdot\|_{I,s} : \phi \mapsto \sup_{a \le b : [a,b] \subset I} \left( \int_{\mathbf{R}_{>0}} |\phi(t)|^2 \max\{t^{2a}, t^{2b}\} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \right)^{1/2} \tag{9.2.2.3}
$$

and denote by $W^s_I(\mathbf{R}_{>0})$ the completion of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ with respect to the norm $\|\cdot\|_{I,s}$. We refer to $W^s_I(\mathbf{R}_{>0})$ as the Sobolev $W^s_I$-space of $\mathbf{R}_{>0}$, and to the norm $\|\cdot\|_{I,s}$ as the Sobolev $W^s_I$-norm.

We check the following basic properties of the Sobolev $W^s_I$-norms:

LEMMA 9.2.2.2 (Sobolev $W^s_I$-norms - I). *Let $I \subset \mathbf{R}$ be a closed interval, $s \ge 0$ a real number. Then:*

(1) *The Sobolev $W^s_I$-norm on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ is continuous on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ and it extends by continuity to $\mathcal{S}_J(\mathbf{R}_{>0})$ for any non-empty open interval $J \subset \mathbf{R}_{>0}$ containing $I$. The completion $W^s_I(\mathbf{R}_{>0})$ of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ equals the completion of $\mathcal{S}_J(\mathbf{R}_{>0})$.*

(2) *If $I$ is compact of the form $I = [a,b]$, for $a \le b$ real numbers, then for any $\phi \in \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ we have:*

$$
\|\phi\|_{I,s} = \left( \int_{\mathbf{R}_{>0}} |\phi(t)|^2 \max\{t^{2a}, t^{2b}\} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \right)^{1/2}. \tag{9.2.2.4}
$$

*If $s$ is an even integer, then the topology on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ generated by $\|\phi\|_{I,s}$ is equivalent to the metrizable topology generated by the finitely many continuous seminorms:*

$$
\|\phi\|_{M,\sigma,k} := \left( \int_{\sigma - i\infty}^{\sigma + i\infty} |\partial^k_z M(\phi)(z)|^2\,|\mathrm{d}z| \right)^{1/2}, \quad \sigma \in \{a,b\},\ 0 \le k \le \left[\frac{s}{2}\right]. \tag{9.2.2.5}
$$

(3) *Let $a,b \in \mathbf{R}$ be real numbers. If $I$ is of the form:*

(a) $I = [a,+\infty)$, then we have, for any $\phi \in \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$:

$$
\|\phi\|_{I,s} = \sup_{\sigma \ge a} \left( \int_{\mathbf{R}_{>0}} |\phi(t)|^2 \max\{t^{2a}, t^{2\sigma}\} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \right)^{1/2}. \tag{9.2.2.6}
$$

*If $s$ is an even integer, then for any sequence $\{c_k\}_{k \ge 0} \subset [a,+\infty)$ such that $\limsup_{k \ge 0} c_k = +\infty$ and $c_0 = a$, the topology on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ generated by $\|\phi\|_{I,s}$ is equivalent to the metrizable topology generated by the countable family of continuous seminorms:*

$$
\|\phi\|_{M,\sigma,k} := \left( \int_{\sigma - i\infty}^{\sigma + i\infty} |\partial^k_z M(\phi)(z)|^2\,|\mathrm{d}z| \right)^{1/2}, \quad \sigma \in \{c_k, k \ge 0\},\ 0 \le k \le \left[\frac{s}{2}\right] \tag{9.2.2.7}
$$

(b) $I = (-\infty,b]$, then we have, for any $\phi \in \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$:

$$
\|\phi\|_{I,s} = \sup_{\sigma \le b} \left( \int_{\mathbf{R}_{>0}} |\phi(t)|^2 \max\{t^{2\sigma}, t^{2b}\} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \right)^{1/2} \tag{9.2.2.8}
$$

## PDF page 413

**9.2. HARDY-SOBOLEV SPACES $W^s_I(G)$ AND PALEY-WIENER CONDITIONS** · **413**

*If $s$ is an even integer, then for any sequence $\{c_k\}_{k \ge 0} \subset (-\infty,b]$ such that $\liminf_{k \ge 0} c_k = -\infty$ and $c_0 = b$, the topology on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ generated by $\|\phi\|_{I,s}$ is equivalent to the metrizable topology generated by the countable family of continuous seminorms:*

$$
\|\phi\|_{M,\sigma,k} := \left( \int_{\sigma - i\infty}^{\sigma + i\infty} |\partial^k_z M(\phi)(z)|^2\,|\mathrm{d}z| \right)^{1/2}, \quad \sigma \in \{c_k, k \ge 0\},\ 0 \le k \le \left[\frac{s}{2}\right]. \tag{9.2.2.9}
$$

PROOF. We have, for any $a,b \in \mathbf{R}$ such that $a < b$:

$$
\left( \int_{\mathbf{R}_{>0}} |\phi(t)|^2 \max\{t^{2a}, t^{2b}\} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \right)^{1/2} \le \left( \int_{[1,+\infty)} |\phi(t)|^2 t^{\max\{2a,2b\}} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \right)^{1/2} \tag{9.2.2.10}
$$

$$
+ \left( \int_{(0,1)} |\phi(t)|^2 t^{\min\{2a,2b\}} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \right)^{1/2} \tag{9.2.2.11}
$$

for all $\phi \in \mathcal{S}_{[a,b]}(\mathbf{R}_{>0})$.

(1) : The inequality in (9.2.2.10) implies continuity of $\|\cdot\|_{I,s}$ on $\mathcal{S}_J(\mathbf{R}_{>0})$ by Monotone Convergence, for any nonempty open interval $J$ containing $I$. Since $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ is dense in $\mathcal{S}_J(\mathbf{R}_{>0})$ for any such $J$, the respective completions with respect to the normed topology induced by the norm $\|\cdot\|_{I,s}$ on each are isometric.

(2) : We note that we have, for any $\phi \in \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$:

$$
\int_{\mathbf{R}_{>0}} |\phi(t)|^2 \max\{t^{2a}, t^{2b}\} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} = \int_{[1,+\infty)} |\phi(t)| t^{\max\{2a,2b\}} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \tag{9.2.2.12}
$$

$$
+ \int_{(0,1)} |\phi(t)| t^{\min\{2a,2b\}} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t}. \tag{9.2.2.13}
$$

For any two real numbers $a',b' \in \mathbf{R}$ satisfying $a < a' < b' < b$, we note that we have the inequalities:

$$
\mathrm{1}_{[1,+\infty)}(t) \max\{t^{2a'}, t^{2b'}\} \le \mathrm{1}_{[1,+\infty)}(t) \max\{t^{2a}, t^{2b}\} \tag{9.2.2.14}
$$

and:

$$
\mathrm{1}_{(0,1)}(t) \max\{t^{2a'}, t^{2b'}\} = \mathrm{1}_{(0,1)}(t)\, t^{\min\{2a',2b'\}} = \mathrm{1}_{(0,1)}(t)\, t^{2a'} \le \mathrm{1}_{(0,1)}(t)\, t^{2a} = \mathrm{1}_{(0,1)}(t) \max\{t^{2a}, t^{2b}\}. \tag{9.2.2.15}
$$

The inequalities in (9.2.2.14) and (9.2.2.15) hold for all $t \in \mathbf{R}_{>0}$ and give the inequality:

$$
\max\{t^{2a'}, t^{2b'}\} \le \max\{t^{2a}, t^{2b}\} \tag{9.2.2.16}
$$

which in turn implies that (9.2.2.4) holds.

By Plancherel's Theorem, combined with [Fol, Thm.8.22(d)], we have:

$$
\|\phi\|_{M,\sigma,k} = \left( \int_{\mathbf{R}_{>0}} |\phi(t)|^2 t^{2\sigma} |\log(t)|^{2k} \frac{\mathrm{d}t}{t} \right)^{1/2}. \tag{9.2.2.17}
$$

By Lemma 9.1.2.2, the metrizable topology generated on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ by the finite collection of continuous seminorms $\|\cdot\|_{M,\sigma,k}$, for $\sigma \in \{a,b\}$ and $0 \le k \le [s/2]$, is equivalent to the metrizable topology generated by the two continuous seminorms:

$$
\phi \mapsto \left( \int_{\mathbf{R}_{>0}} |\phi(t)|^2 t^{2\sigma} (1 + |\log(t)|^2)^{s/2} \frac{\mathrm{d}t}{t} \right)^{1/2}, \quad \sigma \in \{a,b\}. \tag{9.2.2.18}
$$

It follows that such topology is at least as coarse as the topology generated on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ by $\|\cdot\|_{I,s}$. By the estimates in (9.2.2.16), the two topologies are equivalent for $I$ compact.

Both parts of (3) follow from an argument similar to the argument provided for (2). $\square$

## PDF page 414

**414** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

In analogy with Definition 9.2.2.1 and building on Lemma 9.2.2.2, we introduce the following:

DEFINITION 9.2.2.3 (Absolute Hardy-Sobolev space of degree $s$ and base $I$). Let $I \subset \mathbf{R}$ be a non-empty closed interval, $s \ge 0$ a real number. We define on $A\mathcal{S}(\mathbf{C})$ the following continuous norms:

$$
u \mapsto \frac{1}{2\pi} \left( \int_{\sigma - i\infty}^{\sigma + i\infty} |\partial^k_z u(z)|^2\,|\mathrm{d}z| \right)^{1/2} \tag{9.2.2.19}
$$

as $\sigma$ varies over a sequence $\{c_k\}_{k \ge 0} \subset \mathbf{R}$ such that the boundary of $I$ is a set of accumulation points for $\{c_k\}_{k \ge 0}$. We denote by $\mathrm{HS}^s(\mathbf{C}_I)$ the completion of $A\mathcal{S}(\mathbf{C})$ with respect to the metrizable topology generated by the countable family of continuous norms from (9.2.2.19) as $\sigma$ varies over $\{c_k\}_{k \ge 0}$. We refer to $\mathrm{HS}^s(\mathbf{C}_I)$ as the absolute Hardy-Sobolev space of degree $s$ and base $I$.

PROPOSITION 9.2.2.4 (Fourier-Mellin transform on $W^s_I(\mathbf{R}_{>0})$). Let $s \ge 0$ be a real number. Then:

(1) *The topology on $A\mathcal{S}(\mathbf{C})$ generated by the countable family of continuous norms from (9.2.2.19) as $\sigma$ varies over $\{c_k\}_{k \ge 0}$ does not depend on the choice of $\{c_k\}_{k \ge 0}$ and it is Hilbertizable.*

(2) *$\mathrm{HS}^s(\mathbf{C}_I) \subset \mathscr{O}(\mathbf{C}_{\mathrm{Int}(I)})$, and for every $u \in \mathrm{HS}^s(\mathbf{C}_I)$ and every $b \in \partial I$ finite, the limit:*

$$
u_b(\tau) := \lim_{\sigma \to b, \sigma \in \mathrm{Int}(I)} u(\sigma + i\tau) \tag{9.2.2.20}
$$

*exists for almost all $\tau \in \mathbf{R}$ and it is an element of $W^{s,2}(\mathbf{R})$. If $s$ is an even integer, then $u_b$ is an element of $\mathrm{HS}^{s,2}_b(\mathbf{C})$, the $b$-line Hardy-Sobolev space.*

(3) *Assume $s$ is an even integer. Then, for any non-empty open interval $J$ containing $I$, the Mellin transform:*

$$
M : \mathcal{S}_J(\mathbf{R}_{>0}) \to A(\mathbf{C}_J) \tag{9.2.2.21}
$$

*from (D.3.2.2) extends by continuity to a linear topological isomorphism:*

$$
M : W^s_I(\mathbf{R}_{>0}) \to \mathrm{HS}^s(\mathbf{C}_I). \tag{9.2.2.22}
$$

PROOF. Proposition 9.2.2.4 follows from Lemma 9.2.2.2 in the case $I$ is a compact connected interval, and the general case reduces to this special case using Lemma 9.2.2.2 again and the Asymptotic Cauchy Integral Formula (see Theorem B.2.2.4).$^1$ $\square$

COROLLARY 9.2.2.5 (Continuous point-evaluation functionals on Hardy-Sobolev spaces). *Let $I \subset \mathbf{R}$ be a non-empty closed interval, $s \ge 0$ a real number. Let $z_0 \in \mathbf{C}_I$. Then:*

(1) *if $z_0 \in \mathbf{C}_{\mathrm{Int}(I)}$, then for any integer $k \ge 0$, the functional:*

$$
u \mapsto (\partial^k_z u)(z_0) \tag{9.2.2.23}
$$

is continuous.

(2) If $\mathrm{Re}(z_0) \in \partial I$, then the functional:

$$
u \mapsto (\partial^k_z u)(z_0) \tag{9.2.2.24}
$$

*is continuous if and only if the integer $k \ge 0$ satisfies: for every integer*

$$
0 \le k \le \left[\frac{s-1}{2}\right].
$$

PROOF. The proof of Corollary 9.2.2.5 mirrors the argument for Corollary 9.2.1.4, using Proposition 9.2.2.4.$^2$ $\square$

---
$^1$Return here.

$^2$Return here.

## PDF page 415

**9.2. HARDY-SOBOLEV SPACES $W^s_I(G)$ AND PALEY-WIENER CONDITIONS** · **415**

THEOREM 9.2.2.6 (Paley-Wiener Theorem for Hardy-Sobolev Spaces - III). *Let $I \subset \mathbf{R}$ be a non-empty closed interval, $s \ge 0$ an even integer. Let $J \subset \mathbf{R}$ be any non-empty open interval containing $I$. We denote by $M$ the Mellin transform $M : \mathcal{S}_J(\mathbf{R}_{>0}) \to A\mathcal{S}(\mathbf{C}_J)$.*

We denote by:

$$
\mathcal{S}_J(\mathbf{R}_{>0}, (1/a,+\infty)) \subset \mathcal{S}_J(\mathbf{R}_{>0}) \tag{9.2.2.25}
$$

*the linear subspace of those Schwartz-Bruhat functions on $\mathbf{R}_{>0}$ of $J$-exponential decay, whose support is contained within the interval $(1/a,+\infty)$.*

Then:

(1) *The closure of $\mathcal{S}_J(\mathbf{R}_{>0}, (1/a,+\infty))$ in the Sobolev space $W^s_I(\mathbf{R}_{>0})$ is the closed subspace:*

$$
W^s_I(\mathbf{R}_{>0}, (1/a,+\infty)) \subset W^s_I(\mathbf{R}_{>0}) \tag{9.2.2.26}
$$

*obtained as the closed range of the idempotent multiplication operator $M_{\rho_{a,+}} : W^s_I(\mathbf{R}_{>0}) \to W^s_I(\mathbf{R}_{>0})$ obtained by multiplying by the indicator function $\rho_{a,+}(t) := \mathrm{1}_{[1/a,+\infty)}(t)$.*

(2) *The closure $\mathrm{HS}^s(\mathbf{C}_I, (1/a,+\infty))$ of $M(\mathcal{S}_J(\mathbf{R}_{>0}, (1/a,+\infty)))$ in the Hardy-Sobolev space $\mathrm{HS}^s(\mathbf{C}_I)$ satisfies the following property: there exists a commutative diagram of continuous linear operators with linearly short exact rows:*

(9.2.2.27)

```latex
\begin{tikzcd}
0 \arrow[r] & M_{[1/a,1]}W^s_I(\mathbf{R}_{>0}) \arrow[r] \arrow[d, "M"'] & M_{\rho_{a,+}}W^s_I(\mathbf{R}_{>0}) \arrow[r] \arrow[d, "M"'] & M_{\rho_{1,+}}W^s_I(\mathbf{R}_{>0}) \arrow[r] \arrow[d, "M"] & 0 \\
0 \arrow[r] & \mathrm{PW}^s(\mathbf{C}_I,a) \arrow[r] & \mathrm{HS}^s(\mathbf{C}_I,(1/a,+\infty)) \arrow[r] & \mathrm{HS}^s(\mathbf{C}_{I'}) \arrow[r] & 0
\end{tikzcd}
```

*where $M_{[1/a,1]}$ is the multiplication by $\mathrm{1}_{[1/a,1]}$ operator, the leftmost operators in (9.2.2.27) are continuous, with closed range, the rightmost are surjective and open, the vertical arrows are linear topological isomorphisms induced by the Mellin transform, and where:*

(1) *$I' \subset \mathbf{R}$ is the non-empty closed interval $I' := (-\infty,\sup(I)]$.*

(2) *$\mathrm{PW}^s(\mathbf{C}_I,a)$ is the closed linear subspace of the Hardy-Sobolev space $\mathrm{HS}^s(\mathbf{C}_I)$ of those holomorphic functions $\phi(s)$ over $\mathbf{C}_{\mathrm{Int}(I)}$ that extend to entire functions and satisfy:*

$$
\phi(s) = O\left( \frac{(1 - a^{-2\,\mathrm{Re}(s)})^{1/2}}{(\mathrm{Re}(s))^{1/2}} \right). \tag{9.2.2.28}
$$

DEFINITION 9.2.2.7 (Paley-Wiener space of weight $a$, degree $s$, base $I$). Let $I \subset \mathbf{R}$ be a non-empty closed interval, $s \ge 0$ an even integer. Let $a > 1$ be a real number. We denote by $\mathrm{PW}^s(\mathbf{C}_I,a)$ the closed subspace of $\mathrm{HS}^s(\mathbf{C}_I,(1/a,+\infty))$ defined in Theorem 9.2.2.6(2). We refer to $\mathrm{PW}^s(\mathbf{C}_I,a)$ as the Paley-Wiener space of weight $a$, degree $s$ and base $I$.

PROOF OF THEOREM 9.2.2.6. The proof of Theorem 9.2.2.6 proceeds similarly as the proof of Theorem 9.2.1.2.$^3$ $\square$

COROLLARY 9.2.2.8. *Let $I \in \mathbf{R}$ be a non-empty closed interval, $s \ge 0$ an even integer. Let $a > 1$ be a real number.*

Let $z_0 \in \mathbf{C}_{\le \sup(I)}$. Then:

(1) *if $z_0 \in \mathbf{C}_{<\sup(I)}$, then for any integer $k \ge 0$, the functional:*

$$
u \mapsto (\partial^k_z u)(z_0) \tag{9.2.2.29}
$$

is continuous.

---
$^3$Return here.

## PDF page 416

**416** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

(2) *If $\sup(I)$ is finite and $\mathrm{Re}(z_0) = \sup(I)$, then the functional:*

$$
u \mapsto (\partial^k_z u)(z_0) \tag{9.2.2.30}
$$

*is continuous if and only if the integer $k \ge 0$ satisfies: for every integer*

$$
0 \le k \le \left[\frac{s-1}{2}\right].
$$

PROOF. This is a consequence of Corollary 9.2.2.5.$^4$ $\square$

9.2.2.2. *The Hardy-Sobolev spaces $W^s_I(G)$.* We now return to the generality of $G$ an $\mathbf{R}_{>0}$-modulated group with module $|\cdot|_G$ and compact subgroup of module-$1$ elements $G^1$ (i.e. $G^1 := \ker(|\cdot|_G)$). Recall that the Mellin transform is a linear topological isomorphism:

$$
M : \mathcal{S}_I(G) \to A\mathcal{S}(\mathbf{C}_I) \overline{\otimes} \mathcal{S}(G^1)
$$

for any non-empty open interval $I \subset \mathbf{R}$, obtained as follows. We choose a unitary base-point $\chi$ for each connected component of the Riemann surface $\Omega(G)$, and for any $\phi \in \mathcal{S}_I(G)$, $M(\phi)$ sends $\phi$ to the element:

$$
M(\phi)((s,\omega)) = \int_{\mathbf{R}_{>0}} t^{ix_0(\chi)+s} \int_{G^1} \phi(\tau(t)\,g)\,\mathrm{d}\mu_1(g)\,\frac{\mathrm{d}t}{t}
$$

with $\omega := \chi|_{G^1}$, with $\mu_1$ is the volume-$1$ Haar measure on $G^1$, $\tau$ a fixed choice of continuous homomorphic section to the module $|\cdot|_G$, and $x_0 \in \mathbf{R}$ the unique real number such that $\chi(\tau(t)) = t^{ix_0(\chi)}$ as smooth functions of $t \in \mathbf{R}_{>0}$.

DEFINITION 9.2.2.9 (Sobolev $W^s_I$-spaces of $\mathbf{R}_{>0}$-modulated groups). Let $I \subset \mathbf{R}$ be a non-empty closed interval, $s \ge 0$ a real number. Let $\mu_G$ be the canonical Haar measure on $G$ (i.e. the unique Haar measure normalized so as to have, for every real number $\lambda \ge 1$, $\mu_G(\{g \in G : |g|_G \in [1/\lambda,\lambda]\}) = 2\log(\lambda) + O(1)$ as $\lambda \to +\infty$).

We define on $\mathcal{S}_{\mathrm{E}}(G)$ the following norm:

$$
\|\cdot\|_{I,s} : \phi \mapsto \sup_{a \le b : [a,b] \subset I} \left( \int_G |\phi(g)|^2 \max\{|g|^{2a}_G, |g|^{2b}_G\} (1 + |\log|g|_G|^2)^{s/2}\,\mathrm{d}\mu_G(g) \right)^{1/2} \tag{9.2.2.31}
$$

and denote by $W^s_I(G)$ the completion of $\mathcal{S}_{\mathrm{E}}(G)$ with respect to the norm $\|\cdot\|_{I,s}$. We refer to $W^s_I(G)$ as the Sobolev $W^s_I$-space of $G$, and to the norm $\|\cdot\|_{I,s}$ as the Sobolev $W^s_I$-norm.

We check the following basic properties of the Sobolev $W^s_I$-norms in the general case of $\mathbf{R}_{>0}$-modulated groups $G$, as opposed to the special case $G = \mathbf{R}_{>0}$, which is discussed in Lemma 9.2.2.2:

LEMMA 9.2.2.10 (Sobolev $W^s_I$-norms - II). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $I \subset \mathbf{R}$ be a closed interval, $s \ge 0$ a real number. Then:*

(1) *The Sobolev $W^s_I$-norm on $\mathcal{S}_{\mathrm{E}}(G)$ is continuous on $\mathcal{S}_{\mathrm{E}}(G)$ and it extends by continuity to $\mathcal{S}_J(G)$ for any non-empty open interval $J \subset \mathbf{R}$ containing $I$. The completion $W^s_I(G)$ of $\mathcal{S}_{\mathrm{E}}(G)$ equals the completion of $\mathcal{S}_J(G)$. Moreover, if $s$ is an even integer, then for any choice of continuous homomorphic section $\tau$ to the module $|\cdot|_G$, the pull-back map:*

$$
W^s_I(G) \to W^s_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1) \tag{9.2.2.32}
$$

*where $\mu_1$ is the volume-$1$ Haar measure on $G^1$ and $\widehat{\mu}_1$ is its Plancherel measure. The Mellin transform on $\mathcal{S}_{\mathrm{E}}(G)$ induces a linear topological isomorphism:*

$$
W^s_I(G) \to \mathrm{HS}^s(\mathbf{C}_I)\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1) \tag{9.2.2.33}
$$

---
$^4$Return here.

## PDF page 417

**9.2. HARDY-SOBOLEV SPACES $W^s_I(G)$ AND PALEY-WIENER CONDITIONS** · **417**

*where $\widehat{\mu}_1$ is the Plancherel measure of $\mu_1$, and the topology on the $\sigma$-tensor product is equivalent to the metrizable topology generated by the finitely many continuous seminorms:*

$$
\|\cdot\|'_{I,s} \otimes_\sigma \|\cdot\|_{L^2(\widehat{G^1},\widehat{\mu}_1)}
$$

*where, for each $u \in \mathrm{HS}^s(\mathbf{C}_I)$, $\|u\|'_{I,\sigma,k} := \left( \int_{\sigma - i\infty}^{\sigma + i\infty} |\partial^k_z u(z)|^2\,|\mathrm{d}z| \right)^{1/2}$ as $\sigma$ varies over the countably many elements of a sequence $\{c_k\}_{k \ge 0} \subset \mathbf{R}$ such that the finite boundary points of $\partial I$ are limit points of $\{c_k\}_{k \ge 0}$, and such that the integer $k \ge 0$ satisfies $0 \le k \le \left[\frac{s}{2}\right]$.*

(2) *If $I$ is compact of the form $I = [a,b]$, for $a \le b$ real numbers, then for any $\phi \in \mathcal{S}_{\mathrm{E}}(G)$ we have:*

$$
\|\phi\|_{I,s} = \left( \int_G |\phi(g)|^2 \max\{|g|^{2a}_G, |g|^{2b}_G\} (1 + |\log|g|_G|^2)^{s/2}\,\mathrm{d}\mu_G(g) \right)^{1/2}. \tag{9.2.2.34}
$$

(3) *Let $a,b \in \mathbf{R}$ be real numbers. If $I$ is of the form:*

(a) $I = [a,+\infty)$, then we have, for any $\phi \in \mathcal{S}_{\mathrm{E}}(G)$:

$$
\|\phi\|_{I,s} = \sup_{\sigma \ge a} \left( \int_G |\phi(g)|^2 \max\{|g|^{2a}_G, t^{2\sigma}\} (1 + |\log|g|_G|^2)^{s/2}\,\mu_G(g) \right)^{1/2}. \tag{9.2.2.35}
$$

(b) $I = (-\infty,b]$, then we have, for any $\phi \in \mathcal{S}_{\mathrm{E}}(G)$:

$$
\|\phi\|_{I,s} = \sup_{\sigma \le b} \left( \int_G |\phi(g)|^2 \max\{|g|^{2\sigma}_G, |g|^{2b}_G\} (1 + |\log|g|_G|^2)^{s/2}\,\mu_G(g) \right)^{1/2} \tag{9.2.2.36}
$$

PROOF. Upon proving (1), the rest of the Lemma follows from Lemma 9.2.2.2. Part (1) follows from the definition of the norm $\|\cdot\|_{I,s}$ combined with Theorem D.1.2.1.$^5$ $\square$

PROPOSITION 9.2.2.11 (Hardy-Sobolev duality - II). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. Assume $G$ is second-countable. Let $\mu_G$ be a choice of Haar measure on $G$. Let $I \subset \mathbf{R}$ be a closed non-empty interval, $s \ge 0$ a real number. Assume $I$ is compact, of the form $I = [a,b]$, for $a < b$ real numbers.*

*For every open interval $J \subset \mathbf{R}$ containing $I$, the pairing:*

$$
\langle \cdot, \cdot \rangle_{I,s} : \mathcal{S}_J(G) \times \mathcal{S}_J(G) \to \mathbf{C} \tag{9.2.2.37}
$$

defined by the assignment:

$$
\langle \phi, \psi \rangle_{I,s} := \int_G \phi(g)\,\psi(g)\,\mu_G(g) \tag{9.2.2.38}
$$

*is continuous and it extends to a continuous duality pairing:*

$$
\langle \cdot, \cdot \rangle_{I,s} : W^s_I(G) \times W^{-s}_I(G) \to \mathbf{C} \tag{9.2.2.39}
$$

*where $W^{-s}_I(G)$ is the completion of $\mathcal{S}_J(G)$ with respect to the norm:*

$$
\phi \mapsto \|\phi\|_{I,-s} := \left( \int_G |\phi(g)|^2\,w_{I,s}(g)^{-1}\,\mu_G(g) \right)^{1/2} \tag{9.2.2.40}
$$

with $w_{I,s}(g)$ the function:

$$
w_{I,s}(g) := \max\{|g|^{2a}_G, |g|^{2b}_G\}\,(1 + |\log|g|_G|^2)^{s/2}. \tag{9.2.2.41}
$$

*In particular, the induced linear map:*

$$
T_{I,s} : W^s_I(G)'_\beta \to W^{-s}_I(G) \tag{9.2.2.42}
$$

determined by (9.2.2.39), given explicitly by $T \mapsto w^{-1}_{I,s} \cdot T$.

---
$^5$Return here.

## PDF page 418

**418** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

The Proposition is proved in a manner analogous to the proof of Proposition 9.2.1.8, or by using Lemma 9.2.2.10(1).

COROLLARY 9.2.2.12. *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $a,s \in \mathbf{R}$ be real numbers, $a > 1$, $s \ge 0$. Let $I \subset \mathbf{R}$ be a non-empty closed interval. We denote by $M$ the Mellin transform $M : \mathcal{S}_I(G) \to A\mathcal{S}(\mathbf{C}_I) \overline{\otimes} \mathcal{S}(\widehat{G^1})$.*

(1) *For every point $z \in \mathbf{C}_{\mathrm{Int}(I)}$, the point-evaluation functional $\delta_z \otimes \delta_\omega$ and its derivatives $\delta^{(k)}_z \otimes \delta_\omega$, with $\omega \in \widehat{G^1}$ and $\delta_\omega$ the point-mass at $\omega$ on the space of square-summable sequences on the countable discrete abelian group $\widehat{G^1}$, are continuous on $\mathrm{HS}^s(\mathbf{C}_I,(1/a,+\infty))\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1)$.*

For every $\phi \in M_{\rho_{a,+}}W^s_I(G)$, we have:

$$
\delta^{(k)}_z(M(\phi)(s)) = \int_G \phi(g) (\log|g|_G)^m |g|^z_G\,\mu_G(g) \tag{9.2.2.43}
$$

for each integer $k \ge 0$.

(2) *For any $z \in \mathbf{C}_I$ with $\mathrm{Re}(z) \in \partial I$, the point-evaluation functional $\delta_z \otimes \delta_\omega$ and its derivatives $\delta^{(k)}_z \otimes \delta_\omega$ of order $0 \le k \le \left[\frac{s-1}{2}\right]$, are continuous on $\mathrm{HS}^s(\mathbf{C}_I,(1/a,+\infty))\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1)$.*

PROOF. The Corollary follows from Lemma 9.2.2.10 combined with Corollary 9.2.2.5. $\square$

THEOREM 9.2.2.13 (Paley-Wiener Theorem for Hardy-Sobolev Spaces - IV). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated abelian group. Let $a \in \mathbf{R}$ be a real number, $a > 1$. Let $I \subset \mathbf{R}$ be a non-empty closed interval. We denote by $M$ the Mellin transform $M : \mathcal{S}_I(G) \to A\mathcal{S}(\mathbf{C}_I) \overline{\otimes} \mathcal{S}(\widehat{G^1})$.*

We denote by:

$$
\mathcal{S}_I(G,(1/a,+\infty)) \subset \mathcal{S}_I(G) \tag{9.2.2.44}
$$

*the linear subspace of those Schwartz-Bruhat functions on $G$ of $I$-exponential decay, whose support is sent by the module homomorphism $|\cdot|_G$ into the interval $(1/a,+\infty) \subset \mathbf{R}_{>0}$.*

Then:

(1) *The closure of $\mathcal{S}_{\mathrm{E}}(G,(1/a,+\infty))$ in $W^s_I(G)$ is the closed subspace obtained as the closed range of the idempotent multiplication operator $M_{\rho_{a,+}} : W^s_I(G) \to W^s_I(G)$ obtained by multiplying by the indicator function $\rho_{a,+}(g) := \mathrm{1}_{[1/a,+\infty)}(g)$, $g \in G$.*

(2) *The Mellin transform $M$ extends by continuity to the linear topological isomorphism:*

$$
M : W^s_I(G) \to \mathrm{HS}^s(\mathbf{C}_I)\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1) \tag{9.2.2.45}
$$

*where the completion of the algebraic tensor product with respect to the Hausdorff locally topology generated by the family of seminorms associated to the inner products:*

$$
\langle \phi_1 \otimes u_1, \phi_2 \otimes u_2 \rangle_\sigma := \langle \phi_1, \phi_2 \rangle_{\mathrm{HS}^s_b(\mathbf{C})} \langle u_1, u_2 \rangle_{L^2(\widehat{G^1},\widehat{\mu}_1)},\ b \in I \tag{9.2.2.46}
$$

*for $\phi_1,\phi_2 \in \mathrm{HS}^s(\mathbf{C}_I)$ and $u_1,u_2 \in L^2(\widehat{G^1},\widehat{\mu}_1)$, with $\phi_1,\phi_2$ elements of $\mathrm{HS}^s_b(\mathbf{C}_I)$ by restriction to the vertical lines $b + i\mathbf{R}$ for each $b \in I$.*

(3) *The closure of $M(\mathcal{S}_I(G,(1/a,+\infty)))$ in $\mathrm{HS}^s(\mathbf{C}_I)\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1)$ satisfies the following property. There exists a commutative diagram of continuous linear operators with linearly short exact rows:*

(9.2.2.47)

```latex
\begin{tikzcd}
0 \arrow[r] & M_{[1/a,1]}W^s_I(G) \arrow[r] \arrow[d, "M"'] & M_{\rho_{a,+}}W^s_I(G) \arrow[r] \arrow[d, "M"'] & M_{\rho_{1,+}}W^s_I(G) \arrow[r] \arrow[d, "M"] & 0 \\
0 \arrow[r] & \mathrm{PW}^s(\mathbf{C}_I,a)\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1) \arrow[r] & \mathrm{HS}^s(\mathbf{C}_I,(1/a,+\infty))\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1) \arrow[r] & \mathrm{HS}^s(\mathbf{C}_I)\,\widehat{\otimes}_\sigma L^2(\widehat{G^1},\widehat{\mu}_1) \arrow[r] & 0
\end{tikzcd}
```



## PDF page 419

**9.3. MODULE STRUCTURES OVER $\mathcal{D}(G)$ AND APPROXIMATE UNITS** · **419**

*where $M_{[1/a,1]}$ is the multiplication by $\mathrm{1}_{[1/a,1]}$ operator, the leftmost operators in (9.2.2.47) are continuous, with closed range, the rightmost are surjective and open, the vertical arrows are linear topological isomorphisms induced by the Mellin transform.*

Proof. Part (2) of the Theorem is Lemma 9.2.2.10(1). The remaining assertions follow from Theorem 9.2.2.6.

$\square$

9.3. Module structures over $\mathcal{D}(G)$ and approximate units

In this section we discuss, for $G$ a second-countable $\mathbf{R}_{>0}$-modulated group, the continuous $\mathcal{D}(G)$-module structure on $W^s_I(G)$, with $\mathcal{D}(G)$ acting by convolution. We further construct, according to whether $I$ is a single point or has non-empty interior, approximate units for $W^s_I(G)$, i.e. a net of continuous linear endomorphisms converging to the identity with respect to the topology of simple convergence.

9.3.1. Module structure over $\mathcal{D}(G)$. Let $G$ be a Hausdorff locally compact abelian group. We recall that we denote by $\mathcal{D}(G)$ the convolution $\mathbf{C}$-algebra of smooth compactly supported test functions, equipped with its locally convex inductive limit topology as in [Bru, §4]. Similarly, $\mathcal{S}(G)$ is the convolution $\mathbf{C}$-algebra of Schwartz-Bruhat functions on $G$ (see [Bru, §8] and Appendix D of this work).

For any $\varphi\in\mathcal{D}(G)$, we may regularize the continuous left-translation action $\rho_G$ of $G$ on $\mathcal{S}(G)$ and its closed $G$-invariant subspaces, to obtain an operator $A(\varphi)$. Such operator may extend by continuity to completions of $\mathcal{S}(G)$ with respect to coarser topologies.

For $G$ a second-countable $\mathbf{R}_{>0}$-modulated group, $G$ acts continuously by left-translation on $\mathcal{S}_I(G)$, for $I\subset\mathbf{R}$ any non-empty open interval. We denote by $\rho_G:G\times\mathcal{S}_I(G)\to\mathcal{S}_I(G)$ such action, i.e. $\rho_G(g,\phi)(x):=\phi(g^{-1}x)$ as functions of $x\in G$. The same construction as in the foregoing defines a module structure of $\mathcal{D}(G)$ on $\mathcal{S}_I(G)$ which is continuous, giving the convolution operator $A(\varphi)$ associated to each $\varphi\in\mathcal{D}(G)$.

The operator $A(\varphi)$ may extend by continuity to completions of $\mathcal{S}_I(G)$ with respect to coarser topologies. This is the subject of study of this subsection: we discuss herein the convolution action of $G$ on $W^s_I(G)$ for any real number $s\ge 0$.

Definition 9.3.1.1. Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $\mu_G$ be a choice of Haar measure on $G$. Let $I$ be a non-empty closed interval, $s\ge 0$ a real number. We define the $\mathcal{D}(G)$-module structure on $E:=\mathcal{S}_I(G)$, respectively $E:=W^s_I(G)$, to be the linear map:

$$
A:\mathcal{D}(G)\to \mathscr{L}_\beta(E) \tag{9.3.1.1}
$$

assigned by, for each $\varphi\in\mathcal{D}(G)$:

$$
A(\varphi):=\int_G\varphi(g)\rho_G(g,\cdot)\,\mathrm{d}\mu_G(g) \tag{9.3.1.2}
$$

where the integral is in the sense of Pettis. We further refer to $A(\varphi)$ as the $\varphi$-regularized action of $G$ by continuous left-translation on $E$.

Remark 9.3.1.2. Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group, $E:=\mathcal{S}_I(G)$, $W^s_I(G)$ respectively, for $I$ a non-empty closed interval. Since $\varphi$ is compactly supported, we deduce that indeed $A$ is valued in $\mathscr{L}(E)$, the $\mathbf{C}$-algebra of continuous endomorphisms of $E$, by Theorem C.4.3.5, since $E$ is complete (see Theorem D.3.3.7(2) for the case $E=\mathcal{S}_I(G)$), hence quasi-complete.

Lemma 9.3.1.3. *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $I\subset\mathbf{R}$ be a closed non-empty interval, $s\ge 0$ be a real number. Then the linear operators $A$ from (9.3.1.1) from $\mathcal{D}(G)$ to $\mathscr{L}(\mathcal{S}_I(G))$, and to $\mathscr{L}(W^s_I(G))$, respectively, is continuous with respect to the locally convex inductive limit topology on the source, and the topology of uniform convergence on bounded subsets on the target.*

## PDF page 420

**420** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

Proof. By design of the locally convex inductive limit topology on $\mathcal{D}(G)$, it is enough to pre-compose $A$ with the linear topological embedding $\mathcal{D}_K(G,k)\to\mathcal{D}(G)$ for $K\subset G$ a compact subset with non-empty interior, $k\subset G^1$ a compact subgroup with compactly generated orthogonal $k^\perp\subset\widehat{G}$ such that $k\cdot K\subset K$, and with $\mathcal{D}_K(G,k)$ the linear subspace of $\mathcal{D}(G)$ of those $k$-invariant smooth compactly supported functions whose support is contained within $K$.

The linear space $\mathcal{D}_K(G,k)$ is topologized by transport of structure under the linear isomorphism $\mathcal{D}(G,k)\simeq\mathcal{D}(G/k)$ given by composition with the continuous quotient homomorphism $G\to G/k$.

Let $\{\varphi_i\}_{i\in I}$ be a net of test functions in $\mathcal{D}_K(G,k)$ converging to $\varphi\in\mathcal{D}_K(G,k)$.

We now consider the net of vector valued continuous functions $\{\alpha_i:K\to E\}_{i\in I}$, for $E:=\mathscr{L}_\beta(\mathcal{S}_I(G))$:

$$\alpha_i(g):=\varphi_i(g)\rho_G(g,\cdot),\quad g\in G.$$

Since $\varphi_i\to\varphi$ uniformly as continuous functions on $K$, and since $K$ is compact, then the convergence of $\varphi_i$ to $\varphi$ is also in the $L^1$-topology on $K$ with respect to $\mu_G$.

To check that $\alpha_i\to\alpha$ uniformly, we compose with the operator $M:\mathcal{S}_I(G)\to A\mathcal{S}(\mathbf{C}_I)\overline{\otimes}\mathcal{S}(\widehat{G^1})$, the Mellin transform from Theorem D.3.3.13, which gives, upon calling $\alpha:=\varphi\rho_G$, $M(\alpha_i(f))(c)=M(\varphi_i)(c)M(f)(c)$ and $M(\alpha(f))(c)=M(\varphi)(c)M(f)(c)$ as holomorphic functions on $\Omega(G)$, for all $f\in\mathcal{S}_I(G)$.

If $B\subset\mathcal{S}_I(G)$ is a bounded subset then $M(\alpha_i(f))(c)\to M(\alpha(f))(c)$ uniformly as $f\in B$, because $M(\alpha(f))(c)=M(\varphi)(c)M(f)(c)$, and $M(\varphi_i)(c)\to M(\varphi)(c)$ by $L^1(G,|\cdot|^{\sigma(c)}_G\mu_G)$-convergence of $\varphi_i$ to $\varphi$.

By Lemma C.4.3.12, we have $A(\varphi_i)\to A(\varphi)$ in $E$.

Upon choosing $E=W^s_I(G)$, the same argument as in the foregoing applies.

$\square$

Remark 9.3.1.4. Let $F$ be a number field, $G=C_F$ modulated by the idelic norm $|\cdot|_F$. Let $I\subset\mathbf{R}$ be a non-empty closed interval, $s\ge 0$ a real number. We denote by $W^s_I \mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ the closure of the closed subspace of global adelic $\theta$-functions $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ into $\mathcal{S}_\mathrm{E}(C_F)$. This is a closed invariant subspace of $W^s_I(C_F)$, and so the convolution action $A$ of $\mathcal{D}(C_F)$ on $\mathcal{S}_\mathrm{E}(C_F)$ and $\mathcal{S}_I(C_F)$ extends uniquely by continuity to a continuous linear map:

$$A:\mathcal{D}(C_F)\to \mathscr{L}_\beta(W^s_I \mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F)))$$

upon observing that it induces by composition a continuous operator:

$$A:\mathcal{D}(C_F)\to \mathscr{L}_\beta(\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F)),W^s_I \mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F)))$$

and, using the Fourier transform over $C_F$, we deduce that $A$ is valued in the image of the continuous linear operator from $\mathscr{L}_\beta(W^s_I \mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F)))$.

Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Then the space of $S$-local adelic $\theta$-functions $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ itself carries a continuous $\mathcal{D}(J_{F,S})$-module structure. It is given by the linear map:

$$
A_S:\mathcal{D}(J_{F,S})\to \mathscr{L}_\beta(\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))) \tag{9.3.1.3}
$$

assigned by, for each $\varphi\in\mathcal{D}(J_{F,S})$:

$$
A_S(\varphi):=\int_{J_{F,S}}\varphi(g)\rho_{F,S}(g,\cdot)\,\mathrm{d}\overline{\mu}_S(g) \tag{9.3.1.4}
$$

where the integral is in the sense of Pettis, and the same argument from Lemma 9.3.1.3 implies its continuity by the Second Structure Theorem (see Theorem 5.4.1.1), which reduces the continuity assertion to the case of the convolution action of $\mathcal{D}(J_{F,S})$ on $\mathcal{S}_{(0,+\infty)}(J_{F,S})$.

Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. The continuous left-translation action $\rho_G$ of $G$ on $W^s_I(G)$ is not unitary: it grows at most exponentially (where polynomial and ultra-polynomial growth, in the multiplicative sense, i.e. in the sense of functions

## PDF page 421

**9.3. MODULE STRUCTURES OVER $\mathcal{D}(G)$ AND APPROXIMATE UNITS** · **421**

over the Hausdorff locally compact abelian group $G$, is defined in terms of the function $g\mapsto |\log|g|_G|$, which measures rapid decay over $G$).

Lemma 9.3.1.5. *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $I=[a,b]\subset\mathbf{R}$ be a compact non-empty interval, $s\ge 0$ a real number. The function:*

$$
f:G\to \mathscr{L}_\beta(W^s_I(G)) \tag{9.3.1.5}
$$

*defined as $f(g):=\rho_G(g,\cdot)$, satisfies, for any continuous seminorm $p$ on $\mathscr{L}_\beta(W^s_I(G))$:*

$$
p(f(g))\le C_p\max\{|g|^a_G,|g|^b_G\}\,|\log|g|_G|^{s/2} \tag{9.3.1.6}
$$

*for a positive real number $C_p$ depending on $p$ and on $G$, $I$ and $s$. Moreover, $p(f)$ is $\mu_G$-measurable as a real-valued function on $G$.*

In particular, for $I=\{b\}$, a single point, then the operator norm of $\rho_G(g,\cdot)$ as $g$ varies over the second-countable $\mathbf{R}_{>0}$-modulated group $G$, grows at most polynomially over $G$.

Proof. We first treat the case $I=\{b\}$, i.e. $a=b$. We choose $p$ the operator norm. We have:

$$\|f(g)\|=\sup_{\|u\|_{s,2}=1}\left(\int_G|u(g^{-1}h)|^2(1+|\log|h|_G|^2)^{s/2}\,\mathrm{d}\mu_G(h)\right)^{1/2}$$

$$=\sup_{\|u\|_{s,2}=1}\left(\int_G|u(h)|^2(1+|\log|g|_G+\log|h|_G|^2)^{s/2}\,\mathrm{d}\mu_G(h)\right)^{1/2}$$

$$\le\sup_{\|u\|_{s,2}=1}\left(\int_G|u(h)|^2(1+|\log|g|_G|^2+2|\log|g|_G|\,|\log|h|_G|+|\log|h|_G|^2)^{s/2}\,\mathrm{d}\mu_G(h)\right)^{1/2}$$

$$\le C_0\sup_{\|u\|_{s,2}=1}\left(\|u\|_{0,2}^2+|\log|g|_G|^s\|u\|_{0,2}^2+\int_G|u(h)|^2|1+\log|h|_G|^2|^{s/2}\,\mathrm{d}\mu_G(h)+C_1(|\log|g|_G|^{s'})\right)^{1/2}$$

for $s'<s$ and the constant $C_1$ being absolute, as a consequence of (9.1.1.4) from Proposition 9.1.1.3, and for an absolute constant $C_0>0$ depending only on $s$.

By (9.1.1.4) from Proposition 9.1.1.3, the last term in the above chain of inequalities is bounded above by:

$$
C_0\sup_{\|u\|_{s,2}=1}\big(C_2+|\log|g|_G|^sC_2+1+C_1(|\log|g|_G|^{s'})\big)^{1/2} \tag{9.3.1.7}
$$

$$
=C_0\big(C_2+|\log|g|_G|^sC_2+1+C_1(|\log|g|_G|^{s'})\big)^{1/2}
$$

where $C_2$ is provided by (9.1.1.4) from Proposition 9.1.1.3 and depends on $G$.

We may write $G$ as the countable increasing union of the compact subsets $\tau([1/N,N])\cdot G^1$, where $\tau$ is a choice of continuous homomorphic section to the module $|\cdot|_G$, and $G^1$ is the compact subgroup of module-$1$ elements.

We may then write, for each $g\in G$ and $u\in W^s_I(G)$ with $\|u\|_{s,2}=1$:

$$\|\rho_G(g,u)\|_{s,2}=\lim_{N\to+\infty}\left(\int_{\tau([1/N,N])\cdot G^1}|u(g^{-1}h)|^2(1+|\log|h|_G|^2)^{s/2}\,\mathrm{d}\mu_G(h)\right)^{1/2}$$

and since each of the functions of $g$:

$$g\mapsto\left(\int_{\tau([1/N,N])\cdot G^1}|u(g^{-1}h)|^2(1+|\log|h|_G|^2)^{s/2}\,\mathrm{d}\mu_G(h)\right)^{1/2}$$

is continuous over $G$, we deduce that $\|\rho_G(g,u)\|_{s,2}$ is a $\mu_G$-measurable function of $g\in G$ for each $u\in W^s_I(G)$ of norm one (see [Ru-2, p.15, Corollaries, (a)]).

## PDF page 422

**422** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

Since $\|\rho_G(g,\cdot)\|$ is realized as the supremum over a countable subset $\{u_m\}_{m\ge 0}$ of the unit ball in $W^s_I(G)$ of the values $\|\rho_G(g,u_m)\|_{I,s}$, where $\{u_m\}_{m\ge 0}$ can be chosen to be an orthonormal basis for the Hilbert space $W^s_I(G)$, independent of $g\in G$, we see that $\|\rho_G(g,\cdot)\|$, as a function of $g\in G$, is the supremum of a sequence of $\mu_G$-measurable functions, hence itself $\mu_G$-measurable (see [Ru-2, p.14, Thm.1.14]).

The general case follows from a similar argument, choosing the continuous seminorm $p$ to be the operator norm:

$$p(T):=\sup_{\phi\in \mathscr{L}_\beta(W^s_I(G)):\|\phi\|_{I,s}\le 1}\|T(\phi)\|_{I,s}$$

and using Lemma 9.2.2.10(2).

$\square$

9.3.2. Approximate units. Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $I\subset\mathbf{R}$ be a closed non-empty interval, $s\ge 0$ a real number.

Within $W^s_I(G)$, we have the ability to approximate the identity with respect to the strong operator topology, by means of special continuous operators. We record this approximation result for later use.

9.3.2.1. *The case $I=\{b\}$.* The following Lemma is a consequence of [Co, Lemma 5].

Lemma 9.3.2.1 (Bounded Approximation of the identity). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group, $\mu_G$ a choice of Haar measure on $G$. Let $b,s\in\mathbf{R}$ be real numbers, $s\ge 0$. The continuous linear operator $A$ from (9.3.1.1) with target $\mathscr{L}_\beta(W^s_{\{b\}}(G))$, extends uniquely to a continuous linear operator*

$$
A:\mathcal{S}(G)\to \mathscr{B}_{\mathrm{NT}}(W^s_{\{b\}}(G)). \tag{9.3.2.1}
$$

*For each continuous character $\omega\in\widehat{G^1}$, we choose a continuous character $\chi\in\widehat{G}$ such that $\chi|_{G^1}=\omega$. There exists a countable subset $B=\{\varphi_{m,\omega}\}_{(m,\omega)\in\mathbf{N}\times\widehat{G^1}}\subset C^\infty(G)$ of smooth functions, such that*

$$
|\cdot|^b_G\cdot B\subset\mathcal{S}(G)
$$

*(i.e. $B\subset\mathcal{S}_I(G)$ for $I=\{b\}$) satisfying the following properties:*

(1) $A(B)$ is norm-bounded by $2$ in $W^s_{\{b\}}(G)$.

(2) For each $(m,\omega)\in\mathbf{N}\times\widehat{G^1}$, $\varphi_{m,\omega}$ is $\omega$-homogeneous.

(3) *For each integer $m\ge 0$, the Fourier transform of $|\cdot|^b_G\varphi_{m,\omega}\in B$ is supported over the compact subset of $\widehat{G}$ of characters of the form $\chi|\cdot|^{ix}_G$ for $x\in[-m,m]$.*

(4) *The closure of $A(B)$ with respect to the strong operator topology on $\mathscr{L}(W^s_{\{b\}}(G))=\mathscr{B}(W^s_{\{b\}}(G))$, contains the identity.*

We note that $\mathscr{B}_{\mathrm{NT}}(W^s_{\{b\}}(G))$, the $\mathbf{C}$-algebra of continuous $\mathbf{C}$-linear endomorphisms of the Hilbert space $W^s_{\{b\}}(G)$ topologized with the operator-norm topology (see Remark C.2.1.8), is $\mathscr{L}_\beta(W^s_{\{b\}}(G))$ as per (9.3.1.1).

Remark 9.3.2.2. We note that the nomenclature "Bounded Approximation" does not refer to the BAP, the Bounded Approximation Property, for Hausdorff locally convex topological $\mathbf{C}$-vector spaces. All normed spaces in this Chapter will be separable Hilbert spaces, and they have the Metric Approximation Property (see [Scha, Ch.III, §9]), since every countable orthonormal topological basis is a Schauder basis with basis constant (the supremum of the operator-norm of the projectors onto the line spanned by each basis element) equal to one.

Proof. The linear operator $\phi\mapsto|\cdot|^b_G\phi$ induces a linear isometry $W^s_{\{b\}}(G)\to W^{s,2}(G)$. Similarly, $\phi\mapsto|\cdot|^b_G\phi$ induces a linear topological isomorphism $\mathcal{S}(G)\to\mathcal{S}_{\{b\}}(G)$. It is therefore enough to treat the case $b=0$. Let $\varphi\in\mathcal{S}(G)$ be a Schwartz-Bruhat function. We define the assignment:

$$
A(\varphi):u\mapsto A(\varphi)(u):=\int_G\varphi(g)\rho_G(g,u)\,\mathrm{d}\mu_G(g) \tag{9.3.2.2}
$$

## PDF page 423

**9.3. MODULE STRUCTURES OVER $\mathcal{D}(G)$ AND APPROXIMATE UNITS** · **423**

on each element $u\in W^s_{\{b\}}(G)$. Upon defining the Radon measure $\mu:=|\varphi|\mu_G$ on $G$, a Hausdorff locally compact topological space, $\mu$ is finite Radon on $G$, and the function $g\mapsto\rho_G(g,u)$ is weakly measurable on $G$ for every $u\in W^{s,2}(G)$ (see Definition C.4.2.1), since it is continuous, being the left-translation action of $G$ on $W^{s,2}(G)$ continuous with respect to the strong operator topology.

The function $g\mapsto\|\rho_G(g,\cdot)\|$, the norm being the operator norm on $\mathscr{B}(W^{s,2}(G))$, is $\mu$-measurable and $\mu$-integrable, since, by Lemma 9.3.1.5, it is bounded above by the function $C|\log|g|_G|^s$ for a positive absolute constant $C$, and $\varphi$ is Schwartz-Bruhat over $G$, and hence decays faster than any positive power of $|\log|g|_G|^{-1}$ as $|\log|g|_G|\to+\infty$.

From Lemma C.4.3.11 applied to $E:=W^{s,2}(G)$, to our choice of $\mu$ dependent on $\varphi$, and to the function $f:g\mapsto\rho_G(g,\cdot)$, valued in $\mathscr{B}(E)$, we deduce that $A(\varphi)$ from (9.3.2.2) is a bounded $\mathbf{C}$-linear endomorphism on $W^{s,2}(G)$.

The assignment $\varphi\mapsto A(\varphi)$ defined in (9.3.2.2) therefore provides the desired extension of $A$ from (9.3.1.1) to the Schwartz-Bruhat functions $\mathcal{S}(G)$ on $G$, from $\mathcal{D}(G)$ (i.e. it extends $A$ from (9.3.1.1) from $\mathcal{D}(G)$ to the larger domain $\mathcal{S}(G)$).

We now show that $A:\mathcal{S}(G)\to \mathscr{B}_{\mathrm{NT}}(W^{s,2}(G))$ is continuous (with respect to the operator-norm topology on the target). This follows from Lemma C.4.3.9: indeed, the continuous norm on $\mathscr{B}_{\mathrm{NT}}(W^{s,2}(G))$ given by the operator-norm $\|\cdot\|$ satisfies:

$$\int_G\|\rho_G(g,\cdot)\|\,|\varphi(g)|\,\mu_G(g)\le C\int_G|\varphi(g)|\,|\log|g|_G|^s\,\mathrm{d}\mu_G(g)$$

for a positive absolute constant $C$. Since the function $f(g):=\int_G|\varphi(g)|\,|\log|g|_G|^s\,\mathrm{d}\mu_G(g)$ is itself a continuous seminorm on $\mathcal{S}(G)$, we deduce from Lemma C.4.3.9 that $A$ is continuous with respect to the Schwartz-Bruhat topology on the source, and the operator-norm topology on the target.

Let $\varepsilon>0$ be a fixed real number such that $-1+\varepsilon<1-\varepsilon$, and $\phi_0\in C^\infty_c(\mathbf{R})$ be a smooth cut-off function supported on $[-1,1]$, such that $\phi_0$ is bounded above by $1$, and equal to $1$ over the interval $[-1+\varepsilon,1-\varepsilon]$. Such $\phi_0$ exists by [Horm, Ch.I, Thm.1.4.1, p.25].

Let $\alpha_0\in\mathcal{S}(\mathbf{R}_{>0})$ be the inverse Fourier transform of $\phi_0$, i.e.:

$$\alpha_0(t):=\int_{-1}^{1}\phi_0(x)t^{2\pi ix}\,\mathrm{d}x.$$

We define, for each integer $m\ge 0$:

$$
\beta_m(t):=m\alpha_0(t^m). \tag{9.3.2.3}
$$

For every integer $m>0$, $\beta_m$ is a Schwartz-Bruhat function on $\mathbf{R}_{>0}$ such that the Fourier transform $\widehat{\beta_m}$ is supported on $[-m,m]$. Indeed, we have

$$\int_{\mathbf{R}_{>0}}\beta_m(t)t^{-2\pi ix}\,\frac{\mathrm{d}t}{t}=m\int_{-\infty}^{+\infty}\alpha_0(e^{my})e^{-2\pi ixy}\,\mathrm{d}y=\int_{-\infty}^{+\infty}\alpha_0(e^y)e^{-2\pi ixy/m}\,\mathrm{d}y=\phi_0(x/m)$$

which is supported over $[-m,m]$.

We now define, for each $\omega\in\widehat{G^1}$:

$$
\varphi_{m,\omega}:=\varphi_m\otimes\psi_\omega \tag{9.3.2.4}
$$

where $\psi_\omega$ is any choice of smooth compactly supported function on $G^1$ whose uniform norm is bounded above by $1/\mu_1(G^1)$, for $\mu_1$ the unique choice of Haar measure on $G^1$ such that $\mathrm{d}t/t$ is the push-forward of the quotient measure induced as per Theorem D.1.2.1 by the choices $\mu_G$ on $G$ and $\mu_1$ on $G^1$, and which is $\omega$-homogeneous.

## PDF page 424

**424** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

We have:

$$\|A(\varphi_{m,\omega})\|=\sup_{\|u\|_{s,2}=1}\left(\int_G\left|\int_G\varphi_{m,\omega}(g)u(g^{-1}h)\,\mathrm{d}\mu_G(g)\right|^2(1+|\log|h|_G|^2)^{s/2}\,\mathrm{d}\mu_G(h)\right)^{1/2}$$

$$=\sup_{\|u\|_{s,2}=1}\left(\int_G\left|\int_G\left\{\frac{\varphi_{m,\omega}(g)}{(1+|\log|g|_G|^2|^{s/2}}\right\}u(g^{-1}h)(1+|\log|g|_G|^2)^{s/2}\,\mathrm{d}\mu_G(g)\right|^2(1+|\log|h|_G|^2)^{s/2}\,\mathrm{d}\mu_G(h)\right)^{1/2}.$$

We now call

$$
\phi(g):=\left\{\frac{\varphi_{m,\omega}(g)}{(1+|\log|g|_G|^2|^{s/2}}\right\} \tag{9.3.2.5}
$$

a continuous, compactly supported function of $g\in G$, and $\nu:=(1+|\log|\cdot|_G|^2)^{s/2}\mu_G$, a regular Radon measure on $G$.

We then have:

$$
\left(\int_G\left|\int_G\left\{\frac{\varphi_{m,\omega}(g)}{(1+|\log|g|_G|^2|^{s/2}}\right\}u(g^{-1}h)(1+|\log|g|_G|^2)^{s/2}\,\mathrm{d}\mu_G(g)\right|^2(1+|\log|h|_G|^2)^{s/2}\,\mathrm{d}\mu_G(h)\right)^{1/2} \tag{9.3.2.6}
$$

$$=\|\phi*u\|_{L^2(G,\nu)}.$$

The rightmost side of (9.3.2.6) is, by [HR-1, Cor.20.14, p.293], bounded from above as:

$$
\|\phi*u\|_{L^2(G,\nu)}\le\|\phi\|_{L^1(G,\nu)}\|u\|_{L^2(G,\nu)}=\|\phi\|_{L^1(G,\nu)}\|u\|_{s,2}. \tag{9.3.2.7}
$$

Moreover, by design of $\phi$ from (9.3.2.5), we have:

$$
\|\phi\|_{L^1(G,\nu)}=\|\varphi_{m,\omega}\|_{L^1(G,\overline{\mu})}\le\int_{\mathbf{R}_{>0}}|\beta_m(t)|\,\frac{\mathrm{d}t}{t}\,\|\psi_\omega\|_{L^1(G^1,\mu_1)}\le\int_{\mathbf{R}_{>0}}|\beta_m(t)|\,\frac{\mathrm{d}t}{t}=\|\alpha_0\|_{L^1(\mathbf{R}_{>0},\mathrm{d}t/t)}. \tag{9.3.2.8}
$$

Since we choose $\alpha_0$ to be the inverse Fourier transform of $\phi_0$, which is in turn supported over $[-1,1]$ and bounded above by $1$, we see that we have $\|\alpha_0\|_{L^2(\mathbf{R}_{>0},\mathrm{d}t/t)}\le 2$.

We deduce that we have, for every $(m,\omega)\in\mathbf{N}\times\widehat{G^1}$:

$$
\|A(\varphi_{m,\omega})\|\le 2. \tag{9.3.2.9}
$$

We have therefore shown that the net $B:=\{\varphi_{m,\omega}\}_{(m,\omega)\in\mathbf{N}\times\widehat{G^1}}$ fulfills (1), (2) and (3) from the statement of the Lemma.

Since, by Lemma 4.3.2.2, the operators $\{1/\overline{\mu}_1(G^1)P_{F,\omega}\}_{\omega\in\widehat{G^1}}$ are projectors and the closure of their convex hull within $\mathscr{B}_{\mathrm{SOT}}(W^{s,2}(G))$ contains the identity, in order to show that $B$ fulfills (4) it is enough to show that the net $\{\varphi_{m,\omega}\}_{m\ge 0}$, for each fixed $\omega$, of $\omega$-homogeneous Schwartz-Bruhat functions on $G$ is such that the identity is in the closure in $\mathscr{B}_{\mathrm{SOT}}(W^{s,2}(G)(\omega))$ of $A(\{\varphi_{m,\omega}\}_{m\ge 0})$.

In turn, it is enough to show that the identity in $\mathscr{B}_{\mathrm{SOT}}(L^2(\mathbf{R}_{>0},(1+|\log(t)|^2)^{s/2}\frac{\mathrm{d}t}{t}))$ is in the closure of the linear span of the sequence of operators:

$$u\mapsto T(\beta_m)(u):=\int_{\mathbf{R}_{>0}}\beta_m(t)u(t^{-1}x)\,\frac{\mathrm{d}t}{t},\quad x\in\mathbf{R}_{>0}.$$

Since the identity in $\mathscr{B}_{\mathrm{SOT}}(L^2(\mathbf{R}_{>0},(1+|\log(t)|^2)^{s/2}\frac{\mathrm{d}t}{t}))$ is in the closure of the convex hull of the orthogonal projectors defined by multiplication by $\mathcal{F}^{-1}\circ M_{\mathrm{1}_{[-N,N]}}\circ\mathcal{F}$, for $\mathcal{F}$ the Fourier transform on $L^2(\mathbf{R}_{>0},\mathrm{d}t/t)$, and $N\ge 1$ an integer, then it is enough to show that for any integer $N\ge 1$ and for any $u\in L^2(\mathbf{R}_{>0},(1+|\log(t)|^2)^{s/2}\frac{\mathrm{d}t}{t})$ whose Fourier transform is supported over $[-N,N]$, then $T(\beta_m)(u)\to u$ as $m\to+\infty$ in $\|\cdot\|_{L^2(\mathbf{R}_{>0},(1+|\log(t)|^2)^{s/2}\frac{\mathrm{d}t}{t})}$-norm. This holds by Dominated Convergence and uniform boundedness (by $2$) of the operator norms $\|T(\beta_m)\|$ for every $m\ge 1$.

$\square$

We record the following consequence of Lemma 9.3.2.1:

## PDF page 425

**9.3. MODULE STRUCTURES OVER $\mathcal{D}(G)$ AND APPROXIMATE UNITS** · **425**

Corollary 9.3.2.3. *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group, $\mu_G$ a choice of Haar measure on $G$. Let $b,s\in\mathbf{R}$ be real numbers, $s\ge 0$.*

(1) *Let $\alpha,\beta\in\mathbf{R}$ be such that $\alpha<\beta$, and $\chi\in\widehat{G}$ a continuous character. Let $\varepsilon>0$ be a real number such that $\alpha+\varepsilon<\beta-\varepsilon$. There exists $u\in W^{s,2}(G)$ such that the Fourier transform $\widehat{u}$ is smooth, compactly supported over the subset $\chi|\cdot|^{i[\alpha,\beta]}_G$ of $\widehat{G^1}$, and is identically $1$ over the subset $\chi|\cdot|^{i[\alpha+\varepsilon,\beta-\varepsilon]}_G$.*

(2) *The set of those elements $u\in W^{s,2}(G)$ such that $\widehat{u}$ is compactly supported, is dense in $W^{s,2}(G)$.*

Proof. (1): The indicator function $\mathrm{1}_{\{\chi|_{G^1}\}}$ of the subset $\{\chi|_{G^1}\}\subset\widehat{G^1}$ is continuous and compactly supported, being $\widehat{G^1}$ discrete by [DE, Thm.3.2.1], as $G^1$ is compact. As such, its inverse Fourier transform $F$ is continuous, and hence continuous and compactly supported.

Let $\tau$ be a continuous homomorphic section to the idelic norm. We define $x_0$ to be the unique real number such that $\chi(\tau(t))=t^{ix_0}$ for all $t\in\mathbf{R}_{>0}$. We let $\phi_0$ be a smooth cut-off function on $\mathbf{R}$ whose support is contained in $x_0+[\alpha,\beta]\subset\mathbf{R}$ and such that $\phi_0|_{x_0+[\alpha+\varepsilon,\beta-\varepsilon]}=1$. Such $\phi_0$ exists by [Horm, Ch.I, Thm.1.4.1, p.25]. We let $\varphi$ be the inverse Fourier transform on $\mathbf{R}_{>0}$ of $\phi_0$. The function $u:=\varphi\otimes F$ is an element of $W^{s,2}(G)$ for any $s\ge 0$, and $\widehat{u}$ is supported only over $\chi|\cdot|^{i[\alpha,\beta]}_G$, and it is identically $1$ over the subset $\chi|\cdot|^{i[\alpha+\varepsilon,\beta-\varepsilon]}_F$.

(2): Let $u\in W^{s,2}(G)$ be an arbitrary element. By Lemma 9.3.2.1, there exists a countable net $B\subset\mathcal{S}(G)$ such that $A(B)$ is norm-bounded in $\mathscr{B}(W^{s,2}(G))$, the Fourier transform of each element of $B$ is compactly supported, and the identity is contained in the closure of $A(B)$ with respect to the strong operator topology. In particular, for any $\varepsilon>0$ there exists $b\in B$ such that $\|A(b)(u)-u\|_{s,2}<\varepsilon$. Since $\widehat{A(b)(u)}=\widehat{b}\widehat{u}$, and $\widehat{b}$ is compactly supported over $\widehat{G}$, then so is $\widehat{A(b)(u)}$.

$\square$

9.3.2.2. *The general case: approximate units in $W^s_I(G)$.* In this subsection we construct approximate units in $\mathscr{L}_\sigma(W^s_I(G))$ using a divisor on the Riemann surface $\Omega(G)$ supported on a vertical strip of bounded width contained in a single connected component.

We begin with the following:

Lemma 9.3.2.4. *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. Let $\chi\in\widehat{G}$ be a fixed continuous character. Let $I\subset\mathbf{R}$ be a compact interval with non-empty interior.*

*Let $\phi\in\mathcal{S}_\mathrm{E}(G)$. Let $T\in\mathbf{R}$ be a real number. Then the number of zeros of $M(\phi)(\chi|\cdot|^z_G)$ contained in the box $I\times i[T,T+1]$ is $O(\log|T|)$, where the implied constant depends on $\phi$ and $I$.*

Proof. Let $a\in\mathbf{R}$ be a real number such that $M(\phi)(\chi|\cdot|^z_G)$ has no zeros on the boundary of $\mathbf{C}_I$ and $a+i\mathbf{R}$ is not contained in $\mathbf{C}_I$. We define $z_0:=a+iT+i/2$, $r\ge 0$ a real number large enough so as to arrange that the closed ball centered at $z_0$ with radius $r$ contains the box $I+i[T,T+1]$. We fix a real number $R>r$. By [Lang-b, Ch.XVII, §2, Lemma 2.2, p.333], the Maximum Principle and since $R/r>1$, we have, upon calling $N(T)$ the number of zeros of $M(\phi)(\chi|\cdot|^z_G)$ contained in $B(z_0,r)$:

$$N(T)\log(R/r)\le\log(B)-\log|M(\phi)(\chi|\cdot|^{z_0}_G)|$$

for a large enough real number $B>0$, and hence $N(T)=O(\log|M(\phi)(\chi|\cdot|^{a+iT+i/2}_G)|)$. Since $M(\phi)$ is uniformly Schwartz on every vertical strip of bounded width of each connected component of $\Omega(G)$, we deduce that for every integer $N\ge 0$, there exists a real number $C_N>0$ such that $M(\phi)(\chi|\cdot|^{a+iT+i/2}_G)=O(|T|^N)$ as $|T|\to+\infty$.

We deduce that $N(T)=O(\log|T|)$ holds, with a possibly different implied constant, depending on $\phi$ and $I$.

$\square$

Lemma 9.3.2.5. *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $\chi\in\widehat{G}$ be a fixed continuous character. Let $I\subset\mathbf{R}$ be a compact interval with non-empty interior.*

## PDF page 426

**426** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

*Let $\phi \in \mathcal{S}_{\mathrm{E}}(G)$. Assume that all the zeros of $M(\phi)(\chi\lvert\cdot\rvert^z_G)$ are contained in the interior of the vertical strip $\mathbf{C}_I$. Then the quotient of $\mathcal{S}_{\mathrm{E}}(G)$ by the convolution ideal $\phi \ast \mathcal{S}_{\mathrm{E}}(G)$ admits an absolute Schauder basis whose set of coefficient functionals is given by the point-evaluation functionals at the zeros of $M(\phi)(\chi\lvert\cdot\rvert^z_G)$ and their derivatives, i.e. $\delta^{(k)}_{\rho}$ as $\rho$ varies over the zeros of $M(\phi)(\chi\lvert\cdot\rvert^z_G)$ and $0 \le k \le N(\rho)-1$, with $N(\rho)$ the multiplicity of $\rho$.*

Proof. The exponential decay condition defining $\mathcal{S}_{\mathrm{E}}(G)$ implies the convergence axiom defining Schauder bases, using Lemma 9.3.2.4 and Theorem D.3.3.13, combined with the description of the topology on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ provided by Lemma D.3.1.2. By Theorem 4.1.2.6(1) and (3), indeed the Schauder basis is absolute.$^6$ $\square$

THEOREM 9.3.2.6 (Approximate units in $\mathscr{L}_{\sigma}(W^s_I(G))$). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $I \subset \mathbf{R}$ be a closed interval with non-empty interior, $s \ge 0$ a real number. For $T > 0$ a real number, we define the closed subspace:*

$$
W^s_I(G)_{\le T} := \bigcap_{\rho: M(\phi)(\chi\lvert\cdot\rvert^{\rho}_G)=0, \lvert\mathrm{Im}(\rho)\rvert \le T} \bigcap_{0 \le k \le N(\rho)-1} \ker(\delta^{(k)}_{\rho}). \tag{9.3.2.10}
$$

*The orthogonal projectors $P_T$ onto each $W^s_I(G)_{\le T}$ form a net of orthogonal projectors whose limit as $T \to +\infty$ with respect to the topology of simple convergence is the identity, i.e. $P_T \to \mathrm{Id}$ as $T \to +\infty$ with respect to the strong operator topology on the space of continuous endomorphisms of the Hilbert space $W^s_I(G)$.*

Proof. Using the basis projectors provided by Lemma 9.3.2.5 we see that $\bigcup_{T>0} W^s_I(G)_{\le T}$ is dense in $W^s_I(G)$, which implies that the net of orthogonal projectors $\{P_T\}_{T>0}$ indeed converges strongly to the identity, since $W^s_I(G)_{\le T} \subset W^s_I(G)_{\le T'}$ for every pair of real numbers $0 < T < T'$. $\square$

9.3.3. Trace of the regular representation on $W^s_I(G)$. Let $G$ be an $\mathbf{R}_{>0}$-modulated Hausdorff locally compact abelian group, with module $\lvert\cdot\rvert_G$. Let $\mu_G$ be a choice of Haar measure on $G$. Let $I \subset \mathbf{R}$ be a non-empty closed interval, $s \ge 0$ a real number. The continuous left-translation action $\rho_G$ of on $\mathcal{S}_{\mathrm{E}}(G)$ extends by continuity to $W^s_I(G)$. We refer to this continuous representation of $G$ as the regular representation of $G$ on $W^s_I(G)$.

9.3.3.1. *Cutoffs.* The purpose of this subsection is to introduce truncation operators, to be reprised later. We let $\varphi: G \to \mathbf{C}$ be a bounded function, whose support is compact. The operator

$$
A_G(\varphi): \psi \mapsto \int_G \varphi(g)\psi(g^{-1}x)\,\mathrm{d}\mu_G(g)
$$

is well defined and it is continuous as an operator on $W^{s,2}(G)$ by Theorem C.4.3.5, which applies by boundedness of $\varphi$ and compactness of its support, which implies that $g \mapsto \varphi(g)\rho_G(g,\cdot)$, as a uniformly continuous (see Lemma 4.3.3.1 and the discussion preceding Lemma D.2.2.1) $W^{s,2}(G)$-valued function, is $\mu_G$-integrable in the sense of Pettis.

We will be computing the trace of the nuclear obtained from $A_G(\varphi)$ by composition with a truncation operator.

For any non-empty connected interval $I \subset \mathbf{R}$ and $a \in \mathbf{R}$ such that $-a+I$ contains $0 \in \mathbf{R}$, we will be making the calculation also on the closure of $\lvert\cdot\rvert^a_G \mathcal{S}_I(G)$ in $W^{s,2}(G)$, noting that every element $\psi$ of $\lvert\cdot\rvert^a_G \mathcal{S}_I(G)$ is absolutely square-integrable with respect to the Radon measure $(1+\lvert\log\lvert\cdot\rvert_G\rvert^2)^{s/2}\mu_G$ for any $s \ge 0$, since it is a Schwartz-Bruhat function on $G$, i.e. an element of $\mathcal{S}(G)$, by definition of $\mathcal{S}_I(G)$, the Hausdorff locally convex topological $\mathbf{C}$-vector space of Schwartz-Bruhat functions on $G$ with $I$-exponential decay (see Definition D.3.3.1 from §D.3).

$^6$Return here.

## PDF page 427

**9.3. MODULE STRUCTURES OVER $\mathcal{D}(G)$ AND APPROXIMATE UNITS** · **427**

The truncation operators alluded to in the foregoing are obtained by integration on growing relatively compact domains of the $\mathbf{R}_{>0}$-modulated group $G$ of the form $\{g \in G : \lvert g\rvert_G \in (1/\Lambda,\Lambda)\}$ for $\Lambda > 0$. We refer the reader to Definition D.2.1.1 for more on modulated groups. Recall that an $\mathbf{R}_{>0}$-modulated group is a Hausdorff locally compact abelian group $G$ equipped with a module homomorphism $\lvert\cdot\rvert_G: G \to \mathbf{R}_{>0}$ which is assumed to be surjective and proper. Its fibre over $1 \in \mathbf{R}_{>0}$, i.e. its kernel $G^1 := \ker(\lvert\cdot\rvert_G)$, is a closed compact Hausdorff abelian group.

Let $K \subset \mathbf{R}_{>0}$ be a compact subset. We define $G^K$ to be the compact subset:

$$
G^K := \{g \in G : \lvert g\rvert_G \in K\} \subset G.
$$

For instance, for any real number $\Lambda > 0$:

$$
G^{[1/\Lambda,\Lambda]} := \{g \in G : \lvert g\rvert_G \in [1/\Lambda,\Lambda]\} \subset G
$$

a compact subset of $G$ with non-empty interior.

DEFINITION 9.3.3.1 (Smooth cutoffs). Let $G$ be an $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$. We let $\mu_G$ be a choice of Haar measure on $G$. Let $I$ be a closed non-empty interval. Let $\Lambda,\varepsilon > 0$ and $s \ge 0$ be real numbers. Assume $0 < 1/\Lambda-\varepsilon < \Lambda-\varepsilon$. We let $\rho: G \to \mathbf{C}$ be a function such that:

(1) $\rho$ is bounded with $\lVert\rho\rVert_u = 1$, real-valued and nonnegative.

(2) $\rho$ is constant on the fibres of the module $\lvert\cdot\rvert_G: G \to \mathbf{R}_{>0}$, equivalently $\rho$ is $G^1$-invariant.

(3) The unique function induced by $\rho$ on $\mathbf{R}_{>0}$ by $G^1$-invariance and through the module $\lvert\cdot\rvert_G: G/G^1 \simeq \mathbf{R}_{>0}$, is smooth away from finitely many points, at each of which its derivatives of any nonnegative integer order have at worst jump discontinuities, such that both one-ended limits exist and are finite.

(4) $\rho$ is multiplicatively symmetric, i.e. $\rho(g) = \rho(g^{-1})$.

(5) $\rho$ is supported over $G^{[1/\Lambda,\Lambda]}$.

(6) $\rho$ is identically $1$ over $G^{[1/\Lambda+\varepsilon,\Lambda-\varepsilon]}$.

We refer to $\rho$ as a $(\Lambda,\varepsilon)$-cutoff. If $\rho$ is smooth, then we refer to $\rho$ as a smooth $(\Lambda,\varepsilon)$-cutoff. For $\rho$ a $(\Lambda,\varepsilon)$-cutoff, we define the $\rho$-truncation operator to be the multiplication operator:

$$
M_{\rho}: W^s_I(G) \to W^s_I(G) \tag{9.3.3.1}
$$

defined as:

$$
M_{\rho}(\phi)(g) := \rho(g)\phi(g) \tag{9.3.3.2}
$$

as functions of $g \in G$.

REMARK 9.3.3.2. We note that indeed $M_{\rho}$ is a continuous linear endomorphism of $W^s_I(G)$, since for any $\phi \in W^s_I(G)$, we have:

$$
\int_G \lvert(M_{\rho}\phi)(g)\rvert^2 \max\{\lvert g\rvert^{2a}_G,\lvert g\rvert^{2b}_G\}(1+\lvert\log\lvert g\rvert_G\rvert^2)^{s/2}\,\mathrm{d}\mu_G(g) \le \int_G \lvert\phi(g)\rvert^2 \max\{\lvert g\rvert^{2a}_G,\lvert g\rvert^{2b}_G\}(1+\lvert\log\lvert g\rvert_G\rvert^2)^{s/2}\,\mathrm{d}\mu_G(g) < +\infty
$$

and hence $M_{\rho}$ is valued in $W^s_I(G)$ and bounded, and since $\rho$ is multiplicatively symmetric, it satisfies:

$$
M_{\rho} = J \circ M_{\rho} \circ J \tag{9.3.3.3}
$$

where $J$ is the linear topological isomorphism of $W^s_I(G) \to W^s_{-I}(G)$ given by inversion on $G$. If $I=[a,b]$ for real numbers $a<b$, then $M_{\rho}$ is a self-adjoint operator on the Hilbert space $W^s_I(G)$. Indeed, for any $\phi \in W^s_I(G)$ we have:

$$
\langle M_{\rho}\phi,\phi\rangle_{W^s_I(G)} = \int_G \rho(g)\lvert\phi(g)\rvert^2 \max\{\lvert g\rvert^{2a}_G,\lvert g\rvert^{2b}_G\}(1+\lvert\log\lvert g\rvert_G\rvert^2)^{s/2}\,\mathrm{d}\mu_G(g) \ge 0
$$

## PDF page 428

**428** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

which implies that $M_{\rho}$ is a positive operator. By [Cnw-a, Ch.II,§2,Prop.2.12,p.33], it is self-adjoint (more generally, every multiplication operator is normal by [Cnw-a, Ch.II,§2,Prop.2.16(b),p.35], and by [Cnw-a, Ch.II,§2,Example 2.8,p.32] it is self-adjoint if and only if it is real valued). If $G$ is second-countable, then $G$ is $\sigma$-compact, and $\mu_G$ is $\sigma$-finite. By [Cnw-a, Ch.II,§1,Thm.1.5,p.28], we have $\lVert M_{\rho}\rVert = \lVert\rho\rVert_{\infty} = \lVert\rho\rVert_u = 1$. $M_{\rho}$ is injective if the zero-set of $\rho$ is $\mu_G$-negligible as a subset of $G$. The operator $M_{\rho}$ is not generally an idempotent operator, unless $\rho$ is constant over $G$ on an open subset of the form $G - \bigcup_{1 \le k \le N}\{g \in G : \lvert g\rvert_G = t_k\}$ for a finite set $\{t_k\}_{1 \le k \le N}$. $M_{\rho}$ has closed range if $\rho$ is strictly bounded away from $0$ on a subset of $G$ whose complement is $\mu_G$-negligible.

DEFINITION 9.3.3.3 (Absolute cutoffs). Let $G$ be an $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$. We let $\mu_G$ be a choice of Haar measure on $G$. Let $I$ be a closed non-empty interval. Let $\Lambda > 0$ and $s \ge 0$ real numbers. We let $\rho_{\Lambda,+},\rho_{\Lambda,-}: G \to \mathbf{R}_{\ge 0}$ be the bounded functions:

$$
\rho_{\Lambda,+}(x) := \mathrm{1}_{G^{\ge 1/\Lambda}}(x),\; \rho_{\Lambda,-}(x) := \mathrm{1}_{G^{\le \Lambda}}(x),\; x \in G \tag{9.3.3.4}
$$

and $\rho_{\Lambda}: G \to \mathbf{R}_{\ge 0}$ be the bounded function:

$$
\rho_{\Lambda}(x) := \mathrm{1}_{G^{[1/\Lambda,\Lambda]}}(x) = \rho_{\Lambda,+}(x)\rho_{\Lambda,-}(x),\; x \in G. \tag{9.3.3.5}
$$

We refer to $\rho_{\Lambda,+}$, respectively $\rho_{\Lambda,-}$, as a positive, respectively negative $\Lambda$-cutoff, and to $\rho_{\Lambda}$ as a $\Lambda$-cutoff. For $\rho \in \{\rho_{\Lambda,+},\rho_{\Lambda,-},\rho_{\Lambda}\}$, we define the multiplication operator:

$$
M_{\rho}: W^s_I(G) \to W^s_I(G) \tag{9.3.3.6}
$$

defined as:

$$
M_{\rho}(\phi)(g) := \rho(g)\phi(g) \tag{9.3.3.7}
$$

as functions of $g \in G$.

REMARK 9.3.3.4. As in Remark 9.3.3.2, for $\rho \in \{\rho_{\Lambda,+},\rho_{\Lambda,-},\rho_{\Lambda}\}$, we note that indeed $M_{\rho}$ is a continuous linear endomorphism of $W^{s,2}(G)$, since for any $\phi \in W^{s,2}(G)$, we have:

$$
\int_G \lvert(M_{\rho}\phi)(g)\rvert^2 (1+\lvert\log\lvert g\rvert_G\rvert^2)^{s/2}\,\mathrm{d}\mu_G(g) \le \int_G \lvert\phi(g)\rvert^2 (1+\lvert\log\lvert g\rvert_G\rvert^2)^{s/2}\,\mathrm{d}\mu_G(g) < +\infty
$$

and hence $M_{\rho}$ is valued in $W^{s,2}(G)$ and bounded. Each $M_{\rho}$ is a positive operator. By [Cnw-a, Ch.II,§2,Prop.2.12,p.33], it is self-adjoint (as noted in Remark 9.3.3.2, more generally, every multiplication operator is normal by [Cnw-a, Ch.II,§2,Prop.2.16(b),p.35], and by [Cnw-a, Ch.II,§2,Example 2.8,p.32] it is self-adjoint if and only if it is real valued). It is injective, since each choice of $\rho$ vanishes only on a $\mu_G$-negligible subset of $G$. By [Cnw-a, Ch.II,§1,Thm.1.5,p.28], we have $\lVert M_{\rho}\rVert = \lVert\rho\rVert_{\infty} = 1$. Moreover, since each of the three given choices of $\rho$ is, for each $\Lambda > 0$, essentially bounded below away from $0$, then $M_{\rho}$ has closed range. Another way to see this is to observe that $M^2_{\rho} = M_{\rho}$, from which it follows by [Cnw-a, Ch.II,§3,Pop.3.2,(b),p.37] that $M_{\rho}$ has closed range. In fact, by [Cnw-a, Ch.II,§3,Pop.3.3,p.37], it is an orthogonal projector.

For $G$ an $\mathbf{R}_{>0}$-modulated group, and $\mu_G$ a choice of Haar measure on $G$, continuous homomorphic sections $\tau$ to the module $\lvert\cdot\rvert_G$ exist (see Remark D.2.1.2). We define $\mu_1$ to be the unique Haar measure on $G^1$ such that, under the isomorphism of Hausdorff locally compact abelian groups $G \simeq \mathbf{R}_{>0} \times G^1$ induced by one such choice of $\tau$, $\mu_G$ is pushed-forward to $\frac{\mathrm{d}t}{t} \otimes \mu_1$.

Theorem A.5.4.1, which is Lebesgue's Differentiation Theorem for Hausdorff locally compact abelian groups, and which rests on an analog of the Hardy-Littlewood Maximal Theorem (see Theorem A.5.3.6 and

## PDF page 429

**9.3. MODULE STRUCTURES OVER $\mathcal{D}(G)$ AND APPROXIMATE UNITS** · **429**

its global form, Theorem A.5.3.7) leads to the concept of "smoothening" of a locally integrable function on a Hausdorff locally compact abelian group at a point (see Terminology A.5.4.1).

We refer the reader to §A.5.3, §A.5.4, and to [Bris-a, §3], where a generalization of the same instruments leads to trace formulas for nuclear integral operators on the $L^2$-space of a Hausdorff locally compact second-countable topological space equipped with a Radon measure; see also [Bris-a, §3.1,Thm.3.1], and the special case of subdomains of Euclidean spaces from [Bris-b, Thm.3.1].

9.3.3.2. *Calculation of the trace of $M_{\rho} \circ A(\varphi)$.* We have the following:

THEOREM 9.3.3.5 (Nuclearity of the smoothly truncated regular representation on $W^s_I(G)$). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$. Assume $G$ is second-countable. Let $I$ be a non-empty closed interval. We let $\mu_G$ be a choice of Haar measure on $G$. Let $\Lambda,\varepsilon > 0$ and $s \ge 0$ real numbers. Assume $0 < 1/\Lambda+\varepsilon < \Lambda-\varepsilon$. Let $\rho: G \to \mathbf{R}_{\ge 0}$ be a $(\Lambda,\varepsilon)$-cutoff. Then:*

(1) *for every bounded compactly supported complex-valued function $\varphi$ on $G$, the following endomorphism of $W^s_I(G)$:*

$$
M_{\rho} \circ A_G(\varphi) \tag{9.3.3.8}
$$

*is an integral Hilbert-Schmidt operator whose integral kernel has an absolutely $\mu_G$-integrable smoothening along the diagonal.*

(2) *For every smooth compactly supported $\varphi \in \mathcal{D}(G)$ and every smooth $(\Lambda,\varepsilon)$-cutoff, then the Hilbert-Schmidt operator in (9.3.3.8) is nuclear, and its nuclear trace equals the integral of the integral kernel along the diagonal.*

(3) *As $\rho \to 1$ pointwise over $G$ with $\varepsilon\Lambda = o(1)$ as $\Lambda \to +\infty$, then the integral of the smoothening along the diagonal of the integral kernel of the operator in (9.3.3.8) is:*

$$
\mathrm{Trace}(M_{\rho} \circ A_G(\varphi)) = 2\log(\Lambda)\,\mu_1(G^1)\,\varphi(1) + o(1). \tag{9.3.3.9}
$$

Proof. Assume first that $0 \in I$ holds. We denote by $\rho_{I,s}: G \times W^s_I(G) \to W^s_I(G)$ the continuous left translation action $\rho_G$ of $G$ on $W^s_I(G)$ for any real number $s \ge 0$. We now note that $M_{\rho} \circ \int_G \varphi(g)\rho_{\{0\},0}(g,\cdot)\,\mathrm{d}\mu_G(g)$, factors through $W^s_I(G)$ for any $s > 0$ and any non-empty closed interval containing $0$.

Explicitly, given the injective continuous (by Proposition 9.1.1.3(1)) linear operator $U_{I,s}: W^s_I(G) \to L^2(G,\mu_G)$, we have

$$
M_{\rho} \circ \int_G \varphi(g)\rho_s(g,\cdot)\,\mu_G(g) = U_{I,s} \circ M_{\rho} \circ \int_G \varphi(g)\rho_{\{0\},0}(g,\cdot)\,\mu_G(g). \tag{9.3.3.10}
$$

By [Scha, Ch.III,Cor.3,p.100], if $M_{\rho} \circ \int_G \varphi(g)\rho_{\{0\},0}(g,\cdot)\,\mathrm{d}\mu_G(g)$ is nuclear, then so is

$$
M_{\rho} \circ \int_G \varphi(g)\rho_{I,s}(g,\cdot)\,\mathrm{d}\mu_G(g). \tag{9.3.3.11}
$$

Moreover, their traces are the same by Lemma C.3.2.2. We therefore may and do assume $s=0$ and $I=\{0\}$. We abbreviate $L^2(G,\mu_G)$ as $L^2(G)$. We rename $\rho_{\{0\},0}$ as $\rho_0$. We analyze the commutator operator:

$$
\left[M_{\rho} \circ \left(\int_G \varphi(g)\rho_0(g,\cdot)\,\mathrm{d}\mu_G(g)\right) - \left(\int_G \varphi(g)\rho_0(g,\cdot)\,\mathrm{d}\mu_G(g)\right) \circ M_{\rho}\right]: L^2(G) \to L^2(G). \tag{9.3.3.12}
$$

## PDF page 430

**430** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

This operator is Hilbert-Schmidt on $L^2(G)$, with integral kernel given by the element $K_{\varphi,\rho}(x,y) \in L^2((G)_x \times (G)_y)$:

$$
K_{\varphi,\rho}(x,y) := \varphi(xy^{-1})(\rho(x)-\rho(y)). \tag{9.3.3.13}
$$

We check the square-integrability property of $K_{\varphi,\rho}(x,y)$ over $G \times G$ explicitly. Let $B \subset G$ be the compact support of $\varphi$. The support of $K_{\varphi,\rho}$ is the union within $(G)_x \times (G)_y$

$$
[1/\Lambda,\Lambda] \times (B^{-1} \cdot [1/\Lambda,\Lambda]) \cup (B \cdot [1/\Lambda,\Lambda]) \times [1/\Lambda,\Lambda]
$$

which is compact within $(G)_x \times (G)_y$. $K_{\varphi,\rho}$ is therefore $p$-integrable over $(G)_x \times (G)_y$ with respect to the product measure $\mu_G \otimes \mu_G$, for every $p \ge 1$.

We now check the assertion that indeed the operator from (9.3.3.13) is Hilbert-Schmidt with $K_{\varphi,\rho}$ as its integral kernel. We have, for any $u \in L^2(G)$:

$$
\int_{y \in G} K_{\varphi,\rho}(x,y)u(y)\,\mathrm{d}\mu_G(y) = \int_{y \in G} \varphi(xy^{-1})(\rho(x)-\rho(y))u(y)\,\mathrm{d}\mu_G(y)
$$

$$
= \rho(x)\int_G \varphi(xy^{-1})u(y)\,\mathrm{d}\mu_G(y) - \int_G \varphi(xy^{-1})\rho(y)u(y)\,\mathrm{d}\mu_G(y)
$$

$$
= \left[M_{\rho} \circ \left(\int_G \varphi(g)\rho_0(g,\cdot)\,\mathrm{d}\mu_G(g)\right) - \left(\int_G \varphi(g)\rho_0(g,\cdot)\,\mathrm{d}\mu_G(g)\right) \circ M_{\rho}\right](u)(x)
$$

for $\mu_G$-almost all $x \in G$, which indeed shows, by of Hilbert-Schmidt kernels, that $K_{\varphi,\rho}$ indeed is the integral kernel of the commutator operator from (9.3.3.12) (explicitly, the convolution action of $K_{\varphi,\rho}$ on the Schwartz-Bruhat functions on $G$, valued in $L^2(G)$, agrees with that of the commutator operator from (9.3.3.12), and since both operators are Hilbert-Schmidt on $L^2(G)$, their integral kernels agree $(\mu_G \otimes \mu_G)$-almost everywhere on $G \times G$. One of them being already an integral operator with integral kernel $K_{\varphi,\rho}$, we obtain the desired identification of the Hilbert-Schmidt kernel.

When $\rho$ and $\varphi$ are smooth, see also [Tre, Part III,Ch.51,Cor.51.7], Corollary to [Tre, Part III,Ch.51,Thm.51.6], and Theorem C.2.4.19), noting that $K_{\varphi,\rho}$ maps from an element of $L^2((G)_x \times (G)_y)$ to the Schwartz kernel of the operator from (9.3.3.13) restricted to $\mathcal{S}(G)$ and valued in tempered distributions over $G$, as an element of $\mathcal{S}(G)'_{\beta} \widehat{\otimes}_{\pi} \mathcal{S}(G)'_{\beta}$.

As such, the given operator is Hilbert-Schmidt, and $K_{\varphi,\rho}$ is its Hilbert-Schmidt kernel. The function $K_{\varphi,\rho}$ is smooth over $G \times G$ away from a $(\mu_G \otimes \mu_G)$-negligible subset of the form

$$
(\bigcup_{1 \le k \le N}\{g \in G : \lvert g\rvert = t_k\}) \times (\bigcup_{1 \le k \le N}\{g \in G : \lvert g\rvert = t_k\})
$$

for $\{t_1,\dots,t_N\} \subset \mathbf{R}_{>0}$ a finite subset, and it is $(\mu_G \otimes \mu_G)$-integrable. In particular, the diagonal in $G_x \times G_y$ is contained in the Lebesgue set of $K_{\varphi,\rho}$, up to a subset of $\mu_G$-measure zero (see Theorem A.5.4.1 and Remark A.5.4.2). Along the diagonal in $(G)_x \times (G)_y$, the smoothening $\widetilde{K}_{\varphi,\rho}$ (in the sense of Theorem A.5.4.1 and [Bris-a, §3]; see also [Bris-a, §3.1,Thm.3.1]) vanishes $\mu_G$-almost everywhere. In fact, $K_{\varphi,\rho}$ is itself already defined $\mu_G$-almost everywhere along the diagonal at its points of continuity, a subset of the diagonal whose complement in the diagonal is $\mu_G$-negligible. Away from a $\mu_G$-negligible subset, $K_{\varphi,\rho}$ and $\widetilde{K}_{\varphi,\rho}$ agree. The operator from (9.3.3.13) is therefore an integral Hilbert-Schmidt operator whose kernel has an absolutely integrable smoothening along the diagonal, whose mass vanishes.

If both $\rho$ and $\varphi$ are smooth, then it is nuclear on $L^2(G)$ (because the kernel is smooth and compactly supported over $G \times G$, and hence an element of $\mathcal{S}(G) \widehat{\otimes}_{\pi} \mathcal{S}(G)$ (in fact an element of the smaller $\mathcal{S}(G) \overline{\otimes} \mathcal{S}(G)$, since $\varphi$ is contained in some $\mathcal{D}_K(G,k)$ for a compact subgroup $k \subset G$ with compactly generated orthogonal $k^{\perp}$, with $K \subset G$ a compact subset with non-empty interior, and $\mathcal{D}_K(G,k)$ is a Fréchet space), which therefore

## PDF page 431

**9.3. MODULE STRUCTURES OVER $\mathcal{D}(G)$ AND APPROXIMATE UNITS** · **431**

maps to $S_1(G) = L^2(G) \widehat{\otimes}_{\pi} L^2(G)$ by [Jar, ]) and by Lemma C.3.7.1(2) its trace vanishes by Lemma C.3.7.1(1) (see also [Bris-a, Cor.3.2]).

To show that the operator in (9.3.3.11) is an integral Hilbert-Schmidt operator whose kernel has an absolutely integrable smoothening along the diagonal, and, if $\rho$ and $\varphi$ are smooth, is nuclear, it is enough to show that its sum with the operator in (9.3.3.13) is. Such sum is the operator:

$$
\left(\int_G \varphi(g)\rho_0(g,\cdot)\,\mathrm{d}\mu_G(g)\right) \circ M_{\rho}: L^2(G) \to L^2(G). \tag{9.3.3.14}
$$

This is again a Hilbert-Schmidt operator whose integral kernel is:

$$
K'_{\varphi,\rho}(x,y) := \varphi(xy^{-1})\rho(y) \tag{9.3.3.15}
$$

whose smoothening is again integrable along the diagonal of $(G)_x \times (G)_y$. If $\rho$ and $\varphi$ are smooth, the same argument as in the foregoing implies nuclearity, and Lemma C.3.7.1(2) implies that the trace of the nuclear operator in (9.3.3.14) is computed by the integral of the smoothening of $K'_{\varphi,\rho}$ along the diagonal of $(G)_x \times (G)_y$ (see also [Bris-a, Cor.3.2], a generalization of Mercer's Theorem). It remains to perform the calculation. We choose a continuous homomorphic section $\tau$ to the module $\lvert\cdot\rvert_G$, and use the resulting isomorphism of Hausdorff locally compact abelian groups $\mathbf{R}_{>0} \times G^1 \simeq G$ through which $(\mathrm{d}t/t) \otimes \mu_1$ matches $\mu_G$. We rename the smoothening of $K'_{\varpi,\rho}$ as $K'_{\varphi,\rho}$, and we have:

$$
\int_G K'_{\varphi,\rho}(g,g)\,\mathrm{d}\mu_G(g) = \int_{\mathbf{R}_{>0}} \int_{G^1} K'_{\varphi,\rho}(\tau(t)g_0,\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\,\frac{\mathrm{d}t}{t} \tag{9.3.3.16}
$$

$$
= \int_{1/\Lambda}^{1/\Lambda+\varepsilon} \int_{G^1} K'_{\varphi,\rho}(\tau(t)g_0,\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\,\frac{\mathrm{d}t}{t} + \int_{\Lambda-\varepsilon}^{\Lambda} \int_{G^1} K'_{\varphi,\rho}(\tau(t)g_0,\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\,\frac{\mathrm{d}t}{t} \tag{9.3.3.17}
$$

$$
+ \int_{1/\Lambda+\varepsilon}^{\Lambda-\varepsilon} \int_{G^1} K'_{\varphi,\rho}(\tau(t)g_0,\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\,\frac{\mathrm{d}t}{t} \tag{9.3.3.18}
$$

$$
= \varphi(1) \int_{1/\Lambda}^{1/\Lambda+\varepsilon} \int_{G^1} \rho(\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\,\frac{\mathrm{d}t}{t} + \varphi(1) \int_{\Lambda-\varepsilon}^{\Lambda} \int_{G^1} \rho(\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\,\frac{\mathrm{d}t}{t} \tag{9.3.3.19}
$$

$$
+ \varphi(1) \int_{1/\Lambda+\varepsilon}^{\Lambda-\varepsilon} \left(\int_{G^1} \mathrm{d}\mu_1(g)\right)\frac{\mathrm{d}t}{t}. \tag{9.3.3.20}
$$

We have:

$$
\left\lvert\varphi(1) \int_{1/\Lambda}^{1/\Lambda+\varepsilon} \int_{G^1} \rho(\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\,\frac{\mathrm{d}t}{t} + \varphi(1) \int_{\Lambda-\varepsilon}^{\Lambda} \int_{G^1} \rho(\tau(t)g_0)\,\mathrm{d}\mu_1(g_0)\,\frac{\mathrm{d}t}{t}\right\rvert \le \lvert\varphi(1)\rvert \left\{\log\left(\frac{1/\Lambda+\varepsilon}{1/\Lambda}\right) + \log\left(\frac{\Lambda}{\Lambda-\varepsilon}\right)\right\} \tag{9.3.3.21}
$$

and:

$$
\varphi(1) \int_{1/\Lambda+\varepsilon}^{\Lambda-\varepsilon} \left(\int_{G^1} \mathrm{d}\mu_1(g)\right)\frac{\mathrm{d}t}{t} = \log\left(\frac{\Lambda-\varepsilon}{1/\Lambda+\varepsilon}\right)\mu_1(G^1)\varphi(1). \tag{9.3.3.22}
$$

Since, by assumption, $\varepsilon\Lambda = o(1)$ as $\Lambda \to +\infty$, we deduce that we have:

$$
\log\left(\frac{1/\Lambda+\varepsilon}{1/\Lambda}\right) + \log\left(\frac{\Lambda}{\Lambda-\varepsilon}\right) = o(1),\; \log\left(\frac{\Lambda-\varepsilon}{1/\Lambda+\varepsilon}\right) = 2\log(\Lambda) + o(1) \tag{9.3.3.23}
$$

as $\Lambda \to +\infty$, which shows that (9.3.3.9) holds. It remains to treat the case when $I$ does not contain $0$. We choose $b \in \mathbf{R}$ such that $b+I$ contains $0$. Then $\phi \mapsto \lvert\cdot\rvert^b_G \phi$ is a linear topological isomorphism $W^s_{b+I}(G) \to W^s_I(G)$

## PDF page 432

**432** · **CHAPTER 9. HARDY-SOBOLEV TOPOLOGIES**

compatible with the continuous left-translation action by $G$ up to twist by the quasi-character $\lvert\cdot\rvert^{-b}_G$, and since conjugation by linear topological isomorphisms preserves traces of nuclear operators, it is enough to compute the desired trace under the additional assumption $0 \in I$, since the value at $g=1$ of $\varphi$ and of $\lvert\cdot\rvert^{-b}_G \varphi$ is the same. $\square$
