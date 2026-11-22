## PDF page 433

**CHAPTER 10**

**Trace formula: Spectral Side**

10.1. Hardy-Sobolev topologies on $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))$ and $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ 434

10.1.1. Hardy-Sobolev completions of $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ and $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ 434

10.1.2. Fourier transform 437

10.2. Spectral Markushevich Bases 438

10.2.1. The $a$-line Spectral Markushevich Basis 439

10.2.1.1. The $a$-line basis 439

10.2.1.2. Basic properties of the $a$-line basis 443

10.2.2. Spectral Markushevich basis: the general case of a compact interval $I=[\alpha,\beta]$ 445

10.2.2.1. The Markushevich basis on the $I$-based strip 445

10.2.2.2. Basic properties of the Spectral Markushevich Basis on the $I$-based strip 446

10.3. Spectral Nuclearity 447

10.3.1. Spectral nuclearity: the case $I=\{0\}$ 448

10.3.2. Spectral nuclearity: the general case of compact intervals $I=[-\alpha,\alpha]$ 453

10.4. Trace formula: Spectral Side 455

10.4.1. Truncations 456

10.4.2. Spectral Side 458

10.4.2.1. $\varepsilon$-approximate Kernels 461

10.4.2.2. Spectral Side: convolution after projection 463

10.4.3. Spectral Kernels 464

10.4.3.1. Spectral kernels: the case $I=\{0\}$ 464

10.4.3.2. Spectral kernels: the general case of compact intervals $I=[-\alpha,\alpha]$ 471

**433**

## PDF page 434

**434** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

**10.1. Hardy-Sobolev topologies on $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))$ and $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$**

In this section we study the completions of the Hausdorff locally convex topological complex vector spaces $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))$, $\mathcal{S}_\mathrm{E}(C_F)$, $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$, $\mathcal{S}_I(J_{F,S})$ for $I$ a non-empty connected interval of the real line, with respect to the coarser normed topologies originating from the Sobolev norms on $\mathcal{S}_I(G)$ defined in (9.1.2.3) of Definition 9.1.2.1, for $G$ the choice of $\mathbf{R}_{>0}$-modulated group $G=C_F$, respectively $J_{F,S}$.

**10.1.1. Hardy-Sobolev completions of $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ and $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$.** Let $F$ be a number field, $a\in\mathbf{R}$ an arbitrary real number.

By Theorem 2.2.3.4 and Lemma 2.2.4.3, we have an injective $\mathbf{C}$-linear map:

$$
|\cdot|_F^a\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))\to C^\infty_{\mathrm{dir}}(C_F) \tag{10.1.1.1}
$$

where the leftmost $\mathbf{C}$-linear space is thought of as a function space on the idele class group, i.e. each of its elements $\phi=\Phi_F(f)$ for some $f\in\mathcal{S}(\mathbf{A}_F)$ with $f(0)=\widehat{f}(0)=0$, is the function $g\mapsto |g|_F^a\Phi_F(f)(g)$ of $g\in C_F$, and the rightmost space is the $\mathbf{C}$-linear space of those continuous functions on $C_F$ whose directional derivatives of any order along any continuous 1-parameter subgroup of $C_F$ exist and are continuous.

Such function is, by Lemma 2.2.4.3, smooth along any continuous 1-parameter subgroup, and decays more rapidly than any positive power of $e^{-|\log|g|_F|}$ as $|\log|g|_F|\to+\infty$.

We note that the Sobolev norms $\|\cdot\|_{s,2}$ and $\|\cdot\|_{I,s}$ are defined on the image of the injective linear operator in (10.1.1.1) for any real number $s\ge 0$ and any closed interval $I$ with non-empty interior, and induce Hausdorff normed topologies on the source of (10.1.1.1), coarser than the Hausdorff locally convex LF topology (see the First Structure Theorem, Theorem 5.2.1.1(1)) obtained by transport of structure from the case $a=0$.

In particular, every element in the image of (10.1.1.1) is also an element of $W_I^s(C_F)$. We therefore obtain an injective linear map:

$$
|\cdot|_F^a\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))\to W_I^s(C_F) \tag{10.1.1.2}
$$

equivariant with respect to the continuous left-translation action by $C_F$ on the source (sending $(g,|\cdot|_F^a\phi)$ to $|g|_F^{-a}\rho_F(g,\phi)$) and on the target.

DEFINITION 10.1.1.1 (Hardy-Sobolev spaces of global adelic $\theta$-functions). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We define:

(1) for $a\in\mathbf{R}$ a real number, $I\subset\mathbf{R}$ a compact non-empty interval, $s\ge 0$ a real number:

$$
W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))\subset W_I^s(C_F) \tag{10.1.1.3}
$$

to be the closure of $|\cdot|_F^a\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ in $W_I^s(C_F)$. We refer to it as the *Hardy-Sobolev completion of $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ along the $a$-line.*

(2) For $a\in\mathbf{R}_{>0}$ a real number, $I=[\alpha,\beta]\subset\mathbf{R}$ a compact non-empty interval, $s\ge 0$ a real number:

$$
W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S})) \tag{10.1.1.4}
$$

to be the normed completion of $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ with respect to the normed topology defined by the norm assigned by, for every $\phi\in\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$:

$$
\|\phi\|_{a,I,s}:=\left(\int_{J_{F,S}}|\phi(g)|^2\max\{|g|_{F,S}^{2a+2\alpha},|g|_{F,S}^{2a+2\beta}\}(1+|\log|g|_{F,S}|^2)^{s/2}\,\mathrm{d}\bar\mu_S(g)\right)^{1/2}. \tag{10.1.1.5}
$$

We refer to it as the *Sobolev completion of $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ along the $a$-line.*

REMARK 10.1.1.2. We observe that by Proposition 2.4.3.1, the integral in (10.1.1.5) converges. We further caution the reader that while the continuous left-translation action of $C_F$ on $W_I^s(C_F)$ induces on $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ the action $(g,\phi)\mapsto |g|_F^{-a}\rho_F(g,\phi)$, with $\rho_F$ the continuous left-translation action

## PDF page 435

**10.1. HARDY-SOBOLEV TOPOLOGIES ON $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))$ AND $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$** · **435**

induced by left-translation on the global adelic $\theta$-functions, the continuous left-translation action of $J_{F,S}$ on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ extends by continuity to the $W_{a,I}^s$-completion: it will be related to the action inherited from $\mathcal{S}_{-a+(0,+\infty)}(J_{F,S})$ by multiplication by $|\cdot|_{F,S}^{-a}$.$^1$

In this subsection and the next, we collect basic properties of the completions $W_a^{s,2}\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ and $W_a^{s,2}\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$, and discuss continuity of the Fourier transform: specifically, we will see that the only real number $a$ for which the Fourier transform $\mathcal{F}$ defined in Theorem 5.2.4.1 on $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))$ (and hence on $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$) and on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$, extends to a continuous linear operator on the Sobolev completions from Definition 10.1.1.1, is $a=1/2$.

LEMMA 10.1.1.3. *Let $F$ be a number field, $s\ge 0$ a real number, $a\in\mathbf{R}$ a real number. Let $I\subset\mathbf{R}$ be a compact non-empty interval.*

*The subspace topology on $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ inherited from $W_I^s(C_F)$ is the norm-topology induced by the norm on $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$, continuous with respect to the Hausdorff locally convex topology on $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$, defined as:*

$$
\|\Phi_F(f)\|_{a,I,s}:=\left(\int_{C_F}|\Phi_F(f)(g)|^2\max\{|g|_F^{2a+2\alpha},|g|_F^{2a+2\beta}\}(1+|\log|g|_F|^2)^{s/2}\,\mathrm{d}\bar\mu_1(g)\right)^{1/2}. \tag{10.1.1.6}
$$

*We have:*

*(1) $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ is a separable Hilbert space, closed within $W_I^s(C_F)$.*

*(2) The continuous left-translation action of $C_F$ on $W_I^s(C_F)$ preserves $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ and restricts to the continuous left-translation action of $C_F$ on $|\cdot|_F^a\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ induced by the continuous left-translation action of $\mathrm{GL}_1(\mathbf{A}_F)$ on $\mathcal{S}_0(\mathbf{A}_F)$.*

PROOF. Since $C_F$ is second-countable, $W_I^s(C_F)$ is a separable Hilbert space by Lemma 9.1.1.2$^2$, applied to $G=\widehat{C_F}$, $\mu:=\widehat{\bar\mu_1}$. Since $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ is closed in $W_I^s(C_F)$, it is itself a separable Hilbert space, and the normed topology on it is induced by the norm $\|\cdot\|_{I,s}$ on the ambient, which gives (10.1.1.6). $\square$

Recall that we have denoted the continuous left-translation action of $\mathrm{GL}_1(\mathbf{A}_{F,S})$ on $\mathbf{A}_{F,S}$ by $\rho_{F,S}:\mathrm{GL}_1(\mathbf{A}_{F,S})\times\mathbf{A}_{F,S}\to\mathbf{A}_{F,S}$.

We denote, for each real number $s\ge 0$ and real number $a\in\mathbf{R}_{>0}$, for any compact non-empty interval $I=[\alpha,\beta]\subset\mathbf{R}$, by $\mu_{I,s}$ the Borel measure on $\mathrm{GL}_1(\mathbf{A}_{F,S})$:

$$
\mu_{I,s}:=\max\{|\cdot|_{F,S}^{2\alpha},|g|_{F,S}^{2\beta}\}(1+|\log|\cdot|_{F,S}|^2)^{s/2}\,\mu_S
$$

where $\mu_S$ is the multiplicative $S$-local Tamagawa measure on $\mathrm{GL}_1(\mathbf{A}_{F,S})$ from (A.3.4.2).

We note that in light of Theorem 2.4.2.1 and Proposition 2.3.1.2(2), $|\cdot|_{F,S}^a\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ is a linear subspace of $W_{-a+(0,+\infty)}^s(J_{F,S})$ for any real number $s\ge 0$ and any real number $a>0$, and hence of $W_I^s(J_{F,S})$ for any $I$ contained in $-a+(0,+\infty)$.

LEMMA 10.1.1.4. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $s\ge 0$ be a real number, $a\in\mathbf{R}_{>0}$ a real number. Then:*

*(1) $\mu_{I,s}$ is a regular Radon measure on $\mathrm{GL}_1(\mathbf{A}_{F,S})$ invariant under the left-translation action of $\mathcal{O}_{F,S}^\times$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})$.*

*(2) For any compact interval $I=[\alpha,\beta]\subset(0,+\infty)$, the subspace topology on $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ inherited from $W_I^s(J_{F,S})$ is the norm-topology induced by the norm on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$, continuous*

---

$^1$Return here.

$^2$Return here.

## PDF page 436

**436** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

*with respect to the Hausdorff locally convex topology on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$, defined as:*

$$
\|\Phi_{F,S}(f)\|_{a,I,s}:=\left(\int_{J_{F,S}}|\Phi_{F,S}(f)(g)|^2\max\{|g|_{F,S}^{2a+2\alpha},|g|_{F,S}^{2a+2\beta}\}(1+|\log|g|_{F,S}|^2)^{s/2}\,\mathrm{d}\bar\mu_{S,1}(g)\right)^{1/2}. \tag{10.1.1.7}
$$

*(3) $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ is a separable Hilbert space, closed within $W_I^s(J_{F,S})$.*

*(4) The continuous left-translation action of $J_{F,S}$ on $W_I^s(J_{F,S})$ preserves $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ and restricts to the continuous left-translation action of $J_{F,S}$ on $|\cdot|_{F,S}^a\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ induced by the continuous left-translation action of $\mathrm{GL}_1(\mathbf{A}_{F,S})$ on $\mathcal{S}(\mathbf{A}_{F,S})$ multiplied by the effect of left-translation on the quasi-character $|\cdot|_{F,S}^a$.*

PROOF. (1) : The function of $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$:

$$
\alpha_{I,s}(g):=\max\{|g|_{F,S}^{2\alpha},|g|_{F,S}^{2\beta}\}(1+|\log|g|_{F,S}|^2)^{s/2}
$$

is continuous over $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and vanishes at infinity. It follows that $\alpha_{I,s}\,\mu_S$ is a Radon measure on $\mathrm{GL}_1(\mathbf{A}_{F,S})$, and being $\mathrm{GL}_1(\mathbf{A}_{F,S})$ second-countable, by [**Fol**, Thm.7.8] $\mu_{I,s}$ is regular. Invariance under the left-translation action of $\mathcal{O}_{F,S}^\times$ follows from invariance of $|\cdot|_{F,S}$.

(2), (3) and (4) are a consequence of the definition of $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ from (10.1.1.5) and separability of $W_I^s(J_{F,S})$, which follows from Lemma 9.1.1.2$^3$, since $J_{F,S}$ is a second-countable $\mathbf{R}_{>0}$-modulated group. $\square$

We denote by:

$$
\langle\cdot,\cdot\rangle_{L^2(\mathrm{GL}_1(\mathbf{A}_{F,S}),\mu_{I,s})}:L^2(\mathrm{GL}_1(\mathbf{A}_{F,S}),\mu_{I,s})\times L^2(\mathrm{GL}_1(\mathbf{A}_{F,S}),\mu_{I,s})\to\mathbf{C}
$$

the pairing:

$$
\langle\phi,\psi\rangle_{L^2(\mathrm{GL}_1(\mathbf{A}_{F,S}),\mu_{I,s})}=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}\phi(g)\overline{\psi(g)}\,\mathrm{d}\mu_{I,s}(g)
$$

inducing the $L^2$-norm topology on $L^2(\mathrm{GL}_1(\mathbf{A}_{F,S}),\mu_{I,s})$.

We now discuss isotypes of $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ and $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$ under the continuous left-translation action of $C_F^1$, respectively $J_{F,S}^1$.

PROPOSITION 10.1.1.5. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places. Let $s\ge 0$ be a real number, $a,b\in\mathbf{R}$ real numbers, $b>0$. Let $I\subset\mathbf{R}$ be a compact non-empty interval.*

*Let $\omega$ be a continuous character of $C_F^1$, respectively of $J_{F,S}^1$.*

*(1) The integrals:*

$$
P_{F,\omega}:=\int_{C_F^1}\overline{\omega(g)}\rho_F(g,\cdot)\,\mathrm{d}\bar\mu_1(g) \tag{10.1.1.8}
$$

*and, upon assuming $I\subset\mathbf{R}_{>0}$:*

$$
P_{F,S,\omega}:=\int_{J_{F,S}^1}\overline{\omega(g)}\rho_{F,S}(g,\cdot)\,\mathrm{d}\bar\mu_{S,1}(g) \tag{10.1.1.9}
$$

*exist in the sense of Pettis, and define surjective open continuous linear operators:*

$$
P_{F,\omega}:W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))\to W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))(\omega) \tag{10.1.1.10}
$$

*and, upon assuming $I\subset\mathbf{R}_{>0}$:*

$$
P_{F,S,\omega}:W_{b,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))\to W_{b,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))(\omega) \tag{10.1.1.11}
$$

---

$^3$Return here.

## PDF page 437

**10.1. HARDY-SOBOLEV TOPOLOGIES ON $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))$ AND $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$** · **437**

*inducing linear topological isomorphisms:*

$$
P_{F,\omega}:W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\omega,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))\to W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))(\omega) \tag{10.1.1.12}
$$

*and, upon assuming $I\subset\mathbf{R}_{>0}$:*

$$
P_{F,S,\omega}:W_{b,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\omega,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))\to W_{b,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))(\omega). \tag{10.1.1.13}
$$

*(2) The induced continuous linear operators:*

$$
P_F:W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))\to\prod_{\omega\in\widehat{C_F^1}}W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\omega,\mathcal{S}(\mathbf{A}_F)) \tag{10.1.1.14}
$$

*and, upon assuming $I\subset\mathbf{R}_{>0}$:*

$$
P_{F,S}:W_{b,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))\to\prod_{\omega\in\widehat{J_{F,S}^1}}W_{b,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(\omega,\mathcal{S}(\mathbf{A}_{F,S})) \tag{10.1.1.15}
$$

*to the Hausdorff locally convex products, are continuous and injective, and factor through surjective isometries onto the respective Hilbert sums.*

Proposition 10.1.1.5 is a direct consequence of the same argument provided for Proposition 5.2.3.2, upon observing that the actions $\rho_F$ and $\rho_{F,S}$ are continuous with respect to the respective Sobolev topologies, and upon inspection of the definition of Hilbert sum (see §4.3.2 and specifically the proof of Lemma 4.3.2.2).$^4$

**10.1.2. Fourier transform.** In this subsection we study the continuity of the global and $S$-local Fourier transforms with respect to the Sobolev topologies on $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}(\mathbf{A}_F))$, respectively $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^\times,\mathcal{S}(\mathbf{A}_{F,S}))$.

THEOREM 10.1.2.1 (Fourier transform on Hardy-Sobolev spaces of global adelic $\theta$-functions). *Let $F$ be a number field, $s\ge 0$ a real number, $a\in\mathbf{R}$ a complex number. Let $I\subset\mathbf{R}$ a compact non-empty interval. The continuous linear automorphism $J:W_I^s(C_F)\to W_I^s(C_F)$ induced by inversion on $C_F$, induces a continuous linear isometry:*

$$
J:W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))\to W_{1-a-I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F)) \tag{10.1.2.1}
$$

*compatible with passage to $C_F^1$-isotypes.*

*Assume $I=[-\alpha,\alpha]$ for some real number $\alpha\ge 0$. The following conditions on $a$ are equivalent:*

*(1) Fourier transform $\mathcal{F}$ on $\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ defined in (5.2.4.3), induces a unique continuous linear automorphism $\mathcal{F}$ of $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ making the following diagram of continuous linear operators:*

(10.1.2.2)

```latex
\begin{tikzcd}
\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F)) \arrow[r, "E_{a,I}"] \arrow[d, "\mathcal{F}"'] & W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F)) \arrow[d, "\mathcal{F}"] \\
\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F)) \arrow[r, "E_{a,I}"'] & W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))
\end{tikzcd}
```

*commute, where $E_{a,I}$ is the operator sending $\phi\in\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$ to the continuous function*

$$
E_{a,I}(\phi):g\mapsto |g|_F^a\phi(g) \tag{10.1.2.3}
$$

*of $g\in C_F$ as an element of $W_{a,I}^s\,\mathrm{H}_{0,\mathrm{cont}}(F^\times,\mathcal{S}_0(\mathbf{A}_F))$.*

*(2) $a=1/2$.*

PROOF. We denote by $J:W_I^s(C_F)\to W_I^s(C_F)$ the continuous isometric automorphism uniquely determined by the continuous linear automorphism $J:\mathcal{S}(C_F)\to\mathcal{S}(C_F)$ defined by sending $\phi\in\mathcal{S}(C_F)$ to $(J\phi)(g^{-1})$, a Schwartz-Bruhat function of $g\in C_F$.

---

$^4$Return here.

## PDF page 438

**438** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

Since the Sobolev weight $w=\max\{|g|^{2\alpha}_F,|g|^{-2\alpha}_F\}(1+|\log|\cdot|_F|^2)^{s/2}$ is invariant under inversion on $C_F$, and so is the Haar measure $\overline{\mu}_1$, $J$ is indeed norm-preserving on $W^s_I(C_F)$, and hence induces a continuous isometric automorphism on $W^s_I(C_F)$.

We observe, as a consequence of Theorem 2.2.3.2, that we have the following identity, as elements of $\mathcal S(C_F)$:

$$
E_{a,I}(\mathcal F(\phi))=JE_{1-a,I}(\phi) \tag{10.1.2.4}
$$

from which we deduce that $J$ completes the following diagram of continuous linear operators:

(10.1.2.5)

```latex
\begin{tikzcd}
\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F)) \arrow[r, "E_{1-a,I}"] \arrow[d, "\mathcal F"'] & W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F)) \arrow[d, "J"] \\
\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F)) \arrow[r, "E_{a,I}"'] & W^s_{1-a,I}\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))
\end{tikzcd}
```

rendering it commutative.

(1) : Since $|\cdot|^z_F$ is a bounded multiplier on $W^s_I(C_F)$ if and only if $\mathrm{Re}(z)=0$ $^{5}$, we deduce from (10.1.2.4) that continuity of $\mathcal F$ in the $||\cdot||_{a,I}$ is equivalent to $a=1/2$, in which case we may define $\mathcal F:=J$. From commutativity of (10.1.2.5) we deduce that (10.1.2.2) commutes with this choice of $\mathcal F$ on $W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))$.

(2) : If $a=1/2$, then the definition $\mathcal F:=J$, indeed provides a continuous linear automorphism on $W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))$ making the diagram in (10.1.2.2) commute, so long as $I=-I$, which holds since $I=[-\alpha,\alpha]$ for a real number $\alpha\ge 0$. $\square$

We refer the reader to Proposition 5.4.2.1 and the discussion preceding the Proposition, for a discussion on the extension by continuity of the $S$-local Fourier transform on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, to the $L^2$-completion

$$
L^2\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))=W^0_{\{1/2\}}\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})) \tag{10.1.2.6}
$$

(the equal sign denoting the surjective isometry sending the element $\phi$ to $|\cdot|^{1/2}_{F,S}\phi$) ultimately a consequence of the fact (see Theorem 3.3.1.5(2)) that $\rho_S(c)$ from (3.3.1.3) is, when restricted to the relative vertical line $\sigma(c)=1/2$, valued in $\mathrm U(1)$.

**10.2. Spectral Markushevich Bases**

We recall that for a complete Hausdorff locally convex topological $\mathbf C$-vector space $E$ with a Schauder basis $\{x_m\}_{m\ge 0}$, and $\{f_m\}_{m\ge 0}$ the bi-orthogonal sequence in $E'$, then if $E$ is semi-reflexive, $\{f_m\}_{m\ge 0}$ is also a Schauder basis (see [Jar, Part II,Ch.14,§14.5,Thm.1(a),p.302]), and the datum $\{(x_m,f_m)\}_{m\ge 0}$ is a Markushevich basis.

Being a Schauder basis is an unstable property with respect to coarsening of the Hausdorff locally convex topology. The reader may consider the example of the exponential system on $\mathcal S(\mathbf T)=C^\infty(\mathbf T)$, with $\mathbf T:=\mathbf R/\mathbf Z$ the circle group, which is an absolute Schauder basis with respect to the topology of uniform convergence on functions and their derivatives of arbitrary order, but is not a Schauder basis on $L^1(\mathbf T):=L^1(\mathbf T,\mu)$, $\mu$ being the volume-1 Haar measure on $\mathbf T$.

It is, however, a Markushevich basis. The property that is lost under coarsening of the Hausdorff locally convex topology from $\mathcal S(\mathbf T)$ to $L^1(\mathbf T)$ is that of the simple convergence of the finite rank basis projections.

We let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\chi$ be a continuous character of $C_F$, respectively of $J_{F,S}$.

In the remaining sections of this Chapter, we analyze to what extent the Schauder bases constructed in the previous Chapter with respect to the strong topology on the Hausdorff locally convex space $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S(\mathbf A_F))$

---
$^5$Return here.

## PDF page 439

**10.2. SPECTRAL MARKUSHEVICH BASES** · **439**

and its subquotients, and on $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ and its orbital subquotients, remain bases with respect to the coarser Sobolev topologies introduced in Definition 10.1.1.1.

**10.2.1. The $a$-line Spectral Markushevich Basis.** In the special case the compact non-empty interval $I\subset\mathbf R$ from the definition of the Hardy-Sobolev spaces $W^s_I(C_F)$ is of the form $I=\{0\}$, we have

$$
W^s_I(C_F)=W^{s,2}(C_F)
$$

for any real number $s\ge 0$. In this special case, we denote the Hardy-Sobolev completion on the $a$-line of the space of global adelic $\theta$-functions by:

$$
W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))=W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)).
$$

In this section, we consider the linear topological extension:

$$
0\to W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))\to W^{s,2}(C_F)(\chi|_{C^1_F})\to\mathscr H^s_{F,a}(\chi|_{C^1_F})\to 0
$$

where $\mathscr H^s_{F,a}(\chi|_{C^1_F})$ is the normed completion of $\mathscr H_{F,a}(\chi|_{C^1_F})$ in Sobolev degree $s\ge 0$, where $\mathscr H_{F,a}(\chi|_{C^1_F})$ is defined as the quotient nuclear Fréchet space:

$$
\mathscr H_{F,a}(\chi|_{C^1_F}):=\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/|\cdot|^a_F\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))
$$

where multiplication by the quasi-character $|\cdot|^a_F$, a linear topological automorphism on $\mathcal{S}_{\mathrm{E}}(C_F)$ and $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$, is isomorphic to a horizontal translation by $a$ to the left on the Mellin transforms of the elements of $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

We further refer the reader to (7.1.4.7) for the case $a=0$.

Equivalently, by the Open Mapping Theorem, the quotient of the normed completion $W^{s,2}(C_F)(\chi|_{C^1_F})$ of $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$ by the closure of $|\cdot|^a_F\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

We will be computing the nuclear traces of nuclear operators induced on the rightmost Hilbert space $\mathscr H^s_{F,a}(\chi|_{C^1_F})$, given by the operators $A(\varphi)$ from (9.3.1.2), for any $\varphi\in\mathcal D(C_F)$.

The methods and results discussed in this section build on [Co, §III,pp.9-13] and [Co, Appendix I,pp.63-68], and, in particular, rework the spectral interpretation to a subset of the zeros of the Hecke $L$-function $L(s,\chi)$ using the continuous left-translation action of $C_F$ on $\mathscr H^s_{F,a}(\chi|_{C^1_F})$.

We will be discussing the spectral interpretation to such subsets of the zeros of the Hecke $L$-function $L(s,\chi)$ already provided in [Co, §III,Thm.1,p.13] and [Co, §III,Cor.2,p.14], reworking it through the lens of the Schatten-von Neumann convergence of sequences of certain explicit finite rank operators on $\mathscr H^s_{F,a}(\chi|_{C^1_F})$ provided by Markushevich bases of point-evaluation functionals supported at the ordinates of the zeros on the $a$-line.

In [Co, §III,p.13,14], the case $a=1/2$ is discussed and the Sobolev space $\mathscr H^s_{F,1/2}(\chi|_{C^1_F})$ is denoted by $\mathcal H_\chi$, with the infinitesimal generator of the continuous left-translation action by $C_F$, which factors through $C_F/C^1_F\simeq\mathbf R_{>0}$, being denoted by $D_\chi$ (see [Co, §III,(27),p.14]).

The Sobolev degree $s$ is denoted by $\delta$ in [Co, §III,Thm.1,p.13].

10.2.1.1. *The $a$-line basis.* Let $a\in\mathbf R$ be a complex number, $s\ge 0$ a real number. We define:

$$
\mathscr H^s_{F,a}:=W^{s,2}(C_F)/W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F)). \tag{10.2.1.1}
$$

For every $\omega\in\widehat{C^1_F}$, we will be writing $\mathscr H^s_{F,a}(\omega)$ for its $\omega$-isotype, which is isometric to the quotient:

$$
\mathscr H^s_{F,a}(\omega):=W^{s,2}(C_F)(\omega)/W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F)) \tag{10.2.1.2}
$$

by the Open Mapping Theorem (and an application of Lemma 4.3.3.1).

We recall that we denoted the pairing $\langle\cdot,\cdot\rangle_{s,w}$ from (9.1.1.11) by:

$$
\langle\cdot,\cdot\rangle_{s,2}:W^{s,2}(C_F)\times W^{-s,2}(C_F)\to\mathbf C \tag{10.2.1.3}
$$

## PDF page 440

**440** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

where $\langle\cdot,\cdot\rangle_{s,2}$ is assigned by:

$$
\langle\phi,\psi\rangle_{s,2}:=\int_{C_F}\phi(g)\psi(g)\,\mathrm{d}\overline{\mu}(g).
$$

The duality pairing $\langle\cdot,\cdot\rangle_{s,2}$ further identifies, by [NB, Thm.8.12.4(b)], the continuous dual $(\mathscr H^s_{F,a})'$ of the quotient $\mathscr H^s_{F,a}$ with the orthogonal in the sense of [NB, Def.8.9.1] of $W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))$.

We note that the pairing $\langle\cdot,\cdot\rangle_{s,2}$ respects $C^1_F$-isotypes, i.e. it induces a non-degenerate duality pairing:

$$
\langle\cdot,\cdot\rangle_{s,2}:W^{s,2}(C_F)(\omega)\times W^{-s,2}(C_F)(\overline{\omega})\to\mathbf C
$$

by invariance of the Haar measure $\overline{\mu}$ on $C_F$.

Notation 10.2.1.1. Throughout, we fix a choice of holomorphic parametrization for $\Omega(C_F)$. This amounts to choosing, for every $\omega\in\widehat{C^1_F}$, a continuous unitary character $\chi\in\widehat{C_F}$, and parametrize every point of $\Omega(C_F)(\omega)$, the fibre of $\Omega(C_F)$ over $\omega\in\widehat{C^1_F}$, the discrete parameter space of connected components of $\Omega(C_F)$, as:

$$
\chi|\cdot|^z_F,\quad z\in\mathbf C. \tag{10.2.1.4}
$$

We will be denoting by $\widetilde{C^1_F}\subset\widehat{C_F}$ the chosen set of base-points for the connected components of $\Omega(C_F)$.

We will be writing $\sum'_{\omega\in\widehat{C^1_F}}$ to denote the sum of $\mathbf C$-valued functions depending on $\chi$ (such as countable sums of $M(\varphi)(\chi|\cdot|^{it}_F)$ for $t\in\mathbf R$ varying over a suitable discrete subset, for $\varphi\in\mathcal D(C_F)$ fixed, and interpreting the value of the sum as a function of $\chi$), to mean the sum indexed by the choices $\{\chi\in\widehat{C_F}\}$ lifting each point $\omega\in\widehat{C^1_F}$, choices which we fixed at the outset when parametrizing $\Omega(C_F)$ as $\chi|\cdot|^z_F$, $z\in\mathbf C$.

Theorem 10.2.1.1 ($a$-line Spectral Markushevich Basis). *Let $F$ be a number field, $s,a\in\mathbf R$ real numbers, $s>1$. The functions:*

$$
\eta_{\chi,t,m}(g):=\chi(g)|g|^{it}_F(\log|g|_F)^m \tag{10.2.1.5}
$$

such that:

(1) *for $t\in\mathbf R$ such that $\rho_{\chi,t}:=\chi|\cdot|^{a+it}_F$ is a zero of $L(s,\chi)$ of multiplicity $N(\rho_{\chi,t})$.*

(2) $m\ge 0$ is an integer satisfying $m\le N_s(\rho_{\chi,t})-1$ with:

$$
N_s(\rho_{\chi,t})=\min\left\{N(\rho_{\chi,t}),\left[\frac{s-1}{2}+1\right]\right\} \tag{10.2.1.6}
$$

*are elements of $W^{-s,2}(C_F)$, any enumeration admits a bi-orthogonal sequence, and the resulting sequence of pairs is a Markushevich basis for $\mathscr H^s_{F,a}$, for the image of $(\mathscr H^s_{F,a})'_\beta$ in $W^{-s,2}(C_F)$ under $T_s$ from (9.1.2.14), and with respect to the duality pairing $\langle\cdot,\cdot\rangle_{s,2}$ from (10.2.1.3).*

Terminology 10.2.1.1 ($a$-line Spectral Markushevich Basis). We refer to any sequence of pairs

$$
\{(\psi_m,u_m)\}_{m\ge 0}\subset\mathscr H^s_{F,a}\times T_s((\mathscr H^s_{F,a})'_\beta)
$$

obtained from a choice of enumeration of the elements from (10.2.1.5) of $W^{-s,2}(C_F)$ and their bi-orthogonal sequence, as the $a$-line Spectral Markushevich Basis.

Remark 10.2.1.2 (On Markushevich Bases). Since, by [Jar, Part II,Ch.14,§14.1,Prop.2,p.290], bi-orthogonal sequences are unique, for a Markushevich basis $\{(x_m,f_m)\}_{m\ge 0}$ for the duality $\langle E,E'\rangle$ with $E$ a Hausdorff locally convex topological $\mathbf C$-vector space, we will be omitting either $\{x_m\}_{m\ge 0}$ or $\{f_m\}_{m\ge 0}$ from the notation, referring to the former as a Markushevich basis for $E$, and to the latter as a Markushevich basis for $E'_\sigma$. If $E$ is a Hilbert space, then so is $E'_\beta$, and then $\{f_m\}_{m\ge 0}$ linearly generates a subspace of $E'$ which is dense in the strong topology too, by [Jar, Part II,Ch.8,§8.2,Prop.1,p.149] and reflexivity. The

## PDF page 441

**10.2. SPECTRAL MARKUSHEVICH BASES** · **441**

sequence $\{x_m\}_{m\ge 0}$ linearly generates a $\sigma(E,E')$-dense subspace, which is, by the same token, dense with respect to the intrinsic topology on $E$.

Markushevich bases throughout this work will only be with respect to Hilbert normed topologies, and we will therefore be making no distinction between strong and weak denseness of the linear spans of the basis elements.

Proof of Theorem 10.2.1.1. Let $\omega\in\widehat{C^1_F}$ be a unitary character, and $\chi\in\widehat{C_F}$ a unitary character such that $\chi|_{C^1_F}=\omega$. We choose a continuous homomorphic section $\tau$ to the idelic norm, and identify $C_F/C^1_F$ with $\mathbf R_{>0}$ as a Hausdorff locally compact abelian group, by means of $|\cdot|_F$.

The following diagram:

(10.2.1.7)

```latex
\begin{tikzcd}
\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F)) \arrow[d] & \times & \mathcal{S}_{\mathrm{E}}(C_F)(\omega)'_\beta \arrow[r] & \mathbf C \arrow[d, equal] \\
W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F)) & \times & W^{-s,2}(C_F)(\omega) \arrow[u] \arrow[r] & \mathbf C
\end{tikzcd}
```

is commutative, where the top horizontal arrow is the duality pairing $\langle\cdot,\cdot\rangle_{\mathcal{S}_{\mathrm{E}}(C_F)(\omega),\mathcal{S}_{\mathrm{E}}(C_F)(\omega)'_\beta}$, noting that by Theorem 6.3.2.1, $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))$ is closed as a subspace of $\mathcal{S}_{\mathrm{E}}(C_F)(\omega)$, where $\mathcal{S}_{\mathrm{E}}(C_F)(\omega)$ is the $\mathbf C$-linear subspace of the space $\mathcal S(\mathbf R_{>0})$ of Schwartz-Bruhat functions on $\mathbf R_{>0}$ with exponential decay (see Definition D.3.3.1, Lemma D.3.2.7 and Theorem D.3.3.7. Its topology is equivalent to the Hausdorff locally convex topology induced by transport of structure under pull-back along a choice of continuous homomorphic section $\tau$ to the idelic norm, by the countable family of seminorms:

$$
p_{m,n}(f):=\sup_{t\in\mathbf R_{>0}}|e^{-m|\log(t)|}(t\partial_t)^nf(t)|,\quad (m,n)\in\mathbf N^2
$$

on $\mathcal{S}_{\mathrm{E}}(\mathbf R_{>0})$).

The bottom horizontal arrow in (10.2.1.7) is the duality pairing $\langle\cdot,\cdot\rangle_{s,2}:W^{s,2}(C_F)\times W^{-s,2}(C_F)\to\mathbf C$ from (10.2.1.3).

The leftmost vertical arrow is the completion map, and the arrow $W^{-s,2}(C_F)(\omega)\to \mathcal{S}_{\mathrm{E}}(C_F)(\omega)'_\beta$ is the continuous linear operator induced as the continuous adjoint of the completion map

$$
\mathcal S(C_F)(\omega)\to W^{s,2}(C_F)(\omega).
$$



As a consequence of commutativity of (10.2.1.7), we obtain a continuous linear map:

$$
(\mathscr H^s_{F,a}(\omega))'_\beta\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))^\perp \tag{10.2.1.8}
$$

where the orthogonal $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))^\perp$ within $\mathcal{S}_{\mathrm{E}}(C_F)(\omega)'_\beta$ is being formed with respect to the duality $\langle \mathcal{S}_{\mathrm{E}}(C_F)(\omega),\mathcal{S}_{\mathrm{E}}(C_F)(\omega)'_\beta\rangle$.

Since $\mathcal{S}_{\mathrm{E}}(C_F)(\omega)$ is linearly and topologically isomorphic to $A\mathcal S(\mathbf C)$ under the Mellin transform $\phi\mapsto M(\phi)(s):=\int_{\mathbf R_{>0}}\phi(t)t^s\frac{\mathrm{d}t}{t}$ pre-composed with the linear topological isomorphism induced by pull-back under a fixed choice of continuous homomorphic section $\tau$ to the idelic norm, and $M$ restricts to $L$ from (5.1.1.4) on $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ up to a vertical translation on the complex $s$-plane (We further refer the reader to Discussion 4.4.1.1. For $\chi\in\widehat{C_F}$ chosen according to our choice of holomorphic parametrization of $\Omega(C_F)$, and for any $f\in\mathcal S_0(\mathbf A_F)$, we have, for $x_0\in\mathbf R$ the unique real number such that $\chi(\tau(t))=t^{ix_0}$ as smooth functions on $\mathbf R_{>0}$:

$$
M(\Phi_{F,\chi|_{C^1_F}}(f)(\tau(t)))(s+ix_0)=Z(f,\chi|\cdot|^s_F)
$$

as entire functions on the complex $s$-plane, Schwartz uniformly on the open vertical strips of bounded width) then by Theorem 6.3.2.1 we obtain that $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))^\perp$ is linearly isomorphic to $(((s+a)(s+a-1))^{\delta_\chi}L(a+s,\chi)\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C))^\perp$ within $A\mathcal S(\mathbf C)'_\beta$, for $\delta_\chi=0$ for $\chi|_{C^1_F}\ne 1$, and $\delta_\chi=1$ for $\chi|_{C^1_F}=1$, which in

## PDF page 442

**442** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

turn contains

$$
\bigoplus_{\rho:L(a+\rho,\chi)=0}U(J_{a+\rho})
$$

as a dense linear subspace, where $J_{a+\rho}$ was defined in (7.1.4.3).

We note that $U(J_{a+\rho})$ is in the image of (10.2.1.8) if and only if $\rho\in i\mathbf R$, since otherwise the functionals $U(\delta^{(m)}_{a+\rho})$ are discontinuous with respect to the Sobolev topology on $W^{s,2}(C_F)$, since multiplication by a quasi-character of nonzero exponent is a discontinuous linear operator on $W^{s,2}(C_F)$ (valued in $\overline{\mu}$-measurable functions on $C_F$. It is only valued in $W^{s,2}(C_F)$ if and only if the exponent of the quasi-character is zero. In which case such multiplication operator is a linear topological automorphism on $W^{s,2}(C_F)$, preserving $C^1_F$-isotypes).

Explicitly, the element $U(\delta^{(m)}_{a+it})$ is the image of the continuous linear functional on $W^{s,2}(C_F)(\omega)$:

$$
D^m_t:\phi\mapsto\int_{C_F}\phi(g)\chi(g)|g|^{it}_F(\log|g|_F)^m\,\mathrm{d}\overline{\mu}(g)=\int_{C_F}\phi(g)\eta_{\chi,t,m}(g)\,\mathrm{d}\overline{\mu}(g) \tag{10.2.1.9}
$$

so long as $0\le m\le N_s(\rho_{\chi,t})-1$ (by Proposition 9.1.2.5).

Since both $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))$ and $\mathcal{S}_{\mathrm{E}}(C_F)(\omega)$ have dense image in $W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))$, respectively $W^{s,2}(C_F)(\omega)$, then the induced continuous linear operator from (10.2.1.8) is injective.

Since the strong topology on $(\mathscr H^s_{F,a}(\omega))'_\beta$ is finer than the strong topology on the continuous dual of the nuclear Fréchet space $\mathscr H_F(\omega)=\mathcal{S}_{\mathrm{E}}(C_F)(\omega)/\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))$ from Theorem 7.1.4.2, then, since the countable set of continuous functionals $U(\delta^{(m)}_\rho)$ on such quotient is topologically free by Theorem 6.3.2.1(3), so is the countable set of continuous functionals $\{D^m_t\}$ from (10.2.1.9) on $\mathscr H^s_{F,a}(\omega)$.

It remains to show that the $\{D^m_t\}$ linearly generate a strongly dense subspace of $(\mathscr H^s_{F,a}(\omega))'_\beta$, and their bi-orthogonal set, which exists by Theorem 6.3.2.1(3) and is the image of a countable subset of $\mathscr H_F(\omega)$, is dense in $\mathscr H^s_{F,a}(\omega)$.

By Lemma 9.3.2.1, there exists, for each $\chi\in\widehat{C_F}$ chosen as in the fixed holomorphic parametrization of $\Omega(C_F)$ as in Notation 10.2.1.1, a countable subset $B=\{\varphi_{m,\omega}\}_{(m,\omega)\in\mathbf N\times\widehat{C^1_F}}\subset\mathcal S(C_F)$ of Schwartz-Bruhat functions satisfying the following properties:

(1) $A(B)$ is norm-bounded by $2$ in $W^{s,2}(C_F)$.

(2) For each $(m,\omega)\in\mathbf N\times\widehat{C^1_F}$, $\varphi_{m,\omega}$ is $\omega$-homogeneous.

(3) For each integer $m\ge 0$, the Fourier transform of $\varphi_{m,\omega}\in B$ is supported over the compact subset of $\widehat{C_F}$ of characters of the form $\chi|\cdot|^{ix}_F$ for $x\in[-m,m]$.

(4) The closure of $A(B)$ with respect to the strong operator topology on $\mathscr{L}(W^{s,2}(C_F))$ contains the identity.

where $A$ is the continuous linear operator $\mathcal S(C_F)\to\mathscr{L}(W^{s,2}(C_F))$ defined by the assignment:

$$
A(\varphi):=\int_{C_F}\varphi(g)\psi(g^{-1}x)\,\mathrm{d}\overline{\mu}(g)
$$

which was shown to be well-defined and continuous as a linear endomorphism of $W^{s,2}(C_F)$ in Lemma 9.3.2.1

We fix a single $\chi\in\widehat{C_F}$ among the base points of the connected components of $\Omega(C_F)$ according to the chosen holomorphic parametrization of $\Omega(C_F)$ (i.e. we choose a connected component $\Omega(C_F)(\omega)$, and consider the corresponding already chosen lift $\chi$ of $\omega$ to a continuous character of $C_F$), and we will be keeping track of this choice through the notation for the rest of this argument.

We define by:

$$
P_{\chi,m}:W^{s,2}(C_F)(\chi|_{C^1_F})\to W^{s,2}(C_F)(\chi|_{C^1_F}) \tag{10.2.1.10}
$$

the continuous linear operator $A(\varphi_{m,\chi|_{C^1_F}})$.

$P_{\chi,m}$ has range contained within the closed subspace of $W^{s,2}(C_F)(\chi|_{C^1_F})$ of those elements whose Fourier transform (pre-composed with the continuous homomorphic

## PDF page 443

**10.2. SPECTRAL MARKUSHEVICH BASES** · **443**

section $\tau$ to the idelic norm) is compactly supported over the interval $[-m,m]$, because it is isomorphic under the Fourier transform on $W^{s,2}(C_F)(\chi|_{C^1_F})$ (which is indeed defined by Proposition 9.1.2.6) to the multiplication operator by the Fourier transform of $\varphi_{m,\chi|_{C^1_F}}$.

We call $Q_{\chi,m}$ the orthogonal projector on $W^{s,2}(C_F)(\chi|_{C^1_F})$ onto such closed subspace, and $\overline{Q}_{\chi,m}$ the orthogonal projector on $\mathscr H^s_{F,a}(\chi|_{C^1_F})$ onto the closure of the linear image of such closed subspace under the quotient $W^{s,2}(C_F)(\chi|_{C^1_F})\to\mathscr H^s_{F,a}(\chi|_{C^1_F})$, a closed subspace of $\mathscr H^s_{F,a}(\chi|_{C^1_F})$.

Since $P_{\chi,m}\to\mathrm{Id}$ in $\mathscr{B}_{\mathrm{SOT}}(W^{s,2}(C_F)(\chi|_{C^1_F}))$, as $m\to+\infty$, by Lemma 9.3.2.1, the same holds for $Q_{\chi,m}$ as $m\to+\infty$, and therefore $\overline{Q}_{\chi,m}\to\mathrm{Id}$ in $\mathscr{B}_{\mathrm{SOT}}(\mathscr H^s_{F,a}(C_F)(\chi|_{C^1_F}))$.

The same therefore holds for the sequence of continuous adjoints $\overline{Q}'_{\chi,m}$ in $(\mathscr H^s_{F,a}(C_F)(\chi|_{C^1_F}))'_\beta$, as $m\to+\infty$, in $\mathscr{B}_{\mathrm{SOT}}((\mathscr H^s_{F,a}(C_F)(\chi|_{C^1_F}))'_\beta)$.

The range of $\overline{Q}'_{\chi,m}$ in $(\mathscr H^s_{F,a}(C_F)(\chi|_{C^1_F}))'_\beta$ is finite dimensional and is linearly generated by the functionals $\{D^k_t\}$ as $t\in[-m,m]$ and $0\le k\le N_s(\rho_{\chi,t})-1$. It follows that the range of $\overline{Q}_{\chi,m}$ in $\mathscr H^s_{F,a}(C_F)(\chi|_{C^1_F})$ is also finite dimensional and linearly generated by the bi-orthogonal set of the finite set of functionals $\{D^k_t\}$ as $t\in[-m,m]$ and $0\le k\le N_s(\rho_{\chi,t})-1$. This proves both denseness conditions for the set of continuous functionals $\{D^k_t\}$ as $0\le k\le N_s(\rho_{\chi,t})-1$ and $t\in\mathbf R$ varying over the ordinates of the zeros of $L(s,\chi)$ on the $a$-line, in $(\mathscr H^s_{F,a}(C_F)(\chi|_{C^1_F}))'_\beta$, and for its bi-orthogonal set in $\mathscr H^s_{F,a}(C_F)(\chi|_{C^1_F})$. $\square$

10.2.1.2. *Basic properties of the $a$-line basis.* We prove the following properties of the Markushevich basis $\{\eta_{\chi,t,m}\}$ introduced in (10.2.1.5) of Theorem 10.2.1.1, for the orthogonal

$$
W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))^\perp
$$

in $W^{-s,2}(C_F)$ with respect to the pairing $\langle\cdot,\cdot\rangle_{s,2}$ from (10.2.1.3).

We note that the subspace topology on such orthogonal inherited from the normed topology on $W^{-s,2}(C_F)$, is equivalent to the strong topology on the continuous dual of the quotient $\mathscr H^s_{F,a}$ equipped with its normed quotient topology: indeed, the latter is, a priori, finer, by [NB, Thm.8.11.3(d)]. By [NB, Thm.8.12.1(a)] combined with the Open Mapping Theorem, the two topologies are equivalent.

Proposition 10.2.1.3. *Let $F$ be a number field, let $a,s$ be real numbers, $s>1$. There exists a real number $C>0$ such that the functions:*

$$
\eta_{\chi,t,m}(g):=\chi(g)|g|^{it}_F(\log|g|_F)^m \tag{10.2.1.11}
$$

as:

(1) *$\chi$ ranges over the base-points for the chosen holomorphic parametrization for $\Omega(C_F)$ from (6.3.1.1).*

(2) *$t$ ranges over the imaginary parts of the zeros of the Hecke $L$-function $L(s,\chi)$ on the vertical line $\mathrm{Re}(s)=a$, with $0\le m\le N(\rho_{\chi,t})-1$, where $N_s(\rho_{\chi,t})$ is the function defined in (10.2.1.6).*

all satisfy:

$$
\{\chi(g)|g|^{it}_F(\log|g|_F)^m\}_{t,m}\subset B_{C}:=\{\phi\in W^{-s,2}(C_F):1/C\le||\phi||_{-s,2}\le C\}. \tag{10.2.1.12}
$$

*In particular, the set of functions from (10.2.1.11) is not contained in the open ball in $W^{-s,2}(C_F)$ of radius $1/C$.*

Proof. As for Proposition 11.2.0.4, we proceed as follows. For $s>1$, then:

$$
||\eta_{\chi,t,m}||_{-s,2}=\left(\int_{C_F}|\log|g|_F|^{2m}(1+|\log|g|_F|^2)^{-s/2}\,\mathrm{d}\overline{\mu}(g)\right)^{1/2}
$$

## PDF page 444

**444** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

by Proposition 9.1.2.5, and so $||\eta_{\chi,t,m}||_{-s,2}$ can only attain finitely many values, none of which is zero. There therefore exists a real number $C>0$ such that $1/C$ is a strict lower bound for their minimum, and $C$ is a strict upper bound for their maximum. $\square$

Terminology 10.2.1.2 (Normalized Markushevich Bases). As before Corollary 11.2.0.5, we recall the following terminology from [Kal], which applies to Schauder bases.

We recall from [Kal, §3,p.95] that a Schauder basis $\{b_k\}_{k\ge 0}$ in a Hausdorff locally convex topological $\mathbf C$-vector space $E$ is simple if and only if the finite rank projection operators $P_N:=\sum_{0\le k\le N}\langle\varphi_k,\cdot\rangle_{E',E}b_k$, for $\{\varphi_k\}_{k\ge 0}$ the dual basic sequence of $\{b_k\}_{k\ge 0}$, are a bounded set in $\mathscr{L}_\beta(E)$, i.e. they are strongly bounded.

We further recall from [Kal, §1,Def.1.1,p.91] that a Schauder basis $\{b_k\}_{k\ge 0}$ of $E$ is regular if and only if there exists a $0$-neighborhood $V$ such that $b_k\notin V$ for all $k\ge 0$.

Finally, from [Kal, §1,Def.1.2], a Schauder basis is normalized if and only if it is bounded and regular.

We extend the concepts of boundedness, regularities and normalization, to Markushevich bases, as follows.

Let $E$ be Banach space, and $\{(x_m,f_m)\}_{m\ge 0}\subset E\times E'_\beta$ a Markushevich basis. We say it is:

(1) Bounded, if and only if $\{x_m\}_{m\ge 0}\subset E$ is a bounded subset.

(2) Regular, if and only if $\{x_m\}_{m\ge 0}\subset E$ is strictly bounded away from $0\in E$. In particular, $\{f_m\}_{m\ge 0}\subset E'_\beta$ is bounded.

(3) Normalized, if and only if it is both bounded and regular.

We have the following:

Corollary 10.2.1.4. *Let $F$ be a number field, $s>1$ a real number. Any enumeration of the set of functions:*

$$
\eta_{\chi,t,m}(g):=\chi(g)|g|^{it}_F(\log|g|_F)^m \tag{10.2.1.13}
$$

as:

(1) *$\chi$ ranges over the base-points for the chosen holomorphic parametrization for $\Omega(C_F)$ from (6.3.1.1).*

(2) *$t$ ranges over the imaginary parts of the zeros of the Hecke $L$-function $L(s,\chi)$ on the vertical line $\mathrm{Re}(s)=a$, with $0\le m\le N_s(\rho_{\chi,t})-1$, where $N_s(\rho_{\chi,t})$ is the function defined in (10.2.1.6).*

*is a normalized Markushevich basis for the image of $(\mathscr H^s_{F,a})'_\beta$ in $W^{-s,2}(C_F)$ under $T_s$ from (9.1.2.14), i.e. for the orthogonal $W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))^\perp$ in $W^{-s,2}(C_F)$ with respect to the pairing $\langle\cdot,\cdot\rangle_{s,2}$ from (10.2.1.3).*

Proof. As a subset of $W^{-s,2}(C_F)$, there exists a real number $C>0$ such that the set of functions $\{\eta_{\chi,t,m}\}_{\chi,t,m}$ is contained in the annulus $B_{C}$ from (10.2.1.12) of Proposition 10.2.1.3.

In particular, as per Proposition 10.2.1.3, any enumeration of $\{\eta_{\chi,t,m}\}_{\chi,t,m}$, a Markushevich basis for $(\mathscr H^s_{F,a})'_\beta$ by Theorem 10.2.1.1, is regular and bounded, hence normalized. $\square$

Remark 10.2.1.5 (Approximations of the identity and basis projectors). We follow the notational choices made in Terminology 10.2.1.2.

In the special case $E=\mathscr H^s_{F,a}(\chi|_{C^1_F})$, for $a,s\in\mathbf R$, $s>1$, the $a$-line spectral Markushevich bases $\{(x_m,f_m)\}_{m\ge 0}\subset E\times E'_\beta$ provided by Theorem 10.2.1.1 are all normalized by Proposition 10.2.1.3; see Corollary 10.2.1.4.

They also satisfy a close analog of the “simplicity” condition: $\{x_m\}_{m\ge 0}$ is not a Schauder basis, and so the basis projections, all finite rank idempotent operators, do not converge strongly to the identity. However, the orthogonal projectors $\overline{Q}_{\chi,N}$ from the proof of Theorem 10.2.1.1, onto the closed subspace of those elements of $\mathscr H^s_{F,a}(\chi|_{C^1_F})$ which are images of elements in $W^{s,2}(C_F)(\chi|_{C^1_F})$ whose Fourier transform, pre-composed with pull-back along the chosen continuous homomorphic section $\tau$ to the idelic norm, is compactly supported over the interval $[-N,N]\subset\mathbf R$, serve as a replacement of the basis projectors, and they do converge to the identity on $\mathscr H^s_{F,a}(\chi|_{C^1_F})$ strongly, as a consequence of Lemma 9.3.2.1.

## PDF page 445

**10.2. SPECTRAL MARKUSHEVICH BASES** · **445**

**10.2.2. Spectral Markushevich basis: the general case of a compact interval $I=[\alpha,\beta]$.** In this section, we consider the general case of the linear topological extension:

$$
0\to W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))\to W^s_I(C_F)(\chi|_{C^1_F})\to\mathscr H^s_{F,a,I}(\chi|_{C^1_F})\to 0
$$

where $\mathscr H^s_{F,a,I}(\chi|_{C^1_F})$ is the normed completion of $\mathscr H_{F,a,I}(\chi|_{C^1_F})$ in Sobolev degree $s\ge 0$, with $I$ a compact non-empty interval $I=[-\alpha,\alpha]$ for a real number $\alpha\ge 0$, with $\mathscr H_{F,a}(\chi|_{C^1_F})$ defined as the quotient nuclear Fréchet space:

$$
\mathscr H_{F,a}(\chi|_{C^1_F}):=\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/|\cdot|^a_F\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))
$$

where multiplication by the quasi-character $|\cdot|^a_F$, a linear topological automorphism on $\mathcal{S}_{\mathrm{E}}(C_F)$ and $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$, is isomorphic to a horizontal translation by $a$ to the left on the Mellin transforms of the elements of $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$, and $\mathscr H^s_{F,a,I}(\chi|_{C^1_F})$ is the quotient Hilbert space, equivalently (by the Open Mapping Theorem) the completion of $\mathscr H^s_{F,a}(\chi|_{C^1_F})$ with respect to the normed topology induced by the quotient $||\cdot||_{I,s}$-norm.

We will be computing the nuclear traces of nuclear operators induced on the rightmost Hilbert space $\mathscr H^s_{F,a,I}(\chi|_{C^1_F})$, given by the operators $A(\varphi)$ from (9.3.1.2), for any $\varphi\in\mathcal D(C_F)$ and $I=[-\alpha,\alpha]$.

10.2.2.1. *The Markushevich basis on the $I$-based strip.* Let $a,s\in\mathbf R$ be real numbers, $s\ge 0$. We define:

$$
\mathscr H^s_{F,a,I}:=W^s_I(C_F)/W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F)). \tag{10.2.2.1}
$$

For every $\omega\in\widehat{C^1_F}$, we will be writing $\mathscr H^s_{F,a,I}(\omega)$ for its $\omega$-isotype, which is isometric to the quotient:

$$
\mathscr H^s_{F,a,I}(\omega):=W^s_I(C_F)(\omega)/W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F)) \tag{10.2.2.2}
$$

by the Open Mapping Theorem (and an application of Lemma 4.3.3.1).

We recall that we denoted the pairing $\langle\cdot,\cdot\rangle_{I,s}$ from (9.2.1.28) by:

$$
\langle\cdot,\cdot\rangle_{I,s}:W^s_I(C_F)\times W^{-s}_I(C_F)\to\mathbf C \tag{10.2.2.3}
$$

where $\langle\cdot,\cdot\rangle_{I,s}$ is assigned by:

$$
\langle\phi,\psi\rangle_{I,s}:=\int_{C_F}\phi(g)\psi(g)\,\mathrm{d}\overline{\mu}(g).
$$

The duality pairing $\langle\cdot,\cdot\rangle_{I,s}$ further identifies, by [NB, Thm.8.12.4(b)], the continuous dual $(\mathscr H^s_{F,a,I})'$ of the quotient $\mathscr H^s_{F,a,I}$ with the orthogonal in the sense of [NB, Def.8.9.1] of $W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))$.

We note that the pairing $\langle\cdot,\cdot\rangle_{I,s}$ respects $C^1_F$-isotypes, i.e. it induces a non-degenerate duality pairing:

$$
\langle\cdot,\cdot\rangle_{I,s}:W^s_I(C_F)(\omega)\times W^{-s}_I(C_F)(\overline{\omega})\to\mathbf C
$$

by invariance of the Haar measure $\overline{\mu}$ on $C_F$.

Notation 10.2.2.1. Throughout, we fix a choice of holomorphic parametrization for $\Omega(C_F)$ as in Notation 10.2.1.1.

This amounts to choosing, for every $\omega\in\widehat{C^1_F}$, a continuous unitary base-point $\chi\in\widehat{C_F}$, and parametrize every point of $\Omega(C_F)(\omega)$ as $\chi|\cdot|^z_F$ for a unique $z\in\mathbf C$.

We will be denoting by $\widetilde{C^1_F}\subset\widehat{C_F}$ the chosen set of unitary base-points for the connected components of $\Omega(C_F)$.

We will be writing $\sum'_{\omega\in\widehat{C^1_F}}$ to denote the sum of $\mathbf C$-valued functions depending on $\chi$ (such as countable sums of $M(\varphi)(\chi|\cdot|^{it}_F)$ for $t\in\mathbf R$ varying over a suitable discrete subset, for $\varphi\in\mathcal D(C_F)$ fixed, and interpreting the value of the sum as a function of $\chi$), to mean the sum indexed by the choices $\{\chi\in\widehat{C_F}\}$ lifting each point $\omega\in\widehat{C^1_F}$, choices which we fixed at the outset when parametrizing $\Omega(C_F)$ as $\chi|\cdot|^z_F$, $z\in\mathbf C$.

## PDF page 446

**446** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

Theorem 10.2.2.1 (Spectral Markushevich Basis on the $I$-based strip). *Let $F$ be a number field, $s,a\in\mathbf R$ real numbers, $s\ge 0$. Let $I=[-\alpha,\alpha]$ be a compact interval, $\alpha\ge 0$ a real number. The functions:*

$$
\eta_{\chi,t,b,m}(g):=\chi(g)|g|^{it+b}_F(\log|g|_F)^m \tag{10.2.2.4}
$$

such that:

(1) *for $t\in\mathbf R$ such that $\rho_{\chi,t,b}:=\chi|\cdot|^{a+it+b}_F$ is a zero of $L(s,\chi)$ of multiplicity $N(\rho_{\chi,t,b})$.*

(2) $m\ge 0$ is an integer satisfying $m\le N_{I,s}(\rho_{\chi,t,b})-1$ with:

$$
N_{I,s}(\rho_{\chi,t,b})=\min\left\{N(\rho_{\chi,t,b}),\left[\frac{s-1}{2}+1\right]\right\},\quad b=\pm\alpha \tag{10.2.2.5}
$$

and

$$
N_{I,s}(\rho_{\chi,t,b})=N(\rho_{\chi,t,b}),\quad b\in(-\alpha,\alpha) \tag{10.2.2.6}
$$

*are elements of $W^{-s}_I(C_F)$, any enumeration admits a bi-orthogonal sequence, and the resulting sequence of pairs is a Markushevich basis for $\mathscr H^s_{F,a,I}$, for the image of $(\mathscr H^s_{F,a,I})'_\beta$ in $W^{-s}_I(C_F)$ under $T_{I,s}$ from (9.2.1.31), and with respect to the duality pairing $\langle\cdot,\cdot\rangle_{I,s}$ from (10.2.2.3).*

Terminology 10.2.2.1 (Spectral Markushevich Basis on the $I$-bases strip). We refer to any sequence of pairs

$$
\{(\psi_m,u_m)\}_{m\ge 0}\subset\mathscr H^s_{F,a,I}\times T_{I,s}((\mathscr H^s_{F,a,I})'_\beta)
$$

obtained from a choice of enumeration of the elements from (10.2.2.4) of $W^{-s}_I(C_F)$ and their bi-orthogonal sequence, as the Spectral Markushevich Basis on the $I$-based strip.

Proof. The proof of Theorem 10.2.2.1 rests on the same method as in the proof of Theorem 10.2.1.1, with Theorem 9.3.2.6 replacing Lemma 9.3.2.1.$^6$ $\square$

10.2.2.2. *Basic properties of the Spectral Markushevich Basis on the $I$-based strip.* We prove the following properties of the Markushevich basis $\{\eta_{\chi,t,b,m}\}$ introduced in (10.2.2.4) of Theorem 10.2.2.1, for the orthogonal

$$
W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))^\perp
$$

in $W^{-s}_I(C_F)$ with respect to the pairing $\langle\cdot,\cdot\rangle_{I,s}$ from (10.2.2.3).

We note that the subspace topology on such orthogonal inherited from the normed topology on $W^{-s}_I(C_F)$, is equivalent to the strong topology on the continuous dual of the quotient $\mathscr H^s_{F,a,I}$ equipped with its normed quotient topology by the Open Mapping Theorem.

Proposition 10.2.2.2. *Let $F$ be a number field, let $a,s$ be real numbers, $s>1$. Let $I=[-\alpha,\alpha]\subset\mathbf R$ be a compact non-empty interval, $\alpha\ge 0$ a real number.*

*There exists a real number $C>0$ such that the functions:*

$$
\eta_{\chi,t,b,m}(g):=\chi(g)|g|^{it+b}_F(\log|g|_F)^m \tag{10.2.2.7}
$$

as:

(1) *$\chi$ ranges over the base-points for the chosen holomorphic parametrization for $\Omega(C_F)$ from (6.3.1.1).*

(2) *$t$ ranges over the imaginary parts of the zeros of the Hecke $L$-function $L(s,\chi)$ on the vertical line $\mathrm{Re}(s)=a$, with $0\le m\le N_{I,s}(\rho_{\chi,t,b})-1$, where $N_{I,s}(\rho_{\chi,t})$ is the function defined in (10.2.2.5) and (10.2.2.5).*

all satisfy:

$$
\{\chi(g)|g|^{it+b}_F(\log|g|_F)^m\}_{t,b,m}\subset B_{C}:=\{\phi\in W^{-s}_I(C_F):1/C\le||\phi||_{I,-s}\le C\}. \tag{10.2.2.8}
$$

---
$^6$Return here.

## PDF page 447

**10.3. SPECTRAL NUCLEARITY** · **447**

*In particular, the set of functions from (10.2.2.7) is not contained in the open ball in $W^{-s,2}(C_F)$ of radius $1/C$.*

PROOF. For $s>1$, then:

$$
\|\eta_{\chi,t,b,m}\|_{I,-s} = \left(\int_{C_F} \frac{|g|_F^{2b} |\log|g|_F|^{2m}}{\max\{|g|_F^{2\alpha},|g|_F^{-2\alpha}\} (1+|\log|g|_F|^2)^{s/2}}\, \mathrm{d}\bar\mu(g)\right)^{1/2}
$$

by Proposition 9.2.2.11, and so $\|\eta_{\chi,t,m}\|_{I,-s}$ can only attain values within a compact interval which does not contain $0\in\mathbf R$. There therefore exists a real number $C>0$ such that $1/C$ is a strict lower bound for their minimum, and $C$ is a strict upper bound for their maximum. $\square$

We retain, throughout this subsection, the lexicon introduced in Terminology 10.2.1.2.

We have the following:

COROLLARY 10.2.2.3. *Let $F$ be a number field, $s>1$ a real number. Any enumeration of the set of functions:*

$$
\eta_{\chi,t,b,m}(g) := \chi(g) |g|_F^{it+b} (\log|g|_F)^m \tag{10.2.2.9}
$$

*as:*

*(1) $\chi$ ranges over the base-points for the chosen holomorphic parametrization for $\Omega(C_F)$ from (6.3.1.1).*

*(2) $t$ ranges over the imaginary parts of the zeros of the Hecke $L$-function $L(s,\chi)$ on the vertical line $\mathrm{Re}(s)=a$, with $0\le m\le N_{I,s}(\rho_{\chi,t,b})-1$, where $N_{I,s}(\rho_{\chi,t,b})$ is the function defined in (10.2.2.5) and (10.2.2.6).*

*is a normalized Markushevich basis for the image of $(\mathscr H^s_{F,a,I})'_\beta$ in $W^{-s}_I(C_F)$ under $T_{I,s}$ from (9.2.1.31), i.e. for the orthogonal $W^s_{a,I} \mathrm{H}_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))^\perp$ in $W^{-s,2}(C_F)$ with respect to the pairing $\langle\cdot,\cdot\rangle_{I,s}$ from (9.2.1.28).*

PROOF. As a subset of $W^{-s}_I(C_F)$, there exists a real number $C>0$ such that the set of functions $\{\eta_{\chi,t,b,m}\}_{\chi,t,b,m}$ is contained in the annulus $B_C$ from (10.2.2.8) of Proposition 10.2.2.2.

In particular, as per Proposition 10.2.2.2, any enumeration of $\{\eta_{\chi,t,b,m}\}_{\chi,t,b,m}$, a Markushevich basis for $(\mathscr H^s_{F,a,I})'_\beta$ by Theorem 10.2.2.1, is regular and bounded, hence normalized. $\square$

**10.3. Spectral Nuclearity**

A consequence of Theorem 10.2.1.1 is that it enables us to identify certain nuclear operators on $\mathscr H^s_{F,a}$ explicitly, and compute their trace.

The contents of this subsection reprise [Co, §III,Cor.2,pp.13,14] and especially [Co, Appendix II,pp.62,68], providing only a few complements on the convergence of certain finite rank operators with respect to the appropriate Schatten-von Neumann norms (see Definition C.3.6.2) so as to enable a discussion on explicit integral kernels early in the next Chapter.

We recall from [Kothe-I, Part III,Ch.19,§19.9] that for two Banach spaces $E_1, E_2$, the $\mathbf C$-linear space $\mathscr S(E_1,E_2)$ denotes the $\mathbf C$-linear space of those linear operators $T:E_1\to E_2$ which can be written as

$$
T = \sum_{m\ge 0} \lambda_m \langle a_m,\cdot\rangle_{E'_1,E_2}\cdot y_m
$$

with $\{a_m\}_{m\ge 0}\subset B_{E'_1}$, $\{y_m\}_{m\ge 0}\subset B_{E_2}$, where $B_E$ denotes the unit ball of the Banach space $E$, and $\{\lambda_m\}_{m\ge 0}\subset\mathfrak s$, where $\mathfrak s$ is the Köthe sequence space of sequences of complex numbers $\{\lambda_m\}_{m\in\mathbf Z}$ that are rapidly decaying, i.e. such that $\{m^k\lambda_m\}_{m\in\mathbf Z}\subset \mathfrak{c}_0$ for every integer $k\ge 0$ (equivalently, $\mathfrak s = \mathcal S(\mathbf Z)$, the space of Schwartz-Bruhat functions on the discrete abelian group $\mathbf Z$).

The space $\mathfrak s$ is a Fréchet space when endowed with the countable family of seminorms:

$$
p_k(\{\lambda_m\}_{m\ge 0}) := \sum_{m\in\mathbf Z} (1+|m|)^k |\lambda_m|,\; k\ge 0.
$$

## PDF page 448

**448** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

We further refer the reader to [Tre, Part III,Ch.51,Rem.51.1,p.527] for more on $\mathfrak s = \mathcal S(\mathbf Z)$.

The linear space $\mathscr S(E_1,E_2)$ can be made into a complete metrizable topological vector space (see [Kothe-I, Part III,Ch.19,§19.9,Thm.3]).

$\mathscr S(E_1,E_2)$ is a linear subspace of the space $S_1(E_1,E_2)$ of nuclear operators, and when $E_1=E_2$ is a separable Hilbert space, $S_1(E) := S_1(E_1,E_2)$ is the $\mathbf C$-linear space of trace class linear endomorphisms on $E$.

There is a well-defined trace functional

$$
\mathrm{Trace}: S_1(E)\to\mathbf C
$$

which, for $E$ a closed invariant subspace or quotient of $W^{s,2}(C_F)$, we shall denote by $\mathrm{Trace}$ to record the dependence on the Sobolev degree $s$, i.e. the real number $s\ge 0$ built into the Sobolev weight defining $W^{s,2}(C_F)$.

We refer the reader to §C.3 and §C.3.4 for more on the trace class and nuclearity.

We specifically refer the reader to Definition C.3.4.2 for the trace of a nuclear endomorphism of a Hilbert space.

**10.3.1. Spectral nuclearity: the case $I=\{0\}$.**

THEOREM 10.3.1.1 (Spectral Nuclearity - I). *Let $F$ be a number field. Let $a,s\in\mathbf R$ be real numbers, with $s>1$. We choose a subset $\widetilde{C^1_F}\subset\widehat{C_F}$ of representatives for the countable group of continuous characters $\widehat{C^1_F}$, equivalently, a holomorphic parametrization for the Riemann surface $\Omega(C_F)$ of the form*

$$
\chi|\cdot|^z_F,\; (\chi,z)\in\widetilde{C^1_F}\times\mathbf C
$$

*as in (10.2.1.4) and Notation 10.2.1.1.*

*All characters $\chi\in\widehat{C_F}$ occurring below, are assumed to vary over the chosen subset $\widetilde{C^1_F}$, i.e. they are assumed to vary over the chosen base-points of the connected components of $\Omega(C_F)$.*

*Let $\varphi\in\mathcal D(C_F)$ be a test function.*

*(1) For any choice of enumeration $\{\eta_{\chi_k,t_{k,j},m_{k,j}}\}$, with $(k,j)\in\mathbf N\times\mathbf N$ and $0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1$, for the set of elements $\{\eta_{\chi,t,m}\}\subset W^{-s,2}(C_F)$ from Theorem 10.2.1.1, the sequence of finite rank operators:*

$$
\sum_{0\le k\le N_1} \sum_{0\le j\le N_2} \sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1} \langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},\cdot\rangle_{s,2}\; \psi_{\chi_k,t_{k,j},m_{k,j}} \tag{10.3.1.1}
$$

*in $\mathscr L_\beta(\mathscr H^s_{F,a})$ converges in $S_p(\mathscr H^s_{F,a})$ for every $p\ge 1$.*

*(2) The $\mathcal D(C_F)$-module structure:*

$$
A:\mathcal D(C_F)\to\mathscr L_\beta(\mathscr H^s_{F,a}) \tag{10.3.1.2}
$$

*is valued in the Banach space of nuclear operators $S_1(\mathscr H^s_{F,a})$ on $\mathscr H^s_{F,a}$, and is continuous with respect to the Hausdorff locally convex topology on the source, and the trace-norm topology on the target. In particular, the composition of $A$ and the trace functional on $S_1(\mathscr H^s_{F,a})$ is a distribution on $C_F$, whose value at $\varphi\in\mathcal D(C_F)$ is:*

$$
\mathrm{Trace}\; A(\varphi) = \sum_{\chi\in\widetilde{C^1_F}} \sum_{t\in\mathbf R:L(a+it,\chi)=0} N_s(\rho_{\chi,t}) \int_{C_F} \varphi(g)\chi|g|^{it}_F\, \mathrm{d}\bar\mu(g) \tag{10.3.1.3}
$$

*where $N_s$ is the counting function:*

$$
N_s(\rho_{\chi,t}) = \min\left\{N(\rho_{\chi,t}),\left[\frac{s-1}{2}+1\right]\right\} \tag{10.3.1.4}
$$

*where $[x]$ is the largest integer $N\ge 0$ satisfying $N\le x$.*

## PDF page 449

**10.3. SPECTRAL NUCLEARITY** · **449**

*(3) If $\varphi$ is homogeneous of weight $\overline{\omega}\in\widehat{C^1_F}$ under the continuous left-translation action of $C_F$ on $\mathcal D(C_F)$, then $A(\varphi)$ is valued in the linear subspace $\mathscr S(\mathscr H^s_{F,a}(\omega))$ of strongly nuclear operators on the isotype $\mathscr H^s_{F,a}(\omega)$, and its trace is:*

$$
\mathrm{Trace}\; A(\varphi) = \sum_{t\in\mathbf R:L(a+it,\chi)=0} N_s(\rho_{\chi,t}) \int_{C_F} \varphi(g)\chi|g|^{it}_F\, \mathrm{d}\bar\mu(g) \tag{10.3.1.5}
$$

*for $\chi\in\widetilde{C^1_F}$ the unique element of $\widetilde{C^1_F}$ such that $\chi|_{C^1_F}=\omega$, i.e. where $\chi$ is the base-point of $\Omega(C_F)(\omega)$ for the chosen holomorphic parametrization of $\Omega(C_F)$ from (10.2.1.4).*

PROOF. We choose an enumeration for the set $\{\eta_{\chi,t,m}\}$ of functions in $W^{-s,2}(C_F)$ from (10.2.1.5), and we denote it:

$$
\{\eta_{\chi_k,t_{k,j},m_{k,j}}\}_{(k,j)\in\mathbf N\times\mathbf N,0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1}. \tag{10.3.1.6}
$$

By Theorem 10.2.1.1, the sequence of vectors in $W^{-s,2}(C_F)$ from (10.3.1.6) is a Markushevich basis for the orthogonal of $\mathscr H^s_{F,a}$ with respect to the duality pairing $\langle\cdot,\cdot\rangle_{s,2}$ from (9.1.1.11).

(1) : To see this, we proceed as follows: we first show that the sequence of finite rank operators from (10.3.1.1):

$$
\sum_{0\le k\le N_1} \sum_{0\le j\le N_2} \sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1} \langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},\cdot\rangle_{s,2}\; \psi_{\chi_k,t_{k,j},m_{k,j}} \tag{10.3.1.7}
$$

in $\mathscr L_\beta(\mathscr H^s_{F,a})$ converges in $S_p(\mathscr H^s_{F,a})$ for every $p\ge 1$.

We fix $k,j$ such that $0\le k\le N_1$, and $0\le j\le N_2$. We have:

$$
A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}}(y) = \int_{C_F} \varphi(g)\chi_k(gy)|gh|^{it_{k,j}}_F (\log|gy|_F)^{m_{k,j}}\, \mathrm{d}\bar\mu(g) \tag{10.3.1.8}
$$

$$
= \int_{C_F} \varphi(g)\chi_k(g)\chi_k(y)|g|^{it_{k,j}}_F |y|^{it_{k,j}}_F (\log|g|_F+\log|y|_F)^{m_{k,j}}\, \mathrm{d}\bar\mu(g) \tag{10.3.1.9}
$$

$$
= \int_{C_F} \varphi(g)\chi_k(g)\chi_k(y)|g|^{it_{k,j}}_F |y|^{it_{k,j}}_F \sum_{0\le i\le m_{k,j}} \binom{m_{k,j}}{i} (\log|g|_F)^i (\log|y|_F)^{m_{k,j}-i}\, \mathrm{d}\bar\mu(g) \tag{10.3.1.10}
$$

$$
= \int_{C_F} \varphi(g)\chi_k(g)|g|^{it_{k,j}}_F \sum_{0\le i\le m_{k,j}} \binom{m_{k,j}}{i} (\log|g|_F)^i \left\{\chi_k(h)|y|^{it_{k,j}}_F (\log|y|_F)^{m_{k,j}-i}\right\}\, \mathrm{d}\bar\mu(g) \tag{10.3.1.11}
$$

$$
= \sum_{0\le i\le m_{k,j}} \binom{m_{k,j}}{i} \eta_{\chi_k,t_{k,j},m_{k,j}-i}(y) \int_{C_F} \varphi(g)\chi_k(g)|g|^{it_{k,j}}_F (\log|g|_F)^i\, \mathrm{d}\bar\mu(g). \tag{10.3.1.12}
$$

We now compute:

$$
\langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},\psi_{\chi_k,t_{k,j},m'_{k,j}}\rangle_{s,2} = \binom{m_{k,j}}{m_{k,j}-m'_{k,j}} \int_{C_F} \varphi(g)\chi_k(g)|g|^{it_{k,j}}_F (\log|g|_F)^{m_{k,j}-m'_{k,j}}\, \mathrm{d}\bar\mu(g) \tag{10.3.1.13}
$$

for each fixed $0\le k\le N_1$, $0\le j\le N_2$, and for each $0\le m'_{k,j}\le m_{k,j}$, and

$$
\langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},\psi_{\chi_k,t_{k,j},m'_{k,j}}\rangle_{s,2} = 0 \tag{10.3.1.14}
$$

if $m_{k,j}<m'_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1$.

From the Markushevich basis $\{\psi_{\chi_k,t_{k,j},m_{k,j}}\}$ for $\mathscr H^s_{F,a}$, we define the subset:

$$
B_K := \{\psi_{\chi_{k'},t_{k',j'},m_{k',j'}}\}_{0\le m_{k',j'}\le N_s(\rho_{\chi_{k'},t_{k',j'}})-1,(k',j')\in K}
$$

for each fixed finite subset $K\subset\mathbf N\times\mathbf N$.

## PDF page 450

**450** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

For each such $K$ and each fixed $k\in\mathbf N$ indexing the elements of $\widetilde{C^1_F}$, we further define the interval of the real line $[a_{K,k},b_{K,k}]$ where, upon defining $a'_K := \inf\{t_{k,j}:(k',j)\in K, k'=k\}$, $b'_K := \sup\{t_{k,j}:(k,j)\in K\}$, we define $a_{K,k} := a'_K-\varepsilon$ and $b_{K,k} := b'_K+\varepsilon$, for a choice of $\varepsilon>0$ such that the vertical segment $a+i[a_{K,k},b_{K,k}]$ contains no further zeros of $L(s,\chi_k)$ other than $\{a+it_{k,j}:(k,j)\in K\}$.

For each pair of integers $(k,j)$ such that $(k,j)\in K$, we define the finite rank operator:

$$
A_{K,(k,j)} := \sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1} \langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},P_{B_K}(\cdot)\rangle_{s,2}\; \psi_{\chi_k,t_{k,j},m_{k,j}} \tag{10.3.1.15}
$$

in $\mathscr L(\mathscr H^s_{F,a})$, where $P_{B_K}$ is the orthogonal projector onto the closed subspace of $\mathscr H^s_{F,a}$ linearly and topologically generated by the linear image of the closed subspace of $W^{s,2}(C_F)$ of those elements whose Fourier transform is supported over the subset:

$$
\{\chi_k|\cdot|^{i[a_{K,k},b_{K,k}]}_F,\; k\in\mathbf N\}\subset\widehat{C_F}.
$$

We note that in light of the orthogonality of the $\chi_k|_{C^1_F}$- and $\chi_{k'}|_{C^1_F}$-isotypes, for $k\ne k'$, then for each fixed integer $k$, the finite rank operator, whose range is indeed contained within $\mathscr H^s_{F,a}(\chi_k|_{C^1_F})$, defined in (10.3.1.15), factors through the orthogonal projection $P_{B_K,k}$ onto the closed subspace of $\mathscr H^s_{F,a}(\chi_k|_{C^1_F})$ given by the $\chi_k|_{C^1_F}$-isotype of the range of $P_{B_K}$. Such subspace is finite dimensional, since is dual is linearly and topologically generated by the elements of $W^{-s,2}(C_F)(\overline{\chi}_k|_{C^1_F})$:

$$
\eta_{\chi_k,t_{k,j},m_{k,j}}:\; t_{k,j}\in[a_{K,k},b_{K,k}],\; 0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1. \tag{10.3.1.16}
$$

These elements are finitely many, and their number is bounded above by:

$$
\left[\frac{s-1}{2}+1\right] \log(\max\{|a_{K,k}|,|b_{K,k}|\})
$$

by [Lang-b, Ch.XVII,§2,Prop.2.4,p.334].

The following factorization for $A_{K,(k,j)}$ therefore holds:

$$
A_{K,(k,j)} = A^{\mathrm{finite}}_{K,(k,j)}\circ P_{B_K,k}
$$

for $A^{\mathrm{finite}}_{K,(k,j)}$ the unique finite rank operator $A^{\mathrm{finite}}_{K,(k,j)}\in\mathscr L(\mathrm{Im}(P_{B_K,k}))$ induced by $A_{K,(k,j)}$, because the range of $P_{B_K,k}$ is a finite dimensional indecomposable sub-representation of $C_F$.

$A^{\mathrm{finite}}_{K,(k,j)} = A^{\mathrm{finite}}_{\{(k,j)\},(k,j)}$ is represented by the $N\times N$ matrix:

$$
\begin{bmatrix}
\widehat\varphi(it_{k,j}) & 0 & 0 & 0 & 0 & \cdots & 0 \\
\widehat\varphi^{(1)}(it_{k,j}) & \widehat\varphi(it_{k,j}) & 0 & 0 & 0 & \cdots & 0 \\
\widehat\varphi^{(2)}(it_{k,j}) & \binom{2}{1}\widehat\varphi^{(1)}(it_{k,j}) & \widehat\varphi(it_{k,j}) & 0 & 0 & \cdots & 0 \\
\widehat\varphi^{(3)}(it_{k,j}) & \binom{3}{2}\widehat\varphi^{(2)}(it_{k,j}) & \binom{3}{1}\widehat\varphi^{(1)}(it_{k,j}) & \widehat\varphi(it_{k}) & 0 & \cdots & 0 \\
\cdots & \cdots & \cdots & \cdots & \cdots & \cdots & \cdots \\
\widehat\varphi^{(N-1)}(it_{k,j}) & \binom{N-1}{N-2}\widehat\varphi^{(N-2)}(it_{k,j}) & \binom{N-1}{N-3}\widehat\varphi^{(N-3)}(it_{k,j}) & \binom{N-1}{N-4}\widehat\varphi^{(N-4)}(it_{k,j}) & \binom{N-1}{N-5}\widehat\varphi^{(N-5)}(it_{k,j}) & \cdots & \widehat\varphi(it_{k,j})
\end{bmatrix} \tag{10.3.1.17}
$$

where $N := N_s(\rho_{\chi_k,t_{\chi,j}})$, and $\widehat\varphi(z)$ is the Mellin transform of $\varphi$, i.e. $\widehat\varphi(z) := \int_{C_F} \varphi(g)\chi_k(g)|g|^z_F\, \mathrm{d}\bar\mu(g)$, an entire function on the complex $z$-plane, with $\widehat\varphi^{(r)}(z) = \frac{\partial^r}{\partial z^r}\widehat\varphi(z)$.

We further refer the reader to (D.3.3.11) of Theorem D.3.3.7 from Appendix D.3.2, and to Discussion 4.4.1.1, where, upon choosing a continuous homomorphic section $\tau$ to the idelic norm, $\widehat\varphi(z) = M(\varphi)(z+ix_k)$ as entire functions of $z\in\mathbf C$, for $x_k\in\mathbf R$ the unique real number such that $\chi_k(\tau(t)) = t^{ix_k}$ as smooth functions on $\mathbf R_{>0}$.

The finite sum:

$$
A_K := \sum_{(k,j)\in K} A_{K,(k,j)}
$$

## PDF page 451

**10.3. SPECTRAL NUCLEARITY** · **451**

is itself a finite rank operator, and by the foregoing it factors as $A_K = A^{\mathrm{finite}}_K\circ P_{B_K}$ where $A^{\mathrm{finite}}_K$ is a finite rank operator on the finite dimensional vector space $\mathrm{Im}(B_K)$, itself a finite dimensional direct sum of finitely many indecomposable sub-representations of $C_F$ on $\mathscr H^s_{F,a}$.

For a general finite subset $K\subset\mathbf N\times\mathbf N$ containing $(k,j)$, $A^{\mathrm{finite}}_{K,(k,j)}$ is represented by the $N_K\times N_K$ block matrix, for $N_K := \sum_{(k,j)\in K} N_s(\rho_{\chi_k,t_{k,j}})$, comprised, up to conjugation by a finite product of elementary matrices to interchange the ordering of the finitely many basis elements in $\mathrm{Im}(P_{B_K})$, of an $N_s(\rho_{\chi_k,t_{k,j}})\times N_s(\rho_{\chi_k,t_{k,j}})$ block equal to the matrix in (10.3.1.17) representing $A^{\mathrm{finite}}_{K,(k,j)}$, and zero elsewhere.

For every finite subset $K\subset\mathbf N\times\mathbf N$ containing the fixed pair of integers $(k,j)$, the singular values of the linear transformation $A^{\mathrm{finite}}_{K,(k,j)}\in\mathscr L(\mathrm{Im}(P_{B_K}))$ satisfy the following estimate:

$$
\sigma_m(A^{\mathrm{finite}}_{K,(k,j)}) \le N_s(\rho_{\chi_k,t_{k,j}})\cdot C\cdot 2^{N_s(\rho_{\chi_k,t_{k,j}})-1} \sum_{0\le i\le N_s(\rho_{\chi_k,t_{k,j}})-1} |\widehat\varphi^{(i)}(t_{k,j})| \tag{10.3.1.18}
$$

where $C$ is such that

$$
\|\eta_{\chi_k,t_{k,j},m'_{k,j}}\|_{-s,2}\cdot\|\psi_{\chi_k,t_{k,j},m_{k,j}}\|_{s,2}\le C
$$

for all $0\le m'_{k,j}\le m_{k,j}$, and all $0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1$.

The existence of $C$ is ensured by the Markushevich basis $\{\eta_{\chi_k,t_{k,j},m'_{k,j}}\}$, and hence its bi-orthogonal sequence $\{\psi_{\chi_k,t_{k,j},m'_{k,j}}\}$, being normalized (see Terminology 10.2.1.2), which implies that $C$ can be chosen to be independent of $m'_{k,j}$ and of $(k,j)$ (i.e. the countable set $\{\eta_{\chi_k,t_{k,j},m'_{k,j}}\}$ in $W^{-s,2}(C_F)$ and its bi-orthogonal in $W^{s,2}(C_F)$ are both contained in the closed ball of radius $C^{1/2}$ for some large enough $C>0$, and in fact they are contained in a closed collar bounded away from $0$ in each Hilbert space; see Proposition 10.2.1.3).

We deduce from (10.3.1.17) and [Jar, Part III,Ch.19,§19.8,Prop.1,438] (see also Lemma C.3.6.3(2)), that the singular values of the finite rank operator in (10.3.1.15) satisfy:

$$
\sigma_m(A_{K,(k,j)}) \le N_s(\rho_{\chi_k,t_{k,j}})\cdot C\cdot 2^{N_s(\rho_{\chi_k,t_{k,j}})-1} \sum_{0\le i\le N_s(\rho_{\chi_k,t_{k,j}})-1} |\widehat\varphi^{(i)}(t_{k,j})|\; \|P_{B_K}\|_{\mathscr L_\beta(\mathscr H^s_{F,a})} \tag{10.3.1.19}
$$

for $0\le m\le N_s(\rho_{\chi_k,t_{k,j}})-1$, and $\sigma_m(A_{K,(k,j)}) = 0$ for $m\ge N_s(\rho_{\chi_k,t_{k,j}})$.

Since $P_{B_K}$ is an orthogonal projector, we deduce from (10.3.1.19) that the following estimate holds:

$$
\sigma_m(A_{K,(k,j)}) \le N_s(\rho_{\chi_k,t_{k,j}})\cdot C\cdot 2^{N_s(\rho_{\chi_k,t_{k,j}})-1} \sum_{0\le i\le N_s(\rho_{\chi_k,t_{k,j}})-1} |\widehat\varphi^{(i)}(t_{k,j})|. \tag{10.3.1.20}
$$

Since, for every integer $m\ge 1$, we have $\sigma_m(A_{K,(k,j)}) = \sigma_m(A_{K',(k,j)})$ for every pair of finite subsets $K\subset K'\subset\mathbf N\times\mathbf N$ with $(k,j)\in K$, then the net of finite rank operators $\{A_{K,(k,j)}\}_K$ converges in $S_p(\mathscr H^s_{F,a})$ for every $p\ge 1$ to the finite rank operator:

$$
A_{(k,j)} := \sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j},m_{k,j}})-1} \langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},\cdot\rangle_{s,2}\; \psi_{\chi_k,t_{k,j},m_{k,j}}. \tag{10.3.1.21}
$$

To infer the convergence, we are using (10.3.1.20) upon observing that the rightmost side of (10.3.1.20) does not depend on $K$.

We deduce from (10.3.1.19) that we have:

$$
\sigma_m(A_{(k,j)}) \le N_s(\rho_{\chi_k,t_{k,j}})\cdot C\cdot 2^{N_s(\rho_{\chi_k,t_{k,j}})-1} \sum_{0\le i\le N_s(\rho_{\chi_k,t_{k,j}})-1} |\widehat\varphi^{(i)}(t_{k,j})| \tag{10.3.1.22}
$$

for $1\le m\le N_s(\rho_{\chi_k,t_{k,j}})-1$, and $\sigma_m(A_{(k,j)}) = 0$ for $m\ge N_s(\rho_{\chi_k,t_{k,j}})$.

Since $N_s(\rho_{\chi_k,t_{k,j}})$ is bounded independently of $(k,j)$ and only depends on $s$ (see (10.2.1.6)), and since $\widehat\varphi$ and all of its derivatives, the first $N_s(\rho_{\chi_k,t_{k,j}})-1$ only of which enter the estimates from (10.3.1.19), are

## PDF page 452

**452** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

Schwartz functions, being $\varphi$ smooth and compactly supported, then the sum

$$
\sum_{k\ge 0} \sum_{j\ge 0} \left(\sum_{0\le i\le N_s(\rho_{\chi_k,t_{k,j}})-1} |\widehat\varphi^{(i)}(it_{k,j})|\right)^p
$$

is convergent for every $p\ge 1$, and hence by (10.3.1.22) we deduce that the sequence of finite rank operators in $\mathscr L(\mathscr H^s_{F,a})$:

$$
\sum_{0\le k\le N_1} \sum_{0\le j\le N_2} \sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1} \langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},\cdot\rangle_{s,2}\; \psi_{\chi_k,t_{k,j},m_{k,j}} \tag{10.3.1.23}
$$

is Cauchy with respect to the $\|\cdot\|_{S_p(\mathscr H^s_{F,a})}$-norm for every $p\ge 1$, and hence it indeed converges in $S_p((\mathscr H^s_{F,a})'_\beta)$ for every $p\ge 1$.

Moreover, its limit, pre-composed with $P_{B_K}$ for each finite subset $K\subset\mathbf N\times\mathbf N$, agrees with the operator $A(\varphi)\circ P_{B_K}$, since the range of $P_{B_K}$ is a finite direct sum of finite dimensional indecomposable sub-representations of $C_F$ on the dual of $\mathscr H^s_{F,a}$, isometrically identified with a closed subspace of $W^{-s,2}(C_F)$ under $T_s$ from (10.2.1.3), linearly generated by the finitely many elements from (10.3.1.16) as $k\in\mathbf N$ varies over the image of $K$ in $\mathbf N$ under the first projection.

The directed union of the ranges of $P_{B_K}$ is dense in $\mathscr H^s_{F,a}$ by Corollary 9.3.2.3(2) (i.e. $P_{B_K}\to 1$ with respect to the strong operator topology, as $K$ tends to encompass $\mathbf N\times\mathbf N$; see Remark C.3.5.2).

It follows that the limit in $S_p(\mathscr H^s_{F,a})$, for $p\ge 1$, of the sequence of finite rank operators from (10.3.1.23), agrees with $A(\varphi)$ on a dense linear subspace, and hence the two continuous operators agree on $\mathscr H^s_{F,a}$ by continuity.

We further refer the reader to the proof of Theorem 7.4.1.1.

(2) and (3) : Since $W^{s,2}(C_F)$ and $W^{s,2}_a \mathrm{H}_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ are reflexive Banach spaces, being Hilbert spaces, then by [Tre, p.484] $A(\varphi)$ is nuclear if and only if its adjoint $A(\varphi)'$, a continuous linear endomorphism of $(\mathscr H^s_{F,a})'_\beta$, is nuclear. Its trace-norm is computed by $\|A(\varphi)\|_{\mathrm{Tr}} = \|A(\varphi)'\|_{\mathrm{Tr}}$.

The countable set $\{\eta_{\chi,t,m}\}_{(\chi,t,m)}$, with the enumeration chosen in (10.3.1.6), is a Markushevich basis within the in $W^{-s,2}(C_F)$ of $(\mathscr H^s_{F,a})'_\beta$ under the isometry $T_s$ from (10.2.1.3), by Theorem 10.2.1.1, as $\chi$ varies over the chosen (in (10.2.1.4)) base points of the connected components of $\Omega(C_F)$, each over a single point of the discrete parameter space $\widehat{C^1_F}$, $t\in\mathbf R$ varies over the imaginary parts of the zeros of $L(s,\chi)$ on the vertical line $\mathrm{Re}(s)=a$, and for each such zero $\rho=\rho_{\chi,t}$, $m$ varying over the integers $0\le m\le N_s(\rho_{\chi,t})-1$, where $N_s(\rho_{\chi,t})$ is the counting function defined in (10.2.1.6) from Theorem 10.2.1.1.

From the proof of (1), the singular values of the limit operator $A(\varphi)$ are a sequence of rapid decay, and hence $A(\varphi)$ is strongly nuclear.

We note that, since $\varphi$ is smooth and compactly supported, the sum in the right side of (10.3.1.3) is absolutely convergent. To see this, we proceed as follows (compare with Lemma B.4.4.8 and its proof, and see the Uniform Riemann-Lebesgue Lemma from Theorem D.3.4.2. Compare also with Proposition B.2.2.3).

By Theorem D.1.2.1, we write it the right side of (10.3.1.3), upon choosing a continuous homomorphic section $\tau$ to the idelic norm, and writing for any $g\in C_F$, $g=\tau(t)g_0$ for unique $t\in\mathbf R_{>0}$ and $g_0\in C^1_F$:

$$
\int_{\omega\in\widehat{C^1_F}} \sum_{\tau\in\mathbf R:L(a+i\tau,\chi)=0} N_s(\rho_{\chi,\tau}) \int_{\mathbf R_{>0}} \chi(\tau(t))t^{i\tau} \left(\int_{C^1_F} \omega(g_0)\varphi(\tau(t)g_0)\, \mathrm{d}\bar\mu_1(g_0)\right) \frac{\mathrm{d}t}{t} \tag{10.3.1.24}
$$

and we call:

$$
\Phi(x,\omega) := \int_{\mathbf R_{>0}} \chi(\tau(t))t^{ix} \left(\int_{C^1_F} \omega(g_0)\varphi(\tau(t)g_0)\, \mathrm{d}\bar\mu_1(g_0)\right) \frac{\mathrm{d}t}{t} \tag{10.3.1.25}
$$

## PDF page 453

10.3.  SPECTRAL NUCLEARITY                                  453

which is the Fourier transform $\widehat{\varphi}$ of $\varphi$ as a function over $\widehat{C_F}$, composed with the isomorphism of Hausdorff locally compact abelian groups $\mathbf{R}\times\widehat{C_F^1}\simeq\widehat{C_F}$ induced by $\tau$.

Let $\widehat{\bar\mu}_1$ be the Plancherel measure of $\bar\mu_1$, and $\widehat{\bar\mu}$ the Plancherel measure of $\bar\mu$ on $\widehat{C_F}$. Then under such isomorphism, the Haar measure $\lambda\otimes\widehat{\bar\mu}_1$ matches $\widehat{\bar\mu}$, $\lambda$ being the Lebesgue measure on $\mathbf{R}$, normalized so as to give the unit interval $[0,1]$ volume 1.

Since $\varphi\in\mathcal{D}(C_F)\subset\mathcal{S}(C_F)$, the Fourier transform $\widehat{\varphi}$ is Schwartz-Bruhat over $\widehat{C_F}$, hence in particular absolutely integrable, and so:

(10.3.1.26)

$$\sum_{(\omega,t)\in\widehat{C_F^1}\times\{\tau\in\mathbf{R}:L(a+i\tau,\chi)=0\}}|\Phi(\tau,\omega)|$$

is convergent, because it is comparable to the integral $\int_{\mathbf{R}_{>0}}\int_{\widehat{C_F^1}}|\Phi(x,\omega)|\,\mathrm{d}(\lambda\otimes\widehat{\bar\mu}_1)(x,\omega)$.

We further observe that the assignment, for each $\omega\in\widehat{C_F^1}$, of the sequence $\{\Phi(\tau,\omega):\tau\in\mathbf{R},\,L(a+i\tau,\chi)=0\}$, upon choosing any numbering of the imaginary parts of the zeros of $L(s,\chi)$ on the vertical line $\mathrm{Re}(s)=a$, is a sequence of rapid decay. In particular, if $\varphi$ is $\bar\omega$-homogeneous, then $\widehat{\varphi}$ is supported over $\mathbf{R}\times\{\omega\}$.

The formulas for the trace of $A(\varphi)$ provided in (10.3.1.3) and (10.3.1.5) follow from [Lit-II, §4,Cor.2,p.61] applied to $A(\varphi)\circ P_{B_K}$ for each finite subset $K\subset\mathbf{N}\times\mathbf{N}$ (the trace of $A(\varphi)\circ P_{B_K}$ is computed by the expression in (10.3.1.3) since $\{\eta_{\chi,t,m}\}$, with the chosen enumeration, is a Schauder basis within the range of $P_{B_K}$, since this is a finite dimensional $\mathbf{C}$-linear subspace of $\mathscr{H}^s_{F,a}$, and hence the nuclear trace of $A(\varphi)\circ P_{B_K}$ equals its matrix trace) for then using Proposition C.3.6.5 and continuity of the trace functional (see Lemma C.3.4.4) and the convergence $P_{B_K}\to\mathrm{1}$ with respect to the strong operator topology, as $K$ tends to cover $\mathbf{N}\times\mathbf{N}$, upon computing the point-spectrum (i.e. the subset of the complex plane of those complex numbers $\lambda$ that are eigenvalues of $A(\varphi)$) of $A(\varphi)$ to be exactly given by the countable set

$$\{\Phi(\tau,\omega):(\tau,\omega)\in\mathbf{R}\times\widehat{C_F^1},\,L(a+i\tau,\chi)=0\}\subset\mathbf{C}$$

each $\Phi(\tau,\omega)$ counted with multiplicity $N_s(\rho_{\chi,\tau})$, which follows from the calculation of the triangular matrix in (10.3.1.17), and hence the spectrum of $A(\varphi)\circ P_{B_K}$ to be given by the subset of $\{\Phi(\tau,\omega):(\tau,\omega)\in\mathbf{R}\times\widehat{C_F^1},\,L(a+i\tau,\chi)=0\}$ of those values $\Phi(\tau,\omega)$ for $\omega=\chi_k|_{C_F^1}$ with $k$ varying in the image of $K$ under the first projection $\mathbf{N}\times\mathbf{N}\to\mathbf{N}$, and $\tau$ varying over the real numbers $t_{k,j}$ for all $(k,j)\in K$. □

**10.3.2.  Spectral nuclearity: the general case of compact intervals $I=[-\alpha,\alpha]$.** The following generalizes Theorem 10.3.1.1 to the case $I=[-\alpha,\alpha]$ with $\alpha\ge 0$ a real number.

Theorem 10.3.2.1 (Spectral Nuclearity - II). *Let $F$ be a number field. Let $a,s\in\mathbf{R}$ be real numbers, with $s>1$. We choose a subset $\widetilde{C_F^1}\subset\widehat{C_F}$ of representatives for the countable group of continuous characters $\widehat{C_F^1}$, equivalently, a holomorphic parametrization for the Riemann surface $\Omega(C_F)$ of the form*

$$\chi|\cdot|^z_F,\quad(\chi,z)\in\widetilde{C_F^1}\times\mathbf{C}$$

*as in* (10.2.1.4) *and Notation 10.2.1.1.*

*All characters $\chi\in\widehat{C_F}$ occurring below, are assumed to vary over the chosen subset $\widetilde{C_F^1}$, i.e. they are assumed to vary over the chosen unitary base-points of the connected components of $\Omega(C_F)$.*

*Let $\varphi\in\mathcal{D}(C_F)$ be a test function.*

(1) *For any choice of enumeration $\{\eta_{\chi_k,t_{k,j},b_{k,j},m_{k,j}}\}$, with $(k,j)\in\mathbf{N}\times\mathbf{N}$ and $0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j},b_{k,j}})-1$, for the set of elements $\{\eta_{\chi,t,b,m}\}\subset W_I^{-s}(C_F)$ from Theorem 10.2.2.1, the sequence of finite rank operators:*

(10.3.2.1)

$$\sum_{0\le k\le N_1}\ \sum_{0\le j\le N_2}\ \sum_{0\le m_{k,j}\le N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})-1}\langle A(\varphi)'\eta_{\chi_k,t_{k,j},b_{k,j},m_{k,j}},\cdot\rangle_{I,s}\,\psi_{\chi_k,t_{k,j},b_{k,j},m_{k,j}}$$

*in $\mathscr{L}_\beta(\mathscr{H}^s_{F,a})$ converges in $S_p(\mathscr{H}^s_{F,a,I})$ for every $p\ge 1$.*

## PDF page 454

454                         CHAPTER 10.   TRACE FORMULA: SPECTRAL SIDE

(2) *The $\mathcal{D}(C_F)$-module structure:*

(10.3.2.2)

$$A:\mathcal{D}(C_F)\to\mathscr{L}_\beta(\mathscr{H}^s_{F,a,I})$$

*is valued in the Banach space of nuclear operators $S_1(\mathscr{H}^s_{F,a,I})$ on $\mathscr{H}^s_{F,a,I}$, and is continuous with respect to the Hausdorff locally convex topology on the source, and the trace-norm topology on the target. In particular, the composition of $A$ and the trace functional on $S_1(\mathscr{H}^s_{F,a,I})$ is a distribution on $C_F$, whose value at $\varphi\in\mathcal{D}(C_F)$ is:*

(10.3.2.3)

$$\mathrm{Trace}\,A(\varphi)=\sum_{\chi\in\widetilde{C_F^1}}\ \sum_{t\in\mathbf{R},\,b\in[-\alpha,\alpha]:\,L(a+b+it,\chi)=0}N_{I,s}(\rho_{\chi,t,b})\int_{C_F}\varphi(g)\chi|g|_F^{b+it}\,\mathrm{d}\bar\mu(g)$$

*where $N_{I,s}$ is the counting function:*

(10.3.2.4)

$$N_{I,s}(\rho_{\chi,t,b})=\min\left\{N(\rho_{\chi,t,b}),\left[\frac{s-1}{2}+1\right]\right\},\quad b=\pm\alpha,\qquad N_{I,s}(\rho_{\chi,t,b})=N(\rho_{\chi,t,b}),\quad b\in(-\alpha,\alpha)$$

*where $[x]$ is the largest integer $N\ge 0$ satisfying $N\le x$.*

(3) *If $\varphi$ is homogeneous of weight $\bar\omega\in\widehat{C_F^1}$ under the continuous left-translation action of $C_F$ on $\mathcal{D}(C_F)$, then $A(\varphi)$ is valued in the linear subspace $\mathscr{S}(\mathscr{H}^s_{F,a,I}(\omega))$ of strongly nuclear operators on the isotype $\mathscr{H}^s_{F,a,I}(\omega)$, and its trace is:*

(10.3.2.5)

$$\mathrm{Trace}\,A(\varphi)=\sum_{t\in\mathbf{R},\,b\in[-\alpha,\alpha]:\,L(a+b+it,\chi)=0}N_{I,s}(\rho_{\chi,t,b})\int_{C_F}\varphi(g)\chi|g|_F^{b+it}\,\mathrm{d}\bar\mu(g)$$

*for $\chi\in\widetilde{C_F^1}$ the unique element of $\widetilde{C_F^1}$ such that $\chi|_{C_F^1}=\omega$, i.e. where $\chi$ is the base-point of $\Omega(C_F)(\omega)$ for the chosen holomorphic parametrization of $\Omega(C_F)$ from* (10.2.1.4).

Proof. The argument for Theorem 10.3.2.1 follows the same method as in the proof of Theorem 10.3.1.1 upon replacing $N_s(\rho)$ defined in (10.3.1.4) with the truncated multiplicity function $N_{I,s}(\rho)$ defined in (10.2.2.5) and (10.2.2.6), noting that $N_{I,s}$, contrary to $N_s$, is unbounded if $\alpha>0$. In this case, we need to refine the estimate on:

(10.3.2.6)

$$\sum_{k\ge 0}\sum_{j\ge 0}\left(\sum_{0\le i\le N_s(\rho_{\chi_k,t_{k,j}})-1}|M(\varphi)^{(i)}(it_{k,j})|\right)^{p}$$

is convergent for every $p\ge 1$, which is used in the proof of Theorem 10.3.1.1 to infer that the sequence from (10.3.1.1) of finite rank operators converges in the $S_1$-norm topology.

We aim at deducing that the sequence of finite rank operators in (10.3.2.1) also converges in the $S_1$-norm, as $N_1,N_2\to+\infty$.

The sum that replaces (10.3.2.6) is:

(10.3.2.7)

$$\sum_{k\ge 0}\sum_{j\ge 0}\left(\sum_{0\le i\le N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})-1}|M(\varphi)^{(i)}(b_{k,j}+it_{k,j})|\right)^{p}.$$

In order to prove that it converges for every $p>1$, we proceed as follows. We let $N>1$ be a fixed integer, to be chosen later.

We assume for simplicity and without loss of generality that we have $i\ge N$.

## PDF page 455

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **455**

We note that we have, for each $\chi \in \widetilde{C_F}$ and upon choosing a continuous homomorphic section $\tau$ to the idelic norm:

$$
|z^N M(\varphi)^{(i)}(z)| \le \int_{\mathbf{R}_{>0}} \left(\int_{C^1_F} |(t\partial_t)^N(\varphi(\tau(t)g)\log(t)^i)t^{\mathrm{Re}(z)}| \,\mathrm{d}\overline{\mu}(g)\right)\frac{\mathrm{d}t}{t} \tag{10.3.2.8}
$$

$$
\le \sum_{0\le n\le N} \binom{N}{n} \int_{\mathbf{R}_{>0}} \left(\int_{C^1_F} ((t\partial_t)^{N-n}\varphi(\tau(t)g)) \cdot \frac{i!}{(i-n)!}(\log(t))^{i-n} t^{\mathrm{Re}(z)}| \,\mathrm{d}\overline{\mu}(g)\right)\frac{\mathrm{d}t}{t} \tag{10.3.2.9}
$$

$$
\le \sum_{0\le n\le N} \binom{N}{n} \prod_{0\le n\le N-1}(i-n) \int_{\mathbf{R}_{>0}} \left(\int_{C^1_F} |(t\partial_t)^{N-n}\varphi(\tau(t)g)\max\{t^{\alpha},t^{-\alpha}\}(1+|\log(t)|^2)^{s/2} \,\mathrm{d}\overline{\mu}(g)\right)\frac{\mathrm{d}t}{t} \tag{10.3.2.10}
$$

for any integer $0 \le i \le N_{I,s}(z)-1$. It follows that, upon calling $C_{N,I,s}(\varphi)>0$ the value of each integral in the last finite sum in (10.3.2.8), we have:

$$
|M(\varphi)^{(i)}(z)| \le \frac{C_{N,I,s}(\varphi)\prod_{0\le n\le N-1}(i-n)}{|z|^N} \tag{10.3.2.11}
$$

for all $z \in \mathbf{C}_I$, $\mathrm{Im}(z)\ne 0$. Using [Lang-e, Ch.XVII, Prop.2.6], we obtain $N_{I,s}(b+i\tau)=O(\log|\tau|)$, with the implied constant being uniform over all $b\in[-\alpha,\alpha]$, and $\prod_{0\le n\le N-1}(i-n)=C\cdot N\cdot O(\log|\tau)$ with the same implied constant in $O(\log|\tau|)$, and for $C>0$ a universal constant depending only on $N\ge 0$. We now choose $N>1$, and obtain the desired convergence of (10.3.2.7) for every $p>1$. The estimates from the proof of Theorem 10.3.1.1 now carry over, and the rest of the argument for Theorem 10.3.1.1 also establishes Theorem 10.3.2.1.

$\square$

10.4. Trace formula: Spectral Side

Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character.

We fix a real number $s\ge 0$, and we assume $s>1$ to ensure that every element of $W^{s,2}(C_F)$ is absolutely $\overline{\mu}$-integrable (see Proposition 9.1.2.6). Let $I$ be a compact interval, $I=[-\alpha,\alpha]$ for a real number $\alpha\ge 0$. Then we still choose $s>1$ in $W^s_I(C_F)$, to ensure the integrability of the functions $|\cdot|^b_F(\log|g|_F)^m$ for $b=\pm\alpha$ and $m<[\frac{s-1}{2}+1]$.

We further fix a real number $a\in\mathbf{R}$. We will be strengthening the assumptions on $s$ and $a$ as the need arises.

In this section we compute the contribution to the trace of the effect of the convolution action of the kernel $\varphi(xy^{-1})$ on $W^s_I(C_F)$, for $\varphi\in\mathcal{D}(C_F)$ a test function, on the dual of the quotient of the (closed) range of the multiplication operator $M_{\rho}$ by a smooth $(\Lambda,\varepsilon)$-cutoff $\rho$, modulo the closure of the range of $M_{\rho}$ restricted to

$$
|\cdot|^{1/2}_F \mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F)).
$$

We first introduce orthogonal projections $P^{\mathrm{geom}}_a$ on $W^s_I(C_F)(\chi|_{C^1_F})$ onto

$$
W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal{S}_0(\mathbf{A}_F))
$$

and its orthogonal complement, $P^{\mathrm{spec}}_a:=\mathrm{Id}-P^{\mathrm{geom}}_a$, and study the operators $P^{\mathrm{geom}}_a\circ A(\varphi)$ and $P^{\mathrm{spec}}_a\circ A(\varphi)$, for any test function $\varphi\in\mathcal{D}(C_F)$.

We shall prove in Theorem 10.4.2.1 that the latter is a nuclear operator on $W^s_I(C_F)$, and we will be computing its trace in Proposition 10.4.2.4.

## PDF page 456

**456** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

We will also be showing in Theorem 10.4.2.2 that its trace can be approximated by the traces of the Spectral Truncations $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$ as $\rho\to 1$, where $P^{\mathrm{spec}}_{\rho,a}$ will be defined as the composition of $P^{\mathrm{spec}}_a$ followed by multiplication by a $(\Lambda,\varepsilon)$-cutoff (see Definition 9.3.3.1 and Definition 9.3.3.3).

We will then be revisiting these results in terms of the integral kernels of the operators $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$, $P^{\mathrm{spec}}_a\circ A(\varphi)$, and $P^{\mathrm{geom}}_a\circ A(\varphi)$.

10.4.1. Truncations. We now begin our study of the $\mathcal{D}(C_F)$-module $W^s_I(C_F)$ and its closed submodules $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$, for. Due to non-compactness of the idele class group, and much as in the Selberg Trace Formula, we introduce truncation operators to promote the otherwise non-nuclear operator $A(\varphi)$ for each $\varphi\in\mathcal{D}(C_F)$ (see Definition 9.3.1.1) and its restriction to $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$, to nuclear truncated versions, which we will then study as the truncation “level” $\Lambda$ tends to grow large.

We require the following terminology and notation:

Definition 10.4.1.1. Let $F$ be a number field, let $s,a$ be real numbers, $s\ge 0$, $a>0$. Let $I=[-\alpha,\alpha]$ be a compact non-empty interval, with $\alpha\ge 0$ a real number. We define:

(1) The geometric projection operator to be the orthogonal projector:

$$
P^{\mathrm{geom}}_a: W^s_I(C_F)\to W^s_I(C_F) \tag{10.4.1.1}
$$

assigned by sending $\phi\in W^s_I(C_F)$ to the orthogonal projection onto the closed subspace

$$
W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))\subset W^s_I(C_F).
$$

(2) The spectral projection operator to be the orthogonal projector:

$$
P^{\mathrm{spec}}_a: W^s_I(C_F)\to W^s_I(C_F) \tag{10.4.1.2}
$$

assigned by sending $\phi\in W^s_I(C_F)$ to the orthogonal projection onto the closed subspace of $W^s_I(C_F)$ defined as the orthogonal complement of the closed subspace $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$ within $W^s_I(C_F)$.

Lemma 10.4.1.2. *Let $F$ be a number field, let $s,a$ be real numbers, $s\ge 0$, $a>0$. Let*

$$
Q_a: W^s_I(C_F)\to \mathscr{H}^s_{F,a,I}:=W^s_I(C_F)/W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F)) \tag{10.4.1.3}
$$

*be the quotient continuous linear operator by the closed $C_F$-invariant subspace $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))\subset W^s_I(C_F)$.*

Then we have:

$$
Q_a=Q_a\circ P^{\mathrm{spec}}_a,\quad Q_a\circ P^{\mathrm{geom}}_a=0 \tag{10.4.1.4}
$$

*and for every $\psi\in \mathscr{H}^s_{F,a,I}$, the unique $\phi\in W^s_I(C_F)$ orthogonal within $W^s_I(C_F)$ to $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$ and such that $Q_a(\phi)=\psi$ is, for any choice $\widetilde\psi\in W^s_I(C_F)$ such that $Q_a(\widetilde\psi)=\psi$, the element $\phi=P^{\mathrm{spec}}_a(\widetilde\psi)$. The assignment $S_a:\phi\mapsto P^{\mathrm{spec}}_a(\widetilde\psi)$ does not depend on the choice of $\widetilde\psi$, and it is an isometric linear topological isomorphism:*

$$
S_a: \mathscr{H}^s_{F,a,I}\to P^{\mathrm{spec}}_a W^s_I(C_F). \tag{10.4.1.5}
$$

Proof. Since $P^{\mathrm{geom}}_a$ is valued in $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$, we have $Q_a\circ P^{\mathrm{geom}}_a=0$, and since $\mathrm{Id}=P^{\mathrm{geom}}_a+P^{\mathrm{spec}}_a$ in $\mathscr{L}_{\beta}(W^s_I(C_F))$, we have $Q_a=Q_a\circ(P^{\mathrm{geom}}_a+P^{\mathrm{spec}}_a)=Q_a\circ P^{\mathrm{spec}}_a$.

The remaining assertion on $\phi$ follows from the definition of orthogonal projectors on a Hilbert space: if $\phi$ is orthogonal to $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$ and satisfies $Q_a(\phi)=\psi$, then so does $P^{\mathrm{spec}}_a(\phi)$ by (10.4.1.4), and so $\phi=P^{\mathrm{spec}}_a(\phi)$.

This shows that formation of $S_a$ does not depend on the choices being made in its definition, and it is linear. Since $Q_a\circ S_a$ is the identity on $\mathscr{H}^s_{F,a,I}$, we deduce that $S_a:\mathscr{H}^s_{F,a,I}\to P^{\mathrm{spec}}_a W^s_I(C_F)$ is linear and surjective, and $Q_a$ is a continuous left-inverse. $Q_a$ is an isometric linear topological isomorphism from

## PDF page 457

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **457**

$P^{\mathrm{spec}}_a W^s_I(C_F)$ to $\mathscr{H}^s_{F,a,I}$, since it is surjective, injective and open, being a quotient map. Its inverse, both left and right, is continuous, and hence $S_a$ is continuous and bijective, hence a linear topological isomorphism by [NB, Thm.14.4.5]. Since its inverse is isometric, so is $S_a$.

$\square$

We now introduce truncated versions of $P^{\mathrm{geom}}_a$, respectively $P^{\mathrm{spec}}_a$.

We refer the reader to Definition 9.3.3.1 and Definition 9.3.3.3 for the definition of $(\Lambda,\varepsilon)$-cutoffs and smooth $(\Lambda,\varepsilon)$-cutoff, which we will be specializing hereafter to the $\mathbf{R}_{>0}$-modulated group $C_F$, whose module is the idelic norm $|\cdot|_F$.

Definition 10.4.1.3 (Spectral and geometric truncations - projection after convolution). Let $F$ be a number field. Let $I=[-\alpha,\alpha]$ be a compact non-empty interval, with $\alpha\ge 0$ a real number. Let $a,s,\Lambda,\varepsilon$ be real numbers, with $s\ge 0$ and $\Lambda,\varepsilon>0$. Assume $0<1/\Lambda+\varepsilon<\Lambda-\varepsilon$. Let $\rho:C_F\to\mathbf{C}$ be a $(\Lambda,\varepsilon)$-cutoff. Let $\varphi\in\mathcal{D}(C_F)$ be a test function.

(1) We define the Geometric Truncation Operator to be the composition:

$$
P^{\mathrm{geom}}_{\rho,a}: W^s_I(C_F)\to W^s_I(C_F) \tag{10.4.1.6}
$$

of the orthogonal projection $P^{\mathrm{geom}}_a$ onto $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$, followed by the multiplication operator $M_{\rho}$.

We define the Geometric Truncation of $A(\varphi)$ of level $\rho$ to be the composition:

$$
P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi): W^s_I(C_F)\to P^{\mathrm{geom}}_{\rho,a}W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))\to W^s_I(C_F). \tag{10.4.1.7}
$$

(2) We define the Spectral Truncation Operator:

$$
P^{\mathrm{spec}}_{\rho,a}: W^s_I(C_F)\to W^s_I(C_F) \tag{10.4.1.8}
$$

to be the composition of $P^{\mathrm{spec}}_a$ followed by the multiplication operator $M_{\rho}$.

We define the Spectral Truncation of $A(\varphi)$ of level $\rho$ to be the composition:

$$
P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi): W^s_I(C_F)\to P^{\mathrm{spec}}_{\rho,a}W^s_I(C_F)\to W^s_I(C_F). \tag{10.4.1.9}
$$

Remark 10.4.1.4. We note that since $\mathrm{Id}=P^{\mathrm{geom}}_a+P^{\mathrm{spec}}_a$, and since $P^{\mathrm{geom}}_{\rho,a}=M_{\rho}\circ P^{\mathrm{geom}}_a$ and $P^{\mathrm{spec}}_{\rho,a}=M_{\rho}\circ P^{\mathrm{spec}}_a$, we have:

$$M_{\rho}=P^{\mathrm{geom}}_{\rho,a}+P^{\mathrm{spec}}_{\rho,a}$$

in $\mathscr{L}_{\beta}(W^s_I(C_F))$.

We further note that since the Sobolev weight function $\max\{|g|^{\alpha}_F,|g|^{-\alpha}_F\}(1+|\log|\cdot|_F|^2)^{s/2}$ is not $C_F$-invariant (see Lemma 9.3.1.5), the continuous left-translation action of $C_F$ on $W^s_I(C_F)$ is through linear topological automorphisms, but not through isometries, and in particular it does not preserve orthogonality within the metric space $W^s_I(C_F)$.

It does, however, preserve the pairing $\langle\cdot,\cdot\rangle_{I,s}$ from (9.2.1.28), by invariance of the Haar measure $\overline{\mu}$ on $C_F$.

To fix ideas, we choose $I=[-\alpha,\alpha]=\{0\}$, i.e. $\alpha=0$.

If $s$ is an even integer, however, we may change the metric on $W^s_I(C_F)=W^{s,2}(C_F)$ without changing the topology: this is the content of Lemma 9.1.2.2. We further refer the reader to [Fol, Ch.9, §9.3, p.301].

The new metric is such that $C_F$ acts by continuous left-translations in a conformal manner, i.e. its action preserves angles, although, still, not distances (again, by another application of Lemma 9.1.2.2 combined with Lemma 9.3.1.5. The action of $C_F$ is not unitary, but, rather, it grows slowly with respect to the operator norm according to Lemma 9.3.1.5).

Since $P^{\mathrm{geom}}_a$ is valued in $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$, and this latter is a closed $C_F$-invariant subspace of $W^s_I(C_F)$, we have

$$
P^{\mathrm{geom}}_a\circ A(\varphi)\circ P^{\mathrm{geom}}_a=A(\varphi)\circ P^{\mathrm{geom}}_a \tag{10.4.1.10}
$$

## PDF page 458

**458** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

and

$$
P^{\mathrm{spec}}_a\circ A(\varphi)\circ P^{\mathrm{spec}}_a=P^{\mathrm{spec}}_a\circ A(\varphi) \tag{10.4.1.11}
$$

while we do not have the stronger commutation relations $A(\varphi)\circ P^{\mathrm{geom}}_a=P^{\mathrm{geom}}_a\circ A(\varphi)$ and $A(\varphi)\circ P^{\mathrm{spec}}_a=P^{\mathrm{spec}}_a\circ A(\varphi)$, ultimately because $P^{\mathrm{geom}}_a\circ A(\varphi)\circ P^{\mathrm{spec}}_a\ne 0$ (i.e. the continuous left-translation action of $C_F$ on $W^s_I(C_F)$ does not preserve the orthogonality relations intrinsic within $W^s_I(C_F)$ with respect to the metric defined in (9.1.2.3), with the sole exception of the case $s=\alpha=0$, in which case such action is through unitary automorphisms).

We do have $P^{\mathrm{spec}}_a\circ A(\varphi)\circ P^{\mathrm{geom}}_a=0$, which follows from (10.4.1.10).

We define truncations again, but in a different order:

Definition 10.4.1.5 (Spectral and geometric truncations - convolution after projection). Let $F$ be a number field. Let $I=[-\alpha,\alpha]$ be a compact non-empty interval, with $\alpha\ge 0$ a real number. Let $a,s,\Lambda,\varepsilon$ be real numbers, with $s\ge 0$ and $\Lambda,\varepsilon>0$. Assume $0<1/\Lambda+\varepsilon<\Lambda-\varepsilon$. Let $\rho:C_F\to\mathbf{C}$ be a $(\Lambda,\varepsilon)$-cutoff. Let $\varphi\in\mathcal{D}(C_F)$ be a test function.

(1) We define the Geometric Restriction Operator of level $\rho$:

$$
M_{\rho}\circ A^{\mathrm{geom}}_a(\varphi): W^s_I(C_F)\to W^s_I(C_F) \tag{10.4.1.12}
$$

to be the composition of $P^{\mathrm{geom}}_a:W^s_I(C_F)\to W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$, followed by the convolution operator $A(\varphi)$, and by the multiplication operator $M_{\rho}$.

(2) We define the Spectral Restriction Operator of level $\rho$:

$$
M_{\rho}\circ A^{\mathrm{spec}}_a(\varphi): W^s_I(C_F)\to W^s_I(C_F) \tag{10.4.1.13}
$$

to be the composition of $P^{\mathrm{spec}}_a:W^s_I(C_F)\to W^s_I(C_F)$ followed by the convolution operator $A(\varphi)$ and by the multiplication operator $M_{\rho}$.

Geometric and spectral restrictions are those that will be the main focus of this Chapter. It will turn out that the nuclear trace

$$
\mathrm{Trace}\,M_{\rho}\circ A^{\mathrm{spec}}_a(\varphi)
$$

satisfies:

$$\lim_{\Lambda\to+\infty,\varepsilon\Lambda=o(1)}\mathrm{Trace}\,M_{\rho}\circ A^{\mathrm{spec}}_a(\varphi)=\mathrm{Trace}\,A^{\mathrm{spec}}_a(\varphi)$$

as for $P^{\mathrm{spec}}_{a,\rho}\circ A(\varphi)$. This is not formal, but requires explicit estimates using lifts of the Spectral Markushevich bases, combined with Theorem 10.3.2.1.

10.4.2. Spectral Side. In this subsection we study the nuclearity and trace of the spectral truncation of $A(\varphi)$ of level $\rho$ (see (10.4.1.9)) for $\rho$ a $(\Lambda,\varepsilon)$-cutoff in the sense of Definition 9.3.3.1 and Definition 9.3.3.3, for each test function $\varphi\in\mathcal{D}(C_F)$: we show it is a nuclear operator, and compute the limit of its trace as $\rho\to 1$ in the regime $\varepsilon\Lambda=o(1)$ as $\Lambda\to+\infty$.

Since we computed the trace of $M_{\rho}\circ A(\varphi)$ in Theorem 9.3.3.5, and since we have

$$
\mathrm{Trace}\,M_{\rho}\circ A(\varphi)=P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)+P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi) \tag{10.4.2.1}
$$

we will obtain the identity:

$$
\mathrm{Trace}\,(M_{\rho}\circ A(\varphi))=\mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi))+\mathrm{Trace}\,(P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)) \tag{10.4.2.2}
$$

which we will be studying for suitable $a$, and upon choosing $s\ge 0$ large enough, and as $\rho\to 1$ while having $\varepsilon\Lambda=o(1)$ as $\Lambda\to+\infty$.

To study $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$, we first prove that it is nuclear for every $(\Lambda,\varepsilon)$-cutoff $\rho$, and we then compute its trace as $\rho 1$ while $\varepsilon\Lambda=o(1)$ as $\Lambda\to+\infty$. This is the scope of this subsection and the next.

## PDF page 459

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **459**

Theorem 10.4.2.1. *Let $F$ be a number field, $a,s$ real numbers, $s\ge 0$. Let $I=[-\alpha,\alpha]$ be a compact non-empty interval, with $\alpha\ge 0$ a real number. Let $\Lambda,\varepsilon>0$ be real numbers such that $0<1/\Lambda+\varepsilon<\Lambda-\varepsilon$. Let $\rho$ be a $(\Lambda,\varepsilon)$-cutoff.*

*Then for any $\varphi\in\mathcal{D}(C_F)$, the operator $P^{\mathrm{spec}}_a\circ A(\varphi)$, and the operators $P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)$ from (10.4.1.7) and $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$ from (10.4.1.9) are nuclear.*

Their traces satisfy the identity:

$$
\mathrm{Trace}\,(M_{\rho}\circ A(\varphi))=\mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi))+\mathrm{Trace}\,(P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)) \tag{10.4.2.3}
$$

Proof. The projector $P^{\mathrm{spec}}_{\rho,a}$ from (10.4.1.8) satisfies:

$$
P^{\mathrm{spec}}_{\rho,a}=M_{\rho}\circ P^{\mathrm{spec}}_a \tag{10.4.2.4}
$$

where $P^{\mathrm{spec}}_a$ is the orthogonal projector $W^s_I(C_F)$ onto the orthogonal within $W^s_I(C_F)$ of $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$.

Recall that the quotient of $W^s_I(C_F)$ by $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$ was denoted $\mathscr{H}^s_{F,a,I}$ (see (10.2.1.1) and Theorem 10.3.1.1).

The operator $P^{\mathrm{spec}}_a\circ A(\varphi)$ satisfies:

$$
P^{\mathrm{spec}}_a\circ A(\varphi)=S_a\circ A^{\mathrm{spec}}_a(\varphi)\circ Q_a \tag{10.4.2.5}
$$

where $S_a:\mathscr{H}^s_{F,a}\to P^{\mathrm{spec}}_a W^s_I(C_F)$ is the surjective isometry induced by the quotient $Q_a:W^s_I(C_F)\to \mathscr{H}^s_{F,a,I}$, and $A^{\mathrm{spec}}_a(\varphi)$ is the operator from (10.3.1.2) of Theorem 10.3.1.1.

Explicitly, for $\psi\in \mathscr{H}^s_{F,a}$, $S_a(\psi)$ is the unique element $\widetilde\psi\in P^{\mathrm{spec}}_a W^s_I(C_F)$ such that $Q_a(\widetilde\psi)=\psi$. We can compute $S_a(\psi)$ by choosing $\widetilde\psi\in W^s_I(C_F)$ such that $Q_a(\widetilde\psi)=\psi$, and we have $S_a(\psi)=P^{\mathrm{spec}}_a(\widetilde\psi)$.

To prove that (10.4.2.5) holds, we proceed as follows.

We let $\phi\in W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$ be an arbitrary element. Then, since $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$ is a closed $C_F$-invariant subspace of $W^s_I(C_F)$, $A(\varphi)$ induces a continuous linear endomorphism of $W^{s,2}_a \mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$, and hence $A(\varphi)(\phi)\in W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$, which implies that we have:

$$
(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi)=0. \tag{10.4.2.6}
$$

Let $\phi\in W^s_I(C_F)$. We have, by (10.4.2.6):

$$
(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi+\phi_0)=(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi) \tag{10.4.2.7}
$$

for every $\phi_0\in W^{s,2}_a \mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$.

This implies that we have:

$$
(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi)=(S^{-1}_a\circ Q_a\circ A(\varphi))(\phi)=(S^{-1}_a\circ A^{\mathrm{spec}}_a(\varphi)\circ Q_a)(\phi) \tag{10.4.2.8}
$$

for all $\phi\in W^s_I(C_F)$, and so (10.4.2.5) holds ($S^{-1}_a(\psi)$ is the unique element $\widetilde\psi$ of $P^{\mathrm{spec}}_a W^s_I(C_F)$ such that $Q_a(\widetilde\psi)=\psi$. For $\psi=A^{\mathrm{spec}}_a(\varphi)(Q_a(\phi))$, and since $Q_a\circ A(\varphi)=A^{\mathrm{spec}}_a(\varphi)\circ Q_a$, such element is $(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi)$, by (10.4.2.7)).

By Theorem 10.3.1.1, $A^{\mathrm{spec}}_a(\varphi)$ is nuclear, and by [Cnw-b, Ch.3, §18, Thm.18.11(a)] (see also Lemma C.3.4.4(1)), so are $P^{\mathrm{spec}}_a\circ A(\varphi)$ and $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$.

Upon observing that we have $P^{\mathrm{geom}}_{\rho,a}+P^{\mathrm{spec}}_{\rho,a}=M_{\rho}$ within $\mathscr{L}_{\beta}(W^s_I(C_F))$, and since $M_{\rho}\circ A(\varphi)$ is nuclear by Theorem 9.3.3.5, then so is $P^{\mathrm{geom}}_a\circ A(\varphi)=M_{\rho}\circ A(\varphi)-P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$, and we deduce from Proposition C.3.5.1 that (10.4.2.3) holds.

$\square$

We now compute the “Spectral Side” of the Trace Formula, i.e. the limit as $\rho\to 1$ as $\Lambda\to+\infty$ (under the assumption $\varepsilon\Lambda=o(1)$ as $\Lambda\to+\infty$) of $\mathrm{Trace}\,(P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi))$ for any $s\ge 0$ and any $a\in\mathbf{R}$.

We study the $\mathcal{D}(C_F)$-module:

$$\mathscr{H}^s_{F,a,I}:=W^s_I(C_F)/W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$$

## PDF page 460

**460** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

and its $(\chi|_{C^1_F})$-isotype.

It is linearly and topologically isomorphic to the orthogonal of $W^s_{a,I}\mathrm{H}_{0,\mathrm{cont}}(F^{\times},\mathcal{S}_0(\mathbf{A}_F))$ in $W^s_I(C_F)$ with respect to the intrinsic Hilbert pairing $\langle\cdot,\cdot\rangle$ on $W^s_I(C_F)$.

The duality pairing $\langle\cdot,\cdot\rangle_{s,2}$ further identifies, by [NB, Thm.8.12.4(b)], the continuous dual $(\mathscr{H}^s_{F,a})'$ of the quotient $\mathscr{H}^s_{F,a}$ with the orthogonal in the sense of [NB, Def.8.9.1] with respect to $\langle\cdot,\cdot\rangle_{I,s}:W^s_I(C_F)\times W^{-s,2}(C_F)\to\mathbf{C}$ from (10.2.1.3).

Such identifications are all compatible with the continuous left-translation action of $C_F$, whose adjoint on $(\mathscr{H}^s_{F,a})'$ is the right-translation action of $C_F$ on $(\mathscr{H}^s_{F,a})'$, and hence with $\mathcal{D}(C_F)$-module structures.

The following is the first of the two main Theorems of this section (the second being Theorem 10.4.2.8:

Theorem 10.4.2.2 (Spectral side: projection after convolution). *Let $F$ be a number field, $a,s$ real numbers, $s\ge 0$. Let $I=[-\alpha,\alpha]\subset\mathbf{R}$ be a compact interval, $\alpha\ge 0$ a real number. We have, for all real numbers $\Lambda,\varepsilon>0$ satisfying $0<1/\Lambda+\varepsilon<\Lambda-\varepsilon$, and $\varepsilon\Lambda=o(1)$ as $\Lambda\to+\infty$, and for a $(\Lambda,\varepsilon)$-cutoff $\rho$ for each pair $(\Lambda,\varepsilon)$:*

$$
\mathrm{Trace}\,(P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi))=\mathrm{Trace}\,(A^{\mathrm{spec}}_a(\varphi))+o(1) \tag{10.4.2.9}
$$

*as $\Lambda\to+\infty$, where $A^{\mathrm{spec}}_a(\varphi)$ is the nuclear operator from (10.3.1.2), whose trace is computed by the formula in (10.3.1.3) of Theorem 10.3.1.1.*

Remark 10.4.2.3. Theorem 10.4.2.2 will be proved throughout the remainder of this section. The rest of this Chapter will be devoted to computing the trace of the geometric truncation of $A(\varphi)$ of level $\rho$, for then using the formula from (10.4.2.3) of Theorem 10.4.2.1 to obtain an asymptotic identity between $\mathrm{Trace}\,(A^{\mathrm{spec}}_a(\varphi))$, which involves the zeros of all Hecke $L$-functions of $F$, and the quantity:

$$
2\log(\Lambda)\overline{\mu}_1(C^1_F)\varphi(1)-\mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)) \tag{10.4.2.10}
$$

for $s\ge 0$ and $a$ to be chosen, and for $\Lambda>0$ to be sent to $+\infty$ (with $\varepsilon\Lambda=o(1)$ as $\Lambda\to+\infty$, which forces $\rho\to 1$ pointwise over $C_F$ while remaining nonnegative, continuous and uniformly bounded above by the constant function with value $1$).

Note that for the moment the unknown value of the expression in (10.4.2.10) can only be deduced to converge to a finite limit as $\Lambda\to+\infty$, as a consequence of Theorem 10.4.2.2 and Theorem 10.3.1.1.

Before we can prove Theorem 10.4.2.2, we need the following:

Proposition 10.4.2.4. *Let $F$ be a number field, $a,s$ real numbers, $s\ge 3$. Let $\varphi\in\mathcal{D}(C_F)$ be a test function.*

*The following identity between the traces of the two nuclear operators $P^{\mathrm{spec}}_a\circ A(\varphi)$ on $W^s_I(C_F)$ and $A^{\mathrm{spec}}_a(\varphi)$ on $\mathscr{H}^s_{F,a,I}$ from Theorem 10.3.1.1:*

$$
\mathrm{Trace}\,(P^{\mathrm{spec}}_a\circ A(\varphi))=\mathrm{Trace}\,(A^{\mathrm{spec}}_a(\varphi)) \tag{10.4.2.11}
$$

holds.

Proof. By (10.4.1.11) from Remark 10.4.1.4, we have $P^{\mathrm{spec}}_a\circ A(\varphi)=P^{\mathrm{spec}}_a\circ A(\varphi)\circ P^{\mathrm{spec}}_a$ as continuous operators on $W^s_I(C_F)$.

In particular, since both are nuclear, we have:

$$
\mathrm{Trace}\,(P^{\mathrm{spec}}_a\circ A(\varphi))=\mathrm{Trace}(P^{\mathrm{spec}}_a\circ A(\varphi))=\mathrm{Trace}(P^{\mathrm{spec}}_a\circ A(\varphi)\circ P^{\mathrm{spec}}_a). \tag{10.4.2.12}
$$

By Lemma C.3.2.2, since $P^{\mathrm{spec}}_a\circ A(\varphi)\circ P^{\mathrm{spec}}_a$ factors through the subspace $V:=P^{\mathrm{spec}}_a W^s_I(C_F)$, its trace equals the trace of the unique nuclear operator on $V$ obtained as the restriction $T$ of $P^{\mathrm{spec}}_a\circ A(\varphi)\circ P^{\mathrm{spec}}_a$ to $V$.

The continuous linear quotient homomorphism $Q_a:W^s_I(C_F)\to \mathscr{H}^s_{F,a,I}$ from (10.4.1.3) induces a surjective linear isometry $Q_a:V\to \mathscr{H}^s_{F,a,I}$ with inverse $S_a$ from (10.4.1.5) of Lemma 10.4.1.2.

## PDF page 461

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **461**

We have:

$$
Q_a\circ T\circ S_a=A^{\mathrm{spec}}_a(\varphi) \tag{10.4.2.13}
$$

as nuclear operators on $\mathscr{H}^s_{F,a}$. In particular, we have:

$$
\mathrm{Trace}(Q_a\circ T\circ S_a)=\mathrm{Trace}\,(A^{\mathrm{spec}}_a(\varphi)) \tag{10.4.2.14}
$$

and since $Q_a:V\to \mathscr{H}^s_{F,a}$ is a surjective linear isometry, and $S_a$ is its inverse isometry onto $V$, we deduce that we have:

$$
\mathrm{Trace}(P^{\mathrm{spec}}_a\circ A(\varphi))=\mathrm{Trace}(Q_a\circ T\circ S_a) \tag{10.4.2.15}
$$

and hence (10.4.2.11) holds.

$\square$

Proof of Theorem 10.4.2.2. The operator $P^{\mathrm{spec}}_a\circ A(\varphi)$ is nuclear by Theorem 10.4.2.1, and its trace equals $\mathrm{Trace}\,(A^{\mathrm{spec}}_a(\varphi))$, where $A^{\mathrm{spec}}_a(\varphi)$ is the nuclear operator on $\mathscr{H}^s_{F,a,I}$ from Theorem 10.3.2.1.

The multiplication operators $M_{\rho}$ tend to the identity with respect to the strong operator topology, as $\Lambda\to+\infty$, since the assumption $\varepsilon\Lambda=o(1)$ as $\Lambda\to+\infty$ forces $\rho$ to tend to the constant function with value $1$ pointwise over $C_F$, while remaining nonnegative, multiplicatively symmetric and bounded above by $1$.

The multiplication operator $M_{\rho}$ is self-adjoint, as noted in Remark 9.3.3.2.

By design of $P^{\mathrm{spec}}_{\rho,a}$ from Definition 10.4.1.3, we have $P^{\mathrm{spec}}_{\rho,a}=M_{\rho}\circ P^{\mathrm{spec}}_a$, and hence, by Corollary C.3.5.5, $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)\to P^{\mathrm{spec}}_a\circ A(\varphi)$ in $S_1(W^s_I(C_F))$, i.e. as nuclear operators on $W^s_I(C_F)$. In particular, (10.4.2.9) holds.

$\square$

10.4.2.1. *$\varepsilon$-approximate Kernels.* We record here the following Lemma:

Lemma 10.4.2.5. *Let $E$ be a Banach space, $E_0\subset E$ a closed subspace. Let $||\cdot||_E$ be a norm on $E$ generating the Banach space topology on $E$.*

*Assume $E/E_0$, endowed with the quotient topology, admits a normalized Schauder, respectively Markushevich, basis $\{x_m\}_{m\ge 0}$. Let $\{\varphi_m\}_{m\ge 0}$ be its bi-orthogonal sequence.*

*Let $r,r'>0$ be real numbers such that, upon denoting by $||\cdot||_{E/E_0}$ the induced norm on the quotient $E/E_0$, we have:*

$$
\{x_m\}_{m\ge 0}\subset\{x\in E/E_0:||x||_{E/E_0}\in[r,r']\}. \tag{10.4.2.16}
$$

*Let $F\subset E$ be a linear subspace such that $F_0:=F\cap E_0$ is dense in $E_0$ with respect to the normed topology inherited from $E$. Assume $\{x_m\}_{m\ge 0}\subset F/F_0$.*

*We denote by $\widetilde\varphi_m$ the image of $\varphi_m$ under $(E/E_0)'_{\beta}\to E'_{\beta}$, i.e. the composition of $\varphi_m$ with the quotient $E\to E/E_0$.*

*There exists a subset $\{u_m\}_{m\ge 0}\subset F$ satisfying the following properties:*

(1) *For every pair of integers $m,n\ge 0$, we have:*

$$
\widetilde\varphi_m(u_n)=\delta_{m,n}. \tag{10.4.2.17}
$$

(2) *There exists a number $\varepsilon>0$, with $r>\varepsilon$, such that $\{u_m\}_{m\ge 0}\subset E$ satisfies:*

$$
\{u_m\}_{m\ge 0}\subset\{u\in E:||u||_E\in[r-\varepsilon,r'+\varepsilon]\}. \tag{10.4.2.18}
$$

*In particular, $\{u_m\}_{m\ge 0}$ is a bounded subset of $E$ contained in $F$, and a normalized Schauder basis in the closure of its linear span in $E$.*

*There exists a sequence $\{\delta_m\}$ of small enough positive real numbers such that for any $\{y_m\}_{m\ge 0}\subset F_0$ satisfying $||y_m||_E<\delta_m$ for every integer $m\ge 0$, then $\{u_m+y_m\}_{m\ge 0}$ also satisfies (1) and (2), and the assignment $u_m\mapsto u_m+y_m$ uniquely extends to a linear topological isomorphism from the closure of the linear span of $\{u_m\}_{m\ge 0}$ in $E$, to the closure of the linear span of $\{u_m+y_m\}_{m\ge 0}$ in $E$.*

## PDF page 462

**462** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

Terminology 10.4.2.1. Let $E$ be a Banach space, $E_0\subset E$ a closed subspace, and assume $\{x_m\}_{m\ge 0}\subset E/E_0$ is a normalized Schauder, respectively Markushevich, basis, with bi-orthogonal sequence $\{\varphi_m\}_{m\ge 0}$. Assume $F\subset E$ is a linear subspace such that $F\cap E_0$ is dense in $E_0$, and the linear image of $F$ in $E/E_0$ is dense.

We will be referring to the sequence $\{u_m\}_{m\ge 0}$ satisfying (1) and (2) from Lemma 10.4.2.5, whose existence is provided by the Lemma, as an $\varepsilon$-lift of $\{x_m\}_{m\ge 0}$.

Proof of Lemma 10.4.2.5. We discuss the case of a Schauder basis.$^7$

For each integer $m\ge 0$, we let $u_m\in E$ be a choice of element such that its image under the linear quotient operator $E\to E/E_0$ is $x_m$.

Since $E\to E/E_0$ is open, the linear image of $\{\varphi_m\}_{m\ge 0}$ in $E'_{\beta}$ under the continuous linear operator $(E/E_0)'_{\beta}\to E'_{\beta}$ is a Schauder basis in its closure, since $(E/E_0)'_{\beta}\to E'_{\beta}$ is a linear topological embedding by [NB, Thm.8.13.2] (since by [NB, Thm.8.13.2], the range of $(E/E_0)'_{\beta}\to E'_{\beta}$ is weakly closed, hence strongly closed).

For any $u\in E_0$, we have $\widetilde\varphi_k(u+u_m)=\widetilde\varphi_k(u_m)$, and hence $\widetilde\varphi_k(u_m)=\varphi_k(x_m)=\delta_{m,n}$.

The quotient topology on $E/E_0$ is induced, by [NB, Thm.5.11.2], by the norm

$$
\overline{p}(x):=\inf_{u_0\in E_0}||u_0+u||_E \tag{10.4.2.19}
$$

for $u$ a choice of element of $E$ whose image in $E/E_0$ is $x$.

Since $\{x_m\}_{m\ge 0}$ is bounded and regular (i.e. bounded away from $0\in E/E_0$; see [Kal, §1, Def.1.1, p.91]), there exist real numbers $r,r'>0$ with $r<r'$, such that $r\le \overline{p}(x_m)\le r'$ for each $m\ge 0$.

For each integer $m\ge 0$, and for any $u_m\in E$ as in the foregoing, $u+u_m$ also satisfies the conditions in (10.4.2.17) for any $u\in E_0$.

We fix a real number $\varepsilon>0$.

There therefore exists $u\in E_0$ such that $r\le||u+u_m||_E\le r'+\varepsilon/2$, and $u+u_m$ satisfies the conditions in (10.4.2.17).

This is indeed the case since the distance function from a fixed point of a metric space, is a metric-continuous function.

By assumption, we have $\{x_m\}_{m\ge 0}\subset F/F_0$, and hence we may and do assume that each $u_m$ is an element of $F$.

Since $F_0\subset E_0$ is dense with respect to the normed topology on $E_0$ inherited from $E$, there exists $u'\in F_0$ such that $||u-u'||_E<\varepsilon/2$.

We therefore have:

$$r-\varepsilon/2\le\big|\,||u+u_m||_E-||u-u'||_E\,\big|\le||u'+u_m||_E\le||u+u_m||_E+||u-u'||_E\le r'+\varepsilon.$$

Since $r$ does not depend on $m\ge 0$, we may choose $\varepsilon>0$ small enough so as to have $r-\varepsilon/2\ge r-\varepsilon>0$.

We now let $V\subset E$ be the closure of the linear span of $\{u_m\}_{m\ge 0}$. It follows that $\{\widetilde\varphi_m\}_{m\ge 0}$ is a sequence in $H'$ such that $\widetilde\varphi_m(u_n)=\delta_{m,n}$, which proves that $\{u_m\}_{m\ge 0}$ is a Schauder basis in $V$ by [Jar, Part II, Ch.14, §14.2, Prop.3, p.292], since it its topologically free [Jar, Part II, Ch.14, §14.1, Prop.1, p.290].

For any sequence $\{y_m\}_{m\ge 0}$, the sequence $\{u_m+y_m\}_{m\ge 0}$ is also contained in $F$ and satisfies (1). For $\{y_m\}_{m\ge 0}$ satisfying $||y_m||_E<\delta_m$ for $\delta_m>0$ small enough, we have $||u_m+y_m||_E\in[r-\varepsilon,r'+\varepsilon]$.

Up to choosing a sequence $\{\delta'_m\}_{m\ge 0}$ with $0<\delta'_m\le\delta_m$, the $\{u_m\}_{m\ge 0}$ and $\{u_m+y_m\}_{m\ge 0}$ are equivalent basic sequences by [Meg, Ch.4, Prop.4.3.4, p.387], and hence by [Meg, Ch.4, Prop.4.3.2, p.387] the assignment $u_m\mapsto u_m+y_m$ extends uniquely to a linear topological isomorphism $V\to W$, where $W$ is the closure of the linear span of $\{u_m+y_m\}_{m\ge 0}$ in $E$.

$\square$

---
$^7$Return here.

## PDF page 463

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **463**

Remark 10.4.2.6. We note that the quotient $E\to E/E_0$ in Lemma 10.4.2.5 maps the open unit ball in $E$ surjectively onto the open unit ball in $E/E_0$. If $E$ is reflexive, then it maps the closed unit ball in $E$ surjectively onto the closed unit ball in $E/E_0$ (a consequence of [Jar, Part II, Ch.11, §11.4, Cor.2, p.280], to deduce that continuous linear functionals attain their maximum on the closed unit ball). The requirement that the lift $\{u_m\}_{m\ge 0}$ of the subset $\{x_m\}_{m\ge 0}\subset E/E_0$ contained in the closed collar $\{x\in E/E_0:||x||_{E/E_0}\in[r,r']\}$, should not only be contained in a similar closed collar in $E$ bounded away from $0\in E$, but also be contained in $F$, leads to the necessity of enlarging the closed collar in $E$ from $\{u\in E:||u||_E\in[r,r']\}$ to its closed $\varepsilon$-neighborhood for a small enough choice of $\varepsilon>0$.

Remark 10.4.2.7. The Lemma says that given a normalized Schauder basis of $E/E_0$, we can lift it to a Schauder basic sequence of $E$ contained in a given subspace $F\subset E$ such that $F\cap E_0$ is dense, and the image of $F$ in $E/E_0$ is dense (hence, in particular, $F$ is itself dense in $E$), and upon perturbing such lift a little, to another that satisfies the same properties, the closures of their linear spans are linearly and topologically isomorphic.

If $E$ is a Hilbert space, then we can find $\{u_m\}_{m\ge 0}$ such that its closed linear span is linearly and topologically isomorphic to the orthogonal complement of $E_0$, and hence so are the closed linear spans of all small enough perturbations of $\{u_m\}_{m\ge 0}$.

10.4.2.2. *Spectral Side: convolution after projection.* We can now state and prove the last of the main Theorems of this section:

Theorem 10.4.2.8 (Spectral side: convolution after projection). *Let $F$ be a number field, $a,s$ real numbers, $s\ge 0$. Let $I=[-\alpha,\alpha]\subset\mathbf{R}$ be a compact interval, $\alpha\ge 0$ a real number. We have, for all real numbers $\Lambda,\varepsilon>0$ satisfying $0<1/\Lambda+\varepsilon<\Lambda-\varepsilon$, and $\varepsilon\Lambda=o(1)$ as $\Lambda\to+\infty$, and for a $(\Lambda,\varepsilon)$-cutoff $\rho$ for each pair $(\Lambda,\varepsilon)$:*

$$
\mathrm{Trace}\,(M_{\rho}\circ A(\varphi)\circ P^{\mathrm{spec}}_a)=\mathrm{Trace}\,(A^{\mathrm{spec}}_a(\varphi))+o(1) \tag{10.4.2.20}
$$

*as $\Lambda\to+\infty$, where $A^{\mathrm{spec}}_a(\varphi)$ is the nuclear operator from (10.3.2.2), whose trace is computed by the formula in (10.3.2.3) of Theorem 10.3.2.1.*

Proof. We fix a real number $\varepsilon>0$. Let $\chi\in\widehat{C_F}$ be also fixed. We pick a lift of the Spectral Markushevich basis

$$
\psi_{\chi,t,b,m},\,(t,b)\in\mathbf{R}^2:L(s+b+it,\chi)=0,\,0\le m\le N(\rho_{\chi,t,b,m})-1 \tag{10.4.2.21}
$$

on the $I$-based strip (see (10.2.2.4)) provided by Theorem 10.2.2.1, whose continuous coefficient functionals are, as per the theorem, provided by integration with respect to the Haar measure $\overline{\mu}$ on $C_F$ against the functions of $g\in C_F$:

$$
\eta_{\chi,t,b,m}(g)=\chi(g)|g|^{a+b+it}_F(\log|g|_F)^m,\,(t,b)\in\mathbf{R}^2:L(s+b+it,\chi)=0,\,0\le m\le N(\rho_{\chi,t,b,m})-1 \tag{10.4.2.22}
$$

whose lift we denote by:

$$
\widetilde\psi_{\chi,t,b,m},\,(t,b)\in\mathbf{R}^2:L(s+b+it,\chi)=0,\,0\le m\le N(\rho_{\chi,t,b,m})-1 \tag{10.4.2.23}
$$

such that, upon denoting by $C>0$ the real number serving as upper bound to the $W^s_I$-norms of the basis elements such that $1/C$ serves as a lower bound to their norms ($C>0$ exists by Proposition 10.2.2.2), we have:

$$
1/C-\varepsilon<||\widetilde\psi_{\chi,t,b,m}||_{W^s_I(C_F)}<C+\varepsilon \tag{10.4.2.24}
$$

for all $(t,b)\in\mathbf{R}^2$ such that $L(s+b+it,\chi)=0$ and all integers $0\le m\le N(\rho_{\chi,t,b,m})-1$. We choose $\varepsilon>0$ so as to have $1/C-\varepsilon>0$, and choose the lifts in (10.4.2.23) accordingly.

## PDF page 464

**464** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

The $S_1$-norm of the finite rank operators:

$$
A(\varphi)\,\widetilde\psi_{\chi,t,b,m}\otimes\eta_{\chi,t,b,m}\in W^s_I(C_F)\otimes W^{-s}_I(C_F) \tag{10.4.2.25}
$$

equals their $S_2$-norm (see [Cnw-b, Ch.3, §18, Thm.18.13, p.91]), which is in turn computed as the square of the following integral:

$$
\int_{C_F\times C_F}\left|\int_{C_F}\varphi(g)\,\widetilde\psi_{\chi,t,b,m}(g^{-1}x)\,\mathrm{d}\overline{\mu}(g)\,\eta_{\chi,t,b,m}(y)\right|^2 w_{I,s}(x)w_{I,s}(y)^{-1}\,\mathrm{d}(\overline{\mu}\otimes\overline{\mu})(x,y). \tag{10.4.2.26}
$$

We note that we can arrange the $\widetilde\psi_{\chi,t,b,m}$ to be in $\mathcal{S}_{\mathrm{E}}(C_F)$, by Lemma 10.4.2.5.

We now estimate the integral in (10.4.2.26). We have that the integral in (10.4.2.26) equals:

$$
\int_{C_F\times C_F}\int_{C_F\times C_F}\varphi(g_1)\varphi(g_2)\,\widetilde\psi_{\chi,t,b,m}(g^{-1}_1x)\,\widetilde\psi_{\chi,t,b,m}(g^{-1}_2x)\,\mathrm{d}(\overline{\mu}\otimes\overline{\mu})(g_1,g_2)\,\eta_{\chi,t,b,m}(y)^2\,w_{I,s}(x)w_{I,s}(y)^{-1}\,\mathrm{d}(\overline{\mu}\otimes\overline{\mu})(x,y). \tag{10.4.2.27}
$$

By Fubini’s Theorem (see [Fol, Thm.7.28]) and shearing under the transformation $(x,y)\mapsto(g_1x,g_1y)$, we obtain that the integral in (10.4.2.27) equals:

$$
\int_{C_F\times C_F}\widetilde\psi_{\chi,t,b,m}(x)\int_{C_F\times C_F}\varphi(g_1)\varphi(g_2)\,\widetilde\psi_{\chi,t,b,m}(g^{-1}_2g_1x)\,\eta_{\chi,t,b,m}(g_1y)^2\,w_{I,s}(g_1x)w_{I,s}(g_1y)^{-1}\,\mathrm{d}(\overline{\mu}\otimes\overline{\mu})(x,y)\,\mathrm{d}(\overline{\mu}\otimes\overline{\mu})(g_1,g_2). \tag{10.4.2.28}
$$

We have:

$$
\eta_{\chi,t,b,m}(gy)=\chi(gy)|gy|^{b+it}_F(\log|gy|_F)^m \tag{10.4.2.29}
$$

$$
=\chi(g)\chi(y)|g|^{b+it}_F|y|^{b+it}_F(\log|g|_F+\log|y|_F)^m \tag{10.4.2.30}
$$

$$
=\chi(g)\chi(y)|g|^{b+it}_F|y|^{b+it}_F\sum_{0\le i\le m}\binom{m}{i}(\log|g|_F)^i(\log|y|_F)^{m-i} \tag{10.4.2.31}
$$

$$
=\chi(g)|g|^{b+it}_F\sum_{0\le i\le m}\binom{m}{i}(\log|g|_F)^i\,\{\chi(y)|y|^{b+it}_F(\log|y|_F)^{m-i}\} \tag{10.4.2.32}
$$

$$
=\sum_{0\le i\le m}\binom{m}{i}\chi(g)|g|^{b+it}_F(\log|g|_F)^i\cdot\eta_{\chi,t,b,m-i}(y). \tag{10.4.2.33}
$$

Using the estimate in (9.3.1.6) from Lemma 9.3.1.5, combined with (10.4.2.29) and un-doing the shearing, we obtain that up to a positive real constant independent of the choice label $(\chi,t,b,m)$, the following sum is an upper bound for the $S_2$-norm, and hence the $S_1$-norm, of (10.4.2.25):

$$
\sum_{k\ge 0}\sum_{j\ge 0}\left(N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})2^{N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})-1}\sum_{0\le i\le N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})-1}|M(\varphi)^{(i)}(b_{k,j}+it_{k,j})|\right)^2 \tag{10.4.2.34}
$$

The argument for the proof of Theorem 10.3.2.1 can now be repeated, giving that the $S_1$-limit of the sum of the rank-1 operators from (10.4.2.25) exists and agrees with $A(\varphi)\circ P^{\mathrm{spec}}_a$, which is therefore nuclear and has the same trace as $P^{\mathrm{spec}}_a\circ A(\varphi)$. The remaining assertions of the Theorem follow as a consequence.$^8$

$\square$

10.4.3. Spectral Kernels.

10.4.3.1. *Spectral kernels: the case $I=\{0\}$.* We let $F$ be a number field and $\chi\in\widehat{C_F}$ a continuous character. We choose a continuous homomorphic section $\tau$ to the idelic norm.

---
$^8$Return here and complete proof.

## PDF page 465

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **465**

We defined:

$$
\Lambda(s,\chi):=\left(\frac{1}{2}s(s-1)\right)^{\delta_{\chi}}L(s,\chi) \tag{10.4.3.1}
$$

where $L(s,\chi)=L(\chi|\cdot|^s_F)$ is the Hecke $L$-function, and $\delta_{\chi}=1$ if $\chi|_{C^1_F}=1$, and $\delta_{\chi}=0$ if $\chi|_{C^1_F}\ne 1$.

The completion map $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})\to W^{s,2}(C_F)(\chi|_{C^1_F})$ fits into a commutative diagram of continuous linear operators:

(10.4.3.2)

```latex
\begin{tikzcd}
0 \arrow[r] & W_{\chi} \arrow[r] \arrow[d, "L^{-1}"'] & A\mathcal S(\mathbf C) \arrow[r] \arrow[d, "M^{-1}"'] & K_{\chi}:=A\mathcal S(\mathbf C)/W_{\chi} \arrow[r] \arrow[d, "M^{-1}"] & 0 \\
0 \arrow[r] & \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \arrow[r] \arrow[d] & \mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F}) \arrow[r] \arrow[d] & \check K_{\chi} \arrow[r] \arrow[d] & 0 \\
0 \arrow[r] & W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)) \arrow[r] & W^{s,2}(C_F)(\chi|_{C^1_F}) \arrow[r] & \mathscr{H}^s_{F,a}(\chi|_{C^1_F}) \arrow[r] & 0
\end{tikzcd}
```

for:

$$
W_{\chi}:=\Lambda(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)
$$

topologized, in light of Theorem 6.3.2.1, with the subspace topology inherited from the separable nuclear Fréchet space $A\mathcal S(\mathbf C)$, and where the notation $\mathscr{H}^s_{F,a}(\chi|_{C^1_F})$ was introduced in (10.2.1.1), where $K_{\chi}$ is the subquotient $A\mathcal S(\mathbf C)/W_{\chi}$, and $\check K_{\chi}$ is its image under the anti-transform $M^{-1}$, where $M$ is the Mellin transform $\phi\mapsto\int_{C_F}\phi(g)\chi(g)|g|^s_F\,\mathrm{d}\overline{\mu}(g)$, where $\chi$ is the fixed character of $C_F$, noting that $M$ restricts to $L$ from (5.2.3.14) on $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

We refer the reader to the discussion on the Mellin transform on $\mathbf R_{>0}$-modulated groups from Discussion 4.4.1.1, and we recall that the operator $M$ in the foregoing is related to $M_I$ for $I=\mathbf R$ by a vertical translation by $ix_0$ on the holomorphic coordinate $s$, which depends on the choice of $\tau$, and on the continuous character $\chi\in\widehat{C_F}$: $x_0\in\mathbf R$ is the unique real number such that $\chi(\tau(t))=t^{ix_0}$ as smooth functions of $t\in\mathbf R_{>0}$.

The bottom vertical arrows are all induced by the norm-completion with respect to the $\|\cdot\|_{s,2}$-norm topology on $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$, and on $|\cdot|^a_F\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))\subset\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$.

They are all injective since the norm topology on $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$ is Hausdorff, and hence so is on its closed (by Theorem 6.3.2.1) subspace $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$, and on the subspace $|\cdot|^a_F\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ (being multiplication by the quasi-character $|\cdot|^a_F$ a continuous continuously (equivalently boundedly, since $\mathcal S_{\mathrm E}(G)$ is bornological, for $G$ a second-countable $\mathbf R_{>0}$-modulated group; see Theorem D.3.3.7(1)) invertible automorphism on $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$, due to the exponential decay of the elements on $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$ and being the Hausdorff locally convex topology on $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$ defined to be, under Mellin transform, that which induces the topology of uniform convergence on the vertical strips of bounded width within $\mathbf C$; see Lemma D.3.1.2 and Theorem D.3.3.13).

By Theorem 6.3.2.1), $L^{-1}$, the top leftmost vertical arrow in (10.4.3.2), is a linear topological isomorphism. So is $M^{-1}$ in the top middle vertical arrow of (10.4.3.2).

It is the content of Theorem 7.1.4.2 that the strong dual $(\check K_{\chi})'_{\beta}$ admits a countable set of linear topological generators given by point-evaluation functionals supported at the zeors of $\Lambda(s,\chi)$ (shifted by $a$ to the left), and their derivatives of order strictly bounded above by the multiplicity of the zero.

Let $(\rho,m)$ be a pair comprising a zero of $L(s,\chi)$ of mutiplicity $N(\rho)$, and $m$ an integer satisfying $0\le m\le N(\rho)-1$.

Such continuous functionals in $(\check K_{\chi})'_{\beta}$ are, for each $(\rho,m)$, given explicitly by the assignment:

$$
D_{\rho,m}:\phi\mapsto\int_{C_F}\phi(g)\chi(g)|g|^{\rho}_F(\log|g|_F)^m\,\mathrm{d}\overline{\mu}(g). \tag{10.4.3.3}
$$

## PDF page 466

**466** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

Multiplication by the quasi-character $|\cdot|^a_F$ on $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$, which is a linear topological automorphism on $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$, sends $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ to $|\cdot|^a_F\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ as closed subspaces of $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$, and its adjoint sends each $D_{\rho,m}$ from (10.4.3.3) to the functionals:

$$
D_{-a+\rho,m}:\phi\mapsto\int_{C_F}\phi(g)\chi(g)|g|^{\rho-a}_F(\log|g|_F)^m\,\mathrm{d}\overline{\mu}(g) \tag{10.4.3.4}
$$

where now $\rho-a$ is a zero of $L(s+a,\chi)$.

In particular, for any real number $a$, and for each pair $(\rho,m)$ such that $a+\rho$ is a zero of $L(s,\chi)$ of multiplicity $N(a+\rho)$, and $m$ is an integer $0\le m\le N(a+\rho)-1$, there exists a unique bi-orthogonal sequence of elements $\psi_{a+\rho,m}\in\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$ satisfying:

$$
D_{a+\rho,m}(\psi_{a+\rho',m'})=\delta_{(a+\rho,m),(a+\rho',m')} \tag{10.4.3.5}
$$

with $\delta_{(a+\rho,m),(a+\rho',m')}=1$ for $(a+\rho,m)=(a+\rho',m')$, and $\delta_{(a+\rho,m),(a+\rho',m')}=0$ otherwise. This is a consequence of the explicit construction of the functions $\phi_{\rho,m}$ in the proof of Theorem 7.1.4.2.

We denote, for each zero $a+\rho$ of $L(s,\chi)$, by:

$$
\check K_{\chi,a+\rho}:=\sum_{0\le m\le N(a+\rho)-1}\mathbf C\psi_{a+\rho,m}\subset\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F}) \tag{10.4.3.6}
$$

the finite dimensional $\mathbf C$-linear subspace generated by the finite collection $\{\psi_{(a+\rho,m)},0\le m\le N(a+\rho)-1\}$.

Since the $\|\cdot\|_{s,2}$-norm topology on $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})$ is, for every real number $s\ge 0$, separated, the finite dimensional linear subspace $\check K_{\chi,a+\rho}$ is mapped injectively into $W^{s,2}(C_F)$ under the completion map $\mathcal S_{\mathrm E}(C_F)(\chi|_{C^1_F})\to W^{s,2}(C_F)(\chi|_{C^1_F})\subset W^{s,2}(C_F)$.

These observations were made throughout the proof of Theorem 10.3.1.1.

In this subsection, we discuss the “spectral side” of the Trace Formula, i.e. we compute the limit as $\Lambda\to+\infty$ of $\mathrm{Trace}\,P^{\mathrm{spec}}_{\Lambda,a}\circ A(\varphi)$, for any $a\in\mathbf R$, $s>1$, and $\varphi\in\mathcal D(C_F)$.

We begin with the following consequence of Theorem 10.2.1.1 and Theorem 10.3.1.1.

We recall that for $X,Y$ two Hausdorff locally compact second countable topological spaces, and $\mu$ a Radon measure on $X$ and $\nu$ a Radon measure on $Y$, then

$$
S_2(L^2(X,\mu),L^2(Y,\nu))=L^2(X\times Y,\mu\otimes\nu) \tag{10.4.3.7}
$$

the source being the Hilbert space of Hilbert-Schmidt operators $L^2(X,\mu)\to L^2(Y,\nu)$, i.e. every Hilbert-Schmidt operator $T:L^2(X,\mu)\to L^2(Y,\nu)$ is obtained by integration against a unique kernel function $k\in L^2(X\times Y,\mu\otimes\nu)$:

$$
(T\phi)(y)=\int_X k(x,y)\phi(x)\,\mathrm{d}\mu(x) \tag{10.4.3.8}
$$

for almost all $y\in Y$.

We further refer the reader to [Jar, Part III,Ch.17,§17.6,p.391], to (C.3.6.5) and to Proposition C.3.6.4.

Theorem 10.4.3.1 (Spectral and Geometric kernels - I). Let $F$ be a number field.

*Let $a,s$ be real numbers, with $a>0$ and $s>1$. Let $\varphi\in\mathcal D(C_F)$ be a test function.*

*We choose an enumeration for the set of triples $Z:=\{\chi,t,m\}$ as follows:*

(1) *We choose an enumeration for the set of continuous characters $\chi$ of the base-points of the connected components of $\Omega(C_F)$ chosen in the holomorphic parametrization from (10.2.1.4) of Notation 10.2.1.1, and denote it $\{\chi_k\}_{k\ge 0}$.*

(2) *For each integer $k\ge 0$, we choose an enumeration $\{t_{k,j}\}_{j\ge 0}$, for the set of real numbers $t\in\mathbf R$ such that $\rho_{\chi_k,t}:=\chi_k|\cdot|^{a+it}_F$ is a zero of $L(s,\chi_k)$, of multiplicity denoted by $N(\rho_{\chi_k,t})$, and we choose the enumeration for the $t_{k,j}$ so as to have $|t_{k,j}|\le|t_{k,j+1}|$ for all integers $j\ge 0$.*

## PDF page 467

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **467**

(3) *For each pair $(\chi_k,t_{k,j})$, we enumerate the finitely many integers $m\ge 0$ satisfying $m\le N_s(\rho_{\chi_k,t_{k,j}})-1$, with $N_s(\rho_{\chi_k,t_{k,j}})$ defined in (10.2.1.6) by:*

$$
N_s(\rho_{\chi_k,t_{k,j}})=\min\left\{N(\rho_{\chi_k,t_{k,j}}),\left[\frac{s-1}{2}+1\right]\right\} \tag{10.4.3.9}
$$

*according to their natural increasing ordering.*

(4) *For each such $\chi$, the induced enumeration of the subset $Z_{\chi}\subset Z$ of those triples such that the first entry is $\chi$, is lexicographical.*

*and denote by $\{\psi_{\chi,t,m}\}_{\chi,t,m}\subset \mathscr{H}^s_{F,a}$ the dual Markushevich basis in $\mathscr{H}^s_{F,a}$ to the Markushevich basis for $(\mathscr{H}^s_{F,a})'_{\beta}$ obtained as the image of the functions:*

$$
\eta_{\chi,t,m}:=\chi|\cdot|^{it}_F(\log|\cdot|_F)^m \tag{10.4.3.10}
$$

*under the inverse of the isometry $T_s:W^{s,2}(C_F)'_{\beta}\to W^{-s,2}(C_F)$ from (9.1.2.14), provided by Theorem 10.2.1.1 for the strong dual $(\mathscr{H}^s_{F,a})'_{\beta}$, where $\mathscr{H}^s_{F,a}$ is the Hilbert space quotient of $W^{s,2}(C_F)$ by $W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^{\times},\mathcal S_0(\mathbf A_F))$ defined in (10.2.1.1).*

We denote by:

$$
I:=\{(k,j,m_{k,j})\in\mathbf N^3:k\ge 0,j\ge 0,0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1\} \tag{10.4.3.11}
$$

*ordered lexicographically from the lexicographic ordering on $\mathbf N^3$.*

Then:

(1) *The effect of the canonical linear isometry $S_a:\mathscr{H}^s_{F,a}\to P^{\mathrm{spec}}_aW^{s,2}(C_F)$ from (10.4.1.5), inverse to the quotient $P^{\mathrm{spec}}_aW^{s,2}(C_F)\to \mathscr{H}^s_{F,a}$, on the basis elements $\{\psi_{\chi,t,m}\}_{\chi,t,m}\subset \mathscr{H}^s_{F,a}$, is described as follows: for each $(\chi,t,m)\in Z$ according to the chosen enumeration, we make a choice of an element $\widetilde\psi_{\chi,t,m}\in W^{s,2}(C_F)$ whose image in $\mathscr{H}^s_{F,a}$ is $\psi_{\chi,t,m}$. Then:*

$$
S_a(\psi_{\chi,t,m})=P^{\mathrm{spec}}_a(\widetilde\psi_{\chi,t,m}). \tag{10.4.3.12}
$$

(2) *The sequences of finite rank kernels:*

$$
\sum_{i\in I}\langle A(\varphi)'\eta_{(\chi,t,m)_i},\cdot\rangle_{s,2}\otimes\psi_{(\chi,t,m)_i}=\sum_{0\le k\le N_1}\sum_{0\le j\le N_2}\sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1}\langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},\cdot\rangle_{s,2}\otimes\psi_{\chi_k,t_{k,j},m_{k,j}} \tag{10.4.3.13}
$$

in $(\mathscr{H}^s_{F,a})'_{\beta}\widehat\otimes_{\pi}(\mathscr{H}^s_{F,a})$, and:

$$
\sum_{i\in I}A(\varphi)'\eta_{(\chi,t,m)_i}\otimes S_a(\psi_{(\chi,t,m)_i})=\sum_{0\le k\le N_1}\sum_{0\le j\le N_2}\sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1}A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}}\otimes S_a(\psi_{\chi_k,t_{k,j},m_{k,j}}) \tag{10.4.3.14}
$$

*in $W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F)$, converge as $(N_1,N_2)\to(+\infty,+\infty)$ in $\mathbf N\times\mathbf N$, equivalently $i\to+\infty$ in $I$, with respect to the respective projective tensor product topologies.*

(3) Let:

$$
\xi_{\pi}:W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F)\to\mathscr{L}_{\beta}(W^{s,2}(C_F)) \tag{10.4.3.15}
$$

*be the composition of $T^{-1}_s\widehat\otimes_{\pi}\mathrm{Id}$ and the continuous injective linear operator $\chi_{\pi}$ from Proposition C.3.6.4, whose effect on finite rank kernels is that of associating to $\sum_{1\le k\le N}\phi_k\otimes\psi_k$ the finite rank operator $\sum_{1\le k\le N}\langle\phi_k,\cdot\rangle_{s,2}\psi_k$. Upon denoting by $K^{\mathrm{spec}}_{\varphi,a,s}$ the limit in $W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F)$ of the finite rank kernels from (10.4.3.14), then we have, within $\mathscr{L}_{\beta}(W^{s,2}(C_F))$:*

$$
\xi_{\pi}(K^{\mathrm{spec}}_{\varphi,a,s})=P^{\mathrm{spec}}_a\circ A(\varphi). \tag{10.4.3.16}
$$

## PDF page 468

**468** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

The sequence of finite rank operators in (10.3.1.1) was shown to converge in $S_1(\mathscr{H}^s_{F,a})$ throughout the proof of Theorem 10.3.1.1.

Proof. (1) follows from Lemma 10.4.1.2.

Directly, let $Q_a$ be the quotient linear operator from $W^{s,2}(C_F)$ to $\mathscr{H}^s_{F,a}$ from (10.4.1.3).

$S_a$ is the inverse of the restriction of $Q_a$ to $P^{\mathrm{spec}}_aW^{s,2}(C_F)$: such restriction is continuous, open and bijective onto $\mathscr{H}^s_{F,a}$, hence an isometric linear topological isomorphism (see [Tre, Part I,Ch.17,Thm.17.1]).

For each basis element $\psi_{\chi,t,m}\in \mathscr{H}^s_{F,a}$, the choice of lift $\widetilde\psi_{\chi,t,m}$ satisfies

$$
S^{-1}_a(\widetilde\psi_{\chi,t,m})=S^{-1}_a(P^{\mathrm{spec}}_a(\widetilde\psi_{\chi,t,m}))=Q_a(P^{\mathrm{spec}}_a(\widetilde\psi_{\chi,t,m}))=\psi_{\chi,t,m} \tag{10.4.3.17}
$$

where the first identity is a consequence of the containment

$$
P^{\mathrm{geom}}_aW^{s,2}(C_F)=W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^{\times},\mathcal S_0(\mathbf A_F))\subset\ker(Q_a)
$$

and orthogonality in $W^{s,2}(C_F)$ of $P^{\mathrm{geom}}_aW^{s,2}(C_F)$ to the range of $S_a$.

Upon evaluating $S_a$ on both the sides of the rightmost identity (10.4.3.17), we obtain:

$$
P^{\mathrm{spec}}_a(\widetilde\psi_{\chi,t,m})=S_a(\psi_{\chi,t,m}) \tag{10.4.3.18}
$$

and so (10.4.3.12) holds.

(2) : Since $S_a$ is a linear isometry, the image of a Markushevich basis for $\mathscr{H}^s_{F,a}$ is a Schauder basis for $P^{\mathrm{spec}}_aW^{s,2}(C_F)$, since linear isometries respect topologically free sequences (the duality $\langle P^{\mathrm{spec}}_aW^{s,2}(C_F),(P^{\mathrm{spec}}_a)'W^{-s,2}(C_F)\rangle$ is induced by the duality $\langle\cdot,\cdot\rangle_{s,2}$, with respect to which the continuous adjoint of $P^{\mathrm{spec}}_a$ is being defined).

By Theorem 10.2.1.1

$$
\{\eta_{\chi_k,t_{k,j},m_{k,j}}\}_{k\ge 0,j\ge 0,0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1}
$$

is the image under the isometric isomorphism $T_s:W^{s,2}(C_F)'_{\beta}\to W^{-s,2}(C_F)$ of (9.1.2.14), of a Markushevich basis for $(\mathscr{H}^s_{F,a})'_{\beta}$, and $\{\psi_{\chi_k,t_{k,j},m_{k,j}}\}_{k\ge 0,j\ge 0,0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1}$ is its dual basis in $\mathscr{H}^s_{F,a}$, itself a Markushevich basis, for $\mathscr{H}^s_{F,a}$, with the dualities on sources and targets defined accordingly.

This means that the functionals:

$$
\langle\eta_{\chi_k,t_{k,j},m_{k,j}},\cdot\rangle_{s,2}:W^{s,2}(C_F)\to\mathbf C
$$

each of which factors through $\mathscr{H}^s_{F,a}$ defining a unique continuous functional on $\mathscr{H}^s_{F,a}$, i.e. an element of the strong dual $(\mathscr{H}^s_{F,a})'_{\beta}$, are a Markushevich basis for $(\mathscr{H}^s_{F,a})'_{\beta}$, as $(k,j,m_{k,j})$ ranges over the countable set

$$
I:=\{(k,j,m_{k,j})\in\mathbf N^3:k\ge 0,j\ge 0,0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1\}
$$

as in (10.4.3.11).

We note that the concept of “diverging to infinity” for sequences in $I$ is already intrinsically defined, inherited from $\mathbf N\times\mathbf N\times\mathbf N$. It reads as follows: $i\to+\infty$ if and only if, writing $i=(k(i),j(i),m_{k(i),j(i)})$, we have $(k(i),j(i))\to(+\infty,+\infty)$ in $\mathbf N\times\mathbf N$. In other words, “infinity” within $I$ is the subset of the closure $\bar I$ of $I$ within the one-point compactification of the countable discrete set $\mathbf N\times\mathbf N\times(\mathbf N\cap[0,C_s])$ with $C_s:=[(s-1)/2+1]$, obtained as $\bar I-I$, which is contained within $(+\infty,+\infty)\times(\mathbf N\cap[0,C_s])$.

By Corollary 10.2.1.4, each of the two Markushevich bases is normalized (we refer the reader to Terminology 10.2.1.2 for this lexicon, and to the discussion preceding Corollary 10.2.1.4 and Corollary 11.2.0.5).

The sequence of finite rank kernels from (10.4.3.13):

$$
\sum_{0\le k\le N_1}\sum_{0\le j\le N_2}\sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1}\langle A(\varphi)'\eta_{\chi_k,t_{k,j},m_{k,j}},\cdot\rangle_{s,2}\otimes\psi_{\chi_k,t_{k,j},m_{k,j}} \tag{10.4.3.19}
$$

## PDF page 469

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **469**

in $(\mathscr{H}^s_{F,a})'_{\beta}\otimes \mathscr{H}^s_{F,a}$ converge in $(\mathscr{H}^s_{F,a})'_{\beta}\widehat\otimes_{\pi}\mathscr{H}^s_{F,a}$.

Indeed, the sequence of finite rank operators in $\mathscr{L}(\mathscr{H}^s_{F,a})$ from (10.3.1.1) converges in $S_p(\mathscr{H}^s_{F,a})$ for every $p\ge 1$ by Theorem 10.3.1.1(1).

In particular, the sequence of finite rank kernels in (10.4.3.13) converges in $(\mathscr{H}^s_{F,a})'_{\beta}\widehat\otimes_{\pi}\mathscr{H}^s_{F,a}$, since $(\mathscr{H}^s_{F,a})'_{\beta}\widehat\otimes_{\pi}\mathscr{H}^s_{F,a}$ is isometric to $S_1(\mathscr{H}^s_{F,a})$ under the continuous linear operator $\chi_{\pi}$ of (C.3.6.7) from Proposition C.3.6.4.

This establishes both convergence assertions in (2).

The Hilbert space $(\mathscr{H}^s_{F,a})'_{\beta}$ is a closed Hilbert subspace of $W^{s,2}(C_F)'_{\beta}$, which in turn is mapped isometrically isomorphically onto $W^{-s,2}(C_F)$ by $T_s$ from (9.1.2.14) of Proposition 9.1.2.5.

The effect of $T_s$ on the continuous functional $\langle\eta_{(\chi,t,m)_i},\cdot\rangle_{s,2}$ on $\mathscr{H}^s_{F,a}$ is that of sending it to the function $\eta_{(\chi,t,m)_i}\in W^{-s,2}(C_F)$, for each index $i\in I$.

$T_s$ is compatible with the adjoint action of $C_F$ on $(\mathscr{H}^s_{F,a})'_{\beta}$ (induced by the action on $W^{s,2}(C_F)$, on the closed $C_F$-invariant subspace $W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^{\times},\mathcal S_0(\mathbf A_F))$, and hence on the quotient $\mathscr{H}^s_{F,a}$), and so we have:

$$
T_s(\langle A(\varphi)'\eta_{(\chi,t,m)_i},\cdot\rangle_{s,2})=T_s(A(\varphi)'\langle\eta_{(\chi,t,m)_i},\cdot\rangle_{s,2})=A(\varphi)'\eta_{(\chi,t,m)_i}
$$

for every index $i\in I$.

Since $S_a:\mathscr{H}^s_{F,a}\to P^{\mathrm{spec}}_aW^{s,2}(C_F)$ is a surjective linear isometry, as is $T_s$ onto its own image in $W^{-s,2}(C_F)$, we deduce that the topology induced on the tensor product on the source of

$$
T_s\widehat\otimes_{\pi}S_a:(\mathscr{H}^s_{F,a})'_{\beta}\widehat\otimes_{\pi}\mathscr{H}^s_{F,a}\to W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F) \tag{10.4.3.20}
$$

by the projective tensor product topology on the target, is the projective tensor product topology.

Indeed, both $T_s$ and $S_a$ are linear topological embeddings whose range is closed and linearly and topologically complemented, being each linear isometries, and being their sources and targets Hilbert spaces. By [Jar, Part III,Ch.15,§15.2,Prop.3(b),p.327], combined with [Jar, Part III,Ch.15,§15.2,Prop.1,p.326], $T_s\otimes S_a$ is a linear topological isomorphism onto its range, and its range $W$ is a linearly and topologically complemented subspace of $W^{-s,2}(C_F)\otimes_{\pi}W^{s,2}(C_F)$.

The unique linear topological isomorphism induced by [Jar, Part I,Ch.3,§3.4,Thm.2,p.61] between the completions of source and target is $(T_s\otimes S_a)^{\wedge}:(\mathscr{H}^s_{F,a})'_{\beta}\widehat\otimes_{\pi}\mathscr{H}^s_{F,a}\to\widehat{W}$ agrees with $T_s\widehat\otimes_{\pi}S_a$, because, by [Jar, Part I,Ch.3,§3.4,Thm.2,p.61], $\widehat{W}\subset W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F)$ is also closed and linearly and topologically complemented (which is seen by applying [Jar, Part I,Ch.3,§3.4,Thm.2,p.61] to the continuous section splitting the linear topological embedding $W\subset W^{-s,2}(C_F)\otimes_{\pi}W^{s,2}(C_F)$) in particular, it carries the subspace topology.

We further refer the reader to [Tre, Part III,Ch.43,Rem.43.2,p.442].

The image under $T_s\otimes S_a$ of the finite rank kernel in (10.4.3.19) is, for each index $i_0\in I$:

$$
\sum_{i\in I,i\le i_0}A(\varphi)'\eta_{(\chi,t,m)_i}\otimes S_a(\psi_{(\chi,t,m)_i})\in W^{-s,2}(C_F)\otimes_{\pi}W^{s,2}(C_F)\subset W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F) \tag{10.4.3.21}
$$

where we have used that the projective tensor product topology on $W^{-s,2}(C_F)\otimes W^{s,2}(C_F)$ is Hausdorff by [Jar, Part III,Ch.15,§15.1,Prop.3,p.325].

Since the sequence of finite rank kernels in (10.4.3.19) converges in $(\mathscr{H}^s_{F,a})'_{\beta}\widehat\otimes_{\pi}\mathscr{H}^s_{F,a}$ by Theorem 10.2.1.1, Corollary 10.2.1.4 and Theorem 10.3.1.1, then so does the sequence of finite rank tensors in $W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F)$ in (10.4.3.21), since it is obtained as its image under $T_s\widehat\otimes_{\pi}S_a$.

(3) : The continuous linear endomorphism $\xi_{\pi}(K^{\mathrm{spec}}_{\varphi,a,s})$ acts on each element $\phi\in W^{s,2}(C_F)$ as follows:

$$
\xi_{\pi}(K^{\mathrm{spec}}_{\varphi,a,s})(\phi)=\sum_{k\ge 0}\langle A'(\varphi)\eta_{\chi_k,t_k,m_k},\phi\rangle_{s,2}S_a(\psi_{\chi_k,t_k,m_k}) \tag{10.4.3.22}
$$

and since $P^{\mathrm{spec}}_a\circ A(\varphi)=P^{\mathrm{spec}}_a\circ A(\varphi)\circ P^{\mathrm{spec}}_a$, it is enough to check that for each $\phi$ of the form $S_a(\psi)$ for some $\psi\in \mathscr{H}^s_{F,a}$, the effects of $P^{\mathrm{spec}}_a\circ A(\varphi)$ and of $\xi_{\pi}(K^{\mathrm{spec}}_{\varphi,a,s})$ agree.

## PDF page 470

**470** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

Since $\{\psi_{\chi_k,t_{k},m_k}\}_{k\ge 0}$ is a Markushevich basis for $\mathscr{H}^s_{F,a}$, it is enough to show the assertion for $\phi=S_a(\psi_{\chi,t,m})$.

The assertion in this case is proved as a consequence of the calculation in (10.3.1.8), and Lemma 10.4.1.2.

The rest of the assertions in (3) are a consequence of Proposition C.3.6.4.

$\square$

The continuous linear map:

$$
\xi_{\pi}:W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F)\to\mathscr{L}_{\beta}(W^{s,2}(C_F))
$$

from (10.4.3.15) factors through the continuous linear operator

$$
W^{-s,2}(C_F)\widehat\otimes_{\pi}W^{s,2}(C_F)\to W^{-s,2}(C_F)\widehat\otimes_{\sigma}W^{s,2}(C_F) \tag{10.4.3.23}
$$

the target being the Hilbert-Schmidt tensor product from Proposition C.3.6.4.

There is a continuous linear isometry:

$$
W^{-s,2}(C_F)\widehat\otimes_{\sigma}W^{s,2}(C_F)\to L^2(C_F\times C_F,(1+|\log|\cdot|_F|^2)^{-s/2}\overline{\mu}\otimes(1+|\log|\cdot|_F|^2)^{s/2}\overline{\mu}) \tag{10.4.3.24}
$$

The image of $K^{\mathrm{spec}}_{\varphi,a,s}$ under the composition of the continuous linear operator from (10.4.3.23) with the continuous linear isometry from (10.4.3.24) is the unique element

$$
k\in L^2(C_F\times C_F,(1+|\log|\cdot|_F|^2)^{-s/2}\overline{\mu}\otimes(1+|\log|\cdot|_F|^2)^{s/2}\overline{\mu})
$$

such that, for every $\phi\in W^{s,2}(C_F)$:

$$
\int_{C_F}k(x,y)\phi(y)\,(1+|\log|y|_F|^2)^{-s/2}\mathrm{d}\overline{\mu}(y)=(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi)(x) \tag{10.4.3.25}
$$

for $\overline{\mu}$-almost all $x\in C_F$.

Definition 10.4.3.2 (Global Spectral and Geometric Kernels - the case $I=\{0\}$). Let $F$ be a number field, $a,s$ real numbers, $s\ge 3$.

We define:

(1) The measurable function on $C_F\times C_F$:

$$
k^{\mathrm{spec}}_{\varphi,a,s}(x,y):=k(x,y)(1+|\log|y|_F|^2)^{-s/2}. \tag{10.4.3.26}
$$

We refer to $k^{\mathrm{spec}}_{\varphi,a,s}$ as the Global Spectral Kernel of the $\varphi$-regularized action of $C_F$ on $W^{s,2}(C_F)$.

(2) The measurable function on $C_F\times C_F$:

$$
k^{\mathrm{geom}}_{\varphi,a,s}(x,y):=\varphi(xy^{-1})-k^{\mathrm{spec}}_{\varphi,a,s}(x,y) \tag{10.4.3.27}
$$

We refer to $k^{\mathrm{geom}}_{\varphi,a,s}$ as the Global Geometric Kernel of the $\varphi$-regularized action of $C_F$ on $W^{s,2}(C_F)$.

Remark 10.4.3.3. The function $k^{\mathrm{spec}}_{\varphi,a,s}$ satisfies, for every $\phi\in W^{s,2}(C_F)$:

$$
\int_{C_F}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)\phi(y)\,\mathrm{d}\overline{\mu}(y)=P^{\mathrm{spec}}_a\circ A(\varphi) \tag{10.4.3.28}
$$

for $\overline{\mu}$-almost all $x\in C_F$, as a consequence of (10.4.3.25).

Theorem 10.4.3.4. *Let $F$ be a number field, $a,s$ real numbers, $a>0$, $s>1$. Let $\Lambda,\varepsilon>0$ be real numbers, such that $0<1/\Lambda+\varepsilon<\Lambda-\varepsilon$. Let $\rho:C_F\to\mathbf C$ be a $(\Lambda,\varepsilon)$-cutoff.*

(1) *For any $\phi\in W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^{\times},\mathcal S_0(\mathbf A_F))$, we have, for $\overline{\mu}$-almost all $x\in C_F$:*

$$
A(\varphi)(\phi)(x)=(P^{\mathrm{geom}}_a\circ A(\varphi))(\phi)(x)=\int_{C_F}k^{\mathrm{geom}}_{\varphi,a,s}(x,y)\phi(y)\,\mathrm{d}\overline{\mu}(y). \tag{10.4.3.29}
$$

(2) The functions:

$$
(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y),\quad \rho(x)\,(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y) \tag{10.4.3.30}
$$

## PDF page 471

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **471**

*are representative functions for the Hilbert-Schmidt kernel in $L^2(C_F\times C_F,((1+|\log|\cdot|_F|^2)^{s/2}\overline{\mu})^{\otimes 2})$ of the operator $P^{\mathrm{spec}}_a\circ A(\varphi)$ on $W^{s,2}(C_F)$, respectively for the Hilbert-Schmidt kernel in $L^2(C_F\times C_F,((1+|\log|\cdot|_F|^2)^{s/2}\overline{\mu})^{\otimes 2})$ of the operator $P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)$ on $W^{s,2}(C_F)$.*

(3) The function:

$$
(1+|\log|y|_F|^2)^{-s/2}\rho(x)\,k^{\mathrm{geom}}_{\varphi,a,s}(x,y) \tag{10.4.3.31}
$$

*is a representative function for the Hilbert-Schmidt kernel of the operator $P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)$ on $W^{s,2}(C_F)$.*

Proof. (1) : We compute:

$$
\int_{C_F}k^{\mathrm{geom}}_{\varphi,a,s}(x,y)\phi(y)\,\mathrm{d}\overline{\mu}(y)=\int_{C_F}(\varphi(xy^{-1})-k^{\mathrm{spec}}_{\varphi,a,s}(x,y))\phi(y)\,\mathrm{d}\overline{\mu}(y) \tag{10.4.3.32}
$$

$$
=\int_{C_F}\varphi(xy^{-1})\phi(y)\,\mathrm{d}\overline{\mu}(y)-\int_{C_F}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)\phi(y)\,\mathrm{d}\overline{\mu}(y) \tag{10.4.3.33}
$$

$$
=\int_{C_F}\varphi(y)\phi(y^{-1}x)\,\mathrm{d}\overline{\mu}(y)-(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi)(x) \tag{10.4.3.34}
$$

$$
=A(\varphi)(\phi)(x)-(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi)(x) \tag{10.4.3.35}
$$

where we have used (10.4.3.28) from Remark 10.4.3.3 to identify $\int_{C_F}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)\phi(y)\,\mathrm{d}\overline{\mu}(y)$ with $(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi)(x)$, for $\overline{\mu}$-almost all $x\in C_F$.

Since $A(\varphi)-P^{\mathrm{spec}}_a\circ A(\varphi)=(\mathrm{Id}-P^{\mathrm{spec}}_a)\circ A(\varphi)$, and $\mathrm{Id}-P^{\mathrm{spec}}_a=P^{\mathrm{geom}}_a$, we deduce that (10.4.3.29) holds.

(2) : Since

$$
(P^{\mathrm{spec}}_a\circ A(\varphi))(\phi)(x)=\int_{C_F}(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)\,(1+|\log|y|_F|^2)^{s/2}\mathrm{d}\overline{\mu}(y)
$$

we deduce, by uniqueness of the Hilbert-Schmidt kernel associated to the nuclear, hence Hilbert-Schmidt, operator $P^{\mathrm{spec}}_a\circ A(\varphi)$, that $(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)$ is a representative kernel function for the Hilbert-Schmidt kernel of $P^{\mathrm{spec}}_a\circ A(\varphi)$ (i.e. any other such function agrees with $(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)$ almost everywhere over $C_F\times C_F$ with respect to the product measure $(1+|\log|\cdot|_F|^2)^{-s/2}\overline{\mu})^{\otimes 2}$, equivalently $\overline{\mu}\otimes\overline{\mu}$, since the two measures have the same null sets in $C_F\times C_F$).

A similar argument shows that $\rho(x)\,(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)$ is a representative function over $C_F\times C_F$ for the Hilbert-Schmidt kernel of $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$.

(3) : Since $(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)$ is the Hilbert-Schmidt kernel of the nuclear, hence Hilbert-Schmidt, operator $P^{\mathrm{spec}}_a\circ A(\varphi)$ on $W^{s,2}(C_F)$ by (2), then the function:

$$
\rho(x)\cdot((1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y)) \tag{10.4.3.36}
$$

is the Hilbert-Schmidt kernel of $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$.

Moreover, $\rho(x)\cdot(1+|\log|y|_F|^2)^{-s/2}\varphi(xy^{-1})$ is the Hilbert-Schmidt kernel of $M_{\rho}\circ A(\varphi)$ on $W^{s,2}(C_F)$, and so:

$$
\rho(x)\cdot(1+|\log|y|_F|^2)^{-s/2}\varphi(xy^{-1})-\rho(x)\cdot(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{spec}}_{\varphi,a,s}(x,y) \tag{10.4.3.37}
$$

which is $\rho(x)\cdot(1+|\log|y|_F|^2)^{-s/2}k^{\mathrm{geom}}_{\varphi,a,s}(x,y)$, is the Hilbert-Schmidt kernel of $P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)=M_{\rho}\circ A(\varphi)-P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$ on $W^{s,2}(C_F)$.

$\square$

10.4.3.2. *Spectral kernels: the general case of compact intervals $I=[-\alpha,\alpha]$.* Using the same estimates on singular values from the proof of Theorem 10.4.2.8, we have the following general version of Theorem 10.4.3.1, which we discuss in the case of the convolution-after-projection spectral restriction operators (see Definition 10.4.1.5):

## PDF page 472

**472** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

Theorem 10.4.3.5 (Spectral and Geometric kernels - II). Let $F$ be a number field.

*Let $a,s$ be real numbers, with $a>0$ and $s>1$. Let $I=[-\alpha,\alpha]$ be a compact interval, $\alpha\ge 0$ a real number. Let $\varphi\in\mathcal D(C_F)$ be a test function.*

*We choose an enumeration for the set of tuples $Z:=\{\chi,t,b,m\}$ as follows:*

(1) *We choose an enumeration for the set of continuous characters $\chi$ of the base-points of the connected components of $\Omega(C_F)$ chosen in the holomorphic parametrization from (10.2.1.4) of Notation 10.2.1.1, and denote it $\{\chi_k\}_{k\ge 0}$.*

(2) *For each integer $k\ge 0$, we choose an enumeration $\{t_{k,j},b_{k,j}\}_{j\ge 0}$, for the set of pairs of real numbers $(t,b)\in\mathbf R$ such that $\rho_{\chi_k,t,b}:=\chi_k|\cdot|^{a+b+it}_F$ is a zero of $L(s,\chi_k)$, of multiplicity denoted by $N(\rho_{\chi_k,t,b})$, and we choose the enumeration for the $(t_{k,j},b_{k,j})$ so as to have $|t_{k,j}|\le|t_{k,j+1}|$ for all integers $j\ge 0$.*

(3) *For each triple $(\chi_k,t_{k,j},b_{k,j})$, we enumerate the finitely many integers $m\ge 0$ satisfying $m\le N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})-1$, with $N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})$ defined in (10.2.2.5) and (10.2.2.6) by:*

$$
N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})=\min\left\{N(\rho_{\chi_k,t_{k,j},b_{k,j}}),\left[\frac{s-1}{2}+1\right]\right\},\;b_{k,j}=\pm\alpha,\;N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})=N(\rho_{\chi_k,t_{k,j},b_{k,j}}),\;b_{k,j}\in(-\alpha,\alpha) \tag{10.4.3.38}
$$

*according to their natural increasing ordering.*

(4) *For each such $\chi$, the induced enumeration of the subset $Z_{\chi}\subset Z$ of those tuples such that the first entry is $\chi$, is lexicographical.*

*and denote by $\{\psi_{\chi,t,b,m}\}_{\chi,t,b,m}\subset \mathscr{H}^s_{F,a,I}$ the dual Markushevich basis in $\mathscr{H}^s_{F,a,I}$ to the Spectral Markushevich basis for $(\mathscr{H}^s_{F,a,I})'_{\beta}$ obtained as the image of the functions:*

$$
\eta_{\chi,t,b,m}:=\chi|\cdot|^{b+it}_F(\log|\cdot|_F)^m \tag{10.4.3.39}
$$

*under the inverse of the isometry $T_{I,s}:W^s_I(C_F)'_{\beta}\to W^{-s}_I(C_F)$ from (9.2.2.42), provided by Proposition 9.2.2.11 for the strong dual $(\mathscr{H}^s_{F,a,I})'_{\beta}$, where $\mathscr{H}^s_{F,a,I}$ is the Hilbert space quotient of $W^s_I(C_F)$ by $W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(F^{\times},\mathcal S_0(\mathbf A_F))$ defined in (10.2.2.1).*

We denote by:

$$
I:=\{(k,j,m_{k,j})\in\mathbf N^3:k\ge 0,j\ge 0,0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j}})-1\} \tag{10.4.3.40}
$$

*ordered lexicographically from the lexicographic ordering on $\mathbf N^3$.*

Then:

(1) *The effect of the canonical linear isometry $S_a:\mathscr{H}^s_{F,a,I}\to P^{\mathrm{spec}}_aW^s_I(C_F)$ from (10.4.1.5), inverse to the quotient $P^{\mathrm{spec}}_aW^s_I(C_F)\to \mathscr{H}^s_{F,a,I}$, on the basis elements $\{\psi_{\chi,t,b,m}\}_{\chi,t,b,m}\subset \mathscr{H}^s_{F,a,I}$, is described as follows: for each $(\chi,t,b,m)\in Z$ according to the chosen enumeration, we make a choice of an element $\widetilde\psi_{\chi,t,b,m}\in W^s_I(C_F)$ whose image in $\mathscr{H}^s_{F,a,I}$ is $\psi_{\chi,t,b,m}$. Then:*

$$
S_a(\psi_{\chi,t,b,m})=P^{\mathrm{spec}}_a(\widetilde\psi_{\chi,t,b,m}). \tag{10.4.3.41}
$$

(2) *The sequences of finite rank kernels:*

$$
\sum_{i\in I}\langle A(\varphi)'\eta_{(\chi,t,b,m)_i},\cdot\rangle_{I,s}\otimes\psi_{(\chi,t,b,m)_i}=\sum_{0\le k\le N_1}\sum_{0\le j\le N_2}\sum_{0\le m_{k,j}\le N_s(\rho_{\chi_k,t_{k,j},b_{k,j}})-1}\langle A(\varphi)'\eta_{\chi_k,t_{k,j},b_{k,j},m_{k,j}},\cdot\rangle_{I,s}\otimes\psi_{\chi_k,t_{k,j},b_{k,j},m_{k,j}} \tag{10.4.3.42}
$$

in $(\mathscr{H}^s_{F,a,I})'_{\beta}\widehat\otimes_{\pi}(\mathscr{H}^s_{F,a,I})$, and:

$$
\sum_{i\in I}A(\varphi)'\eta_{(\chi,t,b,m)_i}\otimes S_a(\psi_{(\chi,t,b,m)_i})=\sum_{0\le k\le N_1}\sum_{0\le j\le N_2}\sum_{0\le m_{k,j}\le N_{I,s}(\rho_{\chi_k,t_{k,j},b_{k,j}})-1}A(\varphi)'\eta_{\chi_k,t_{k,j},b_{k,j},m_{k,j}}\otimes S_a(\psi_{\chi_k,t_{k,j},b_{k,j},m_{k,j}}) \tag{10.4.3.43}
$$

## PDF page 473

**10.4. TRACE FORMULA: SPECTRAL SIDE** · **473**

*in $W^{-s}_I(C_F)\widehat\otimes_{\pi}W^s_I(C_F)$, converge as $(N_1,N_2)\to(+\infty,+\infty)$ in $\mathbf N\times\mathbf N$, equivalently $i\to+\infty$ in $I$, with respect to the respective projective tensor product topologies.*

(3) Let:

$$
\xi_{\pi}:W^{-s}_I(C_F)\widehat\otimes_{\pi}W^s_I(C_F)\to\mathscr{L}_{\beta}(W^s_I(C_F)) \tag{10.4.3.44}
$$

*be the composition of $T^{-1}_{I,s}\widehat\otimes_{\pi}\mathrm{Id}$ and the continuous injective linear operator $\chi_{\pi}$ from Proposition C.3.6.4, whose effect on finite rank kernels is that of associating to $\sum_{1\le k\le N}\phi_k\otimes\psi_k$ the finite rank operator $\sum_{1\le k\le N}\langle\phi_k,\cdot\rangle_{I,s}\psi_k$. Upon denoting by $K^{\mathrm{spec}}_{\varphi,a,I,s}$ the limit in $W^{-s}_I(C_F)\widehat\otimes_{\pi}W^s_I(C_F)$ of the finite rank kernels from (10.4.3.42), then we have, within $\mathscr{L}_{\beta}(W^s_I(C_F))$:*

$$
\xi_{\pi}(K^{\mathrm{spec}}_{\varphi,a,I,s})=A(\varphi)\circ P^{\mathrm{spec}}_a. \tag{10.4.3.45}
$$

As a Corollary, we obtain:

Theorem 10.4.3.6. *Let $F$ be a number field, $a,s$ real numbers, $a>0$, $s>1$. Let $\Lambda,\varepsilon>0$ be real numbers, such that $0<1/\Lambda+\varepsilon<\Lambda-\varepsilon$. Let $\rho:C_F\to\mathbf C$ be a $(\Lambda,\varepsilon)$-cutoff.*

*Let $w_{I,s}$ is the weight function defined in (9.2.2.41) as:*

$$
w_{I,s}(g):=\max\{|g|^{2a}_F,|g|^{2b}_F\}\,(1+|\log|g|_F|^2)^{s/2},\ g\in C_F.
$$

Then:

(1) *For any $\phi\in W^s_{a,I}\mathrm H_{0,\mathrm{cont}}(F^{\times},\mathcal S_0(\mathbf A_F))$, we have, for $\overline{\mu}$-almost all $x\in C_F$:*

$$
A(\varphi)(\phi)(x)=(A(\varphi)\circ P^{\mathrm{geom}}_a)(\phi)(x)=\int_{C_F}k^{\mathrm{geom}}_{\varphi,a,I,s}(x,y)\phi(y)\,\mathrm{d}\overline{\mu}(y). \tag{10.4.3.46}
$$

(2) The functions:

$$
w_{I,s}(y)^{-1}k^{\mathrm{spec}}_{\varphi,a,I,s}(x,y),\quad \rho(x)\,w_{I,s}(y)^{-1}k^{\mathrm{spec}}_{\varphi,a,I,s}(x,y) \tag{10.4.3.47}
$$

*are representative functions for the Hilbert-Schmidt kernel in $L^2(C_F\times C_F,(w_{I,s}\overline{\mu})^{\otimes 2})$ of the operator $A(\varphi)\circ P^{\mathrm{spec}}_a$ on $W^s_I(C_F)$, respectively for the Hilbert-Schmidt kernel in $L^2(C_F\times C_F,(w_{I,s}\overline{\mu})^{\otimes 2})$ of the operator $M_{\rho}\circ A(\varphi)\circ P^{\mathrm{geom}}_a$ on $W^s_I(C_F)$.*

(3) The function:

$$
w_{I,s}(y)^{-1}\rho(x)\,k^{\mathrm{geom}}_{\varphi,a,I,s}(x,y) \tag{10.4.3.48}
$$

*is a representative function for the Hilbert-Schmidt kernel of the operator $M_{\rho}\circ A(\varphi)\circ P^{\mathrm{geom}}_a$ on $W^s_I(C_F)$.*

The following is the resulting general case of Definition 10.4.3.2, allowing arbitrary compact intervals $I=[-\alpha,\alpha]$, for $\alpha\ge 0$ a real number.

Definition 10.4.3.7 (Global Spectral and Geometric Kernels - the general case). Let $F$ be a number field, $a,s$ real numbers, $s\ge 3$. Let $I=[-\alpha,\alpha]\subset\mathbf R$ be a compact interval, $\alpha\ge 0$ a real number.

We define:

(1) The measurable function on $C_F\times C_F$:

$$
k^{\mathrm{spec}}_{\varphi,a,I,s}(x,y):=k(x,y)\,w_{I,s}(y)^{-1} \tag{10.4.3.49}
$$

where $w_{I,s}$ is the weight function defined in (9.2.2.41) as:

$$
w_{I,s}(g):=\max\{|g|^{2a}_F,|g|^{2b}_F\}\,(1+|\log|g|_F|^2)^{s/2},\ g\in C_F.
$$

We refer to $k^{\mathrm{spec}}_{\varphi,a,I,s}$ as the Global Spectral Kernel of the $\varphi$-regularized action of $C_F$ on $W^s_I(C_F)$.

(2) The measurable function on $C_F\times C_F$:

$$
k^{\mathrm{geom}}_{\varphi,a,I,s}(x,y):=\varphi(xy^{-1})-k^{\mathrm{spec}}_{\varphi,a,I,s}(x,y) \tag{10.4.3.50}
$$

## PDF page 474

**474** · **CHAPTER 10. TRACE FORMULA: SPECTRAL SIDE**

We refer to $k^{\mathrm{geom}}_{\varphi,a,I,s}$ as the Global Geometric Kernel of the $\varphi$-regularized action of $C_F$ on $W^s_I(C_F)$.
