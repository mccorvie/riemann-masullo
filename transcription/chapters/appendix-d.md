## PDF page 743

APPENDIX D

Schwartz-Bruhat functions

D.1. Schwartz-Bruhat space of a Hausdorff locally compact abelian group 745

D.1.1. Fourier Transform 746

D.1.2. Weil’s Formula for the Haar Integral 747

D.1.3. Schwartz space of elementary Lie groups 749

D.1.3.1. Smooth, rapidly decaying functions on elementary abelian Lie groups. 750

D.1.3.2. Fundamental families of continuous seminorms. 751

D.1.3.3. Nuclearity of the Schwartz-Bruhat space of an elementary abelian Lie group. 752

D.1.4. Structure theory of Hausdorff locally compact abelian groups 757

D.1.4.1. Exhaustion by compactly generated open subgroups, approximation by abelian Lie groups. 758

D.1.4.2. Basic properties of duals and orthogonals. 758

D.1.4.3. General structural results. 759

D.1.5. Schwartz-Bruhat space of a Hausdorff locally compact abelian group 760

D.1.5.1. Good subgroups and structural pairs. 760

D.1.5.2. The Schwartz-Bruhat space $\mathcal{S}(G)$. 761

D.1.5.3. Main Structure Theorems on Schwartz-Bruhat spaces. 763

D.1.6. Differential operators on Hausdorff locally compact abelian groups 765

D.1.6.1. Degree-1 differential operators and differential characterization of smoothness. 766

D.1.6.2. General differential operators. 767

D.1.6.3. Differential operators, symbols and the Fourier transform. 771

D.1.7. Distributional Poisson Summation 776

D.1.8. Support of tempered distributions on Hausdorff locally compact abelian groups 777

D.1.8.1. Kernel Theorems. 777

D.1.8.2. Supports. 779

D.1.9. Continuity of translation on Schwartz-Bruhat spaces 780

D.1.10. Examples: global and $S$-local idele classes 783

D.1.10.1. Complements on the locally convex topology on Schwartz-Bruhat spaces 784

D.1.10.2. Families of continuous seminorms on $\mathcal{S}(C_F)$. 789

D.1.10.3. Families of continuous seminorms on $\mathcal{S}(C_{F,S})$. 791

D.2. Schwartz-Bruhat functions on modulated groups 792

D.2.1. Preparations on modulated groups 792

D.2.1.1. Modulated groups: definition and canonical measure. 792

D.2.2. Complements on the $G^1$-isotypes of $\mathcal{S}(G)$ for modulated groups $G$ 794

D.2.2.1. A kernel Theorem for $\mathbf{R}_{>0}$-modulated groups. 797

D.3. Schwartz-Bruhat functions with $I$-exponential decay 797

D.3.1. Schwartz-Bergman spaces 797

D.3.2. Fourier-Mellin transform on $\mathcal{S}_I(\mathbf{R}_{>0})$ 801

D.3.2.1. Basic properties of $\mathcal{S}_I(\mathbf{R}_{>0})$. 801

D.3.2.2. Fourier-Mellin transform on $\mathcal{S}_I(\mathbf{R}_{>0})$. 802

743

## PDF page 744

744 CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS

D.3.2.3. Fundamental families of continuous seminorms on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$. 803

D.3.3. Schwartz-Bruhat functions with $I$-exponential decay on $\mathbf{R}_{>0}$-modulated groups 804

D.3.3.1. The main Structure Theorem on Schwartz-Bruhat functions with $I$-exponential decay. 806

D.3.3.2. Fourier-Melllin transform on $\mathcal{S}_I(G)$. 812

D.3.4. Uniform Riemann-Lebesgue Lemma on $\mathbf{R}_{>0}$-modulated groups 815

D.3.5. Poisson Summation Formula on $\mathbf{R}_{>0}$-modulated groups: isolated singularities 818

D.3.6. Approximation by smooth compactly supported functions 819

## PDF page 745

D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP · 745

**D.1. Schwartz-Bruhat space of a Hausdorff locally compact abelian group**

In this section we describe, for any Hausdorff locally compact abelian topological group $G$, the $\mathbf{C}$-vector space of Schwartz functions $\mathcal{S}(G)$ and its locally convex topology. Important examples of such $G$ for our purposes are not only the adele ring $\mathbf{A}_F$ and its factor fields $F_v$ for the places $v$ of $F$, but also the multiplicative analogues $\mathrm{GL}_1(\mathbf{A}_F)$ and $F_v^\times$ as well as the idele class group $C_F$ and its $S$-local analogue $C_{F,S}$. (Beware that for non-archimedean $v$, $\mathcal{S}(F_v^\times)$ is much larger than the more widely-seen space $C_c^\infty(F_v^\times)$ of locally constant functions with compact support away from $0$; it includes functions $f(x)$ with sufficiently rapid decay as $|x| \to 0, \infty$.)

We will then recall properties of the Fourier transform on $\mathcal{S}(G)$ and discuss some examples of interest, as well as define the concept of vector-valued tempered distribution on $G$. The latter is needed to prove “kernel theorems” that express function spaces on a product as suitably completed tensor products of function spaces on the factors; such results are a crucial tool to built operators for a product group from operators associated to the factor groups.

To succinctly state the main result of this Appendix, let us first recall some terminology for Hausdorff locally convex topological vector spaces that is reviewed in much more detail in Appendix C.1. We say such a space $E$ is bornological if any seminorm on $E$ that is bounded on bounded subsets is continuous (this is equivalent to another definition given without the language of seminorms in [Scha, Ch. II, p. 61], via the relation to seminorms to circled convex subsets in [Scha, Ch. II, 1.5, 1.6]). We say $E$ is barrelled if every barrel (i.e., closed convex circle absorbing subset) is a neighborhood of $0$; see [Scha, Ch. II, §7] for more on barrelledness. For instance, Fréchet spaces are barrelled [Scha, Ch. II, Cor. to 7.1].

Finally, we say $E$ is Montel if it is reflexive (i.e., the natural map to the strong double dual is a topological isomorphism) and has the Heine-Borel property: closed bounded subsets are compact. It is equivalent (by [Scha, Ch. IV, 3.1, 5.6]) for $E$ to be barrelled and have the Heine-Borel property. Every barrelled quasi-complete nuclear space is Montel [Tre, Cor. 3 to Prop. 50.2], so for example every nuclear Fréchet space is Montel. The latter applies to $\mathcal{S}(\mathbf{R}^N)$, but not to inductive limits such as $\mathcal{S}(\mathbf{Q}_p)$ or $\mathcal{S}(\mathbf{A}_F)$ that are complete [Scha, Ch. II, 6.6] but non-metrizable (they don’t have a countable base of $0$-neighborhoods).

The main result we aim to prove in this Appendix is that if $G$ is second countable (i.e., has a countable base for the topology) then $\mathcal{S}(G)$ is a complete bornological Montel space whose strong dual $\mathcal{S}(G)'_\beta$ is nuclear (the strong dual is then also complete and Montel, as holds for the strong dual of any bornological Montel space [Scha, Ch. IV, 5.9, 6.1]). Nuclearity is always inherited by the strong dual for nuclear Fréchet spaces [Tre, Prop. 50.6], but we need cases such as $G = \mathbf{A}_F$ and $G = C_F$ for which $\mathcal{S}(G)$ is not Fréchet, so the nuclearity of the strong dual of $\mathcal{S}(G)$ is a genuinely additional property for $E = \mathcal{S}(G)$ in general.

The same assertion for $C_c^\infty(G)$ in place of $\mathcal{S}(G)$ is proved as [Bru, §8, Cor. 2 to Prop. 10], and [Bru, §9, Prop. 11] states that this holds for $\mathcal{S}(G)$ by similar arguments, but no details are provided. (In [Bru] the topological hypothesis on $G$ is “separable”, which is defined therein to mean “metrizable and covered by countably many compact subsets”; for Hausdorff locally compact abelian groups this is equivalent to being second countable by Remark A.5.2.9, so it matches the topological hypothesis we shall use but we won’t need that.). Since $\mathcal{S}(G)$ is much larger than $C_c^\infty(G)$, and studying it entails much greater attention to decay estimates than for $C_c^\infty(G)$, a complete treatment of the matter is provided herein. The arguments presented here follow closely those in the early sections of [Bru]. We briefly indicate what happens beyond the second-countable case in Remark D.1.5.8, and primarily focus on second countable $G$ since it is the sole case of relevance for us.

We will be relying on basic duality theory for Hausdorff locally compact abelian groups, for which the reader is referred to [DE, Ch. 3]. We will be referring to [Ru, Ch. 1, 2] and [DE, Ch. 3, 4] for foundational material on the structure of Hausdorff locally compact abelian groups, Pontryagin duality and Fourier Theory, and we will give some references to [Bru] and [Wa, §2] connected to the definition of the Schwartz space $\mathcal{S}(G)$.

## PDF page 746

746 · CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS

Toward the end of this section we define distributions on $G$ valued in a Hausdorff locally convex topological $\mathbf{C}$-vector space $E$ due to its role in the proof of “kernel theorems” as noted above; this includes studying required properties of differential operators and the Fourier transform.

**D.1.1. Fourier Transform.** We first briefly recall the definition and basic properties of the Fourier transform on a Hausdorff locally compact abelian group, to be followed by Weil’s Formula for the Haar Integral (see Theorem D.1.2.1) and by the Poisson Summation Formula (see Theorem D.1.2.7). They are collected here in the generality of Hausdorff locally compact abelian groups, for later reference.

THEOREM D.1.1.1. *Let $G$ be a Hausdorff locally compact abelian group, and $\widehat{G}$ the set of continuous characters $\chi : G \to U(1)$ endowed with the compact-open topology. Then*

(1) *$\widehat{G}$ is a Hausdorff locally compact abelian group, whose formation is contravariantly functorial with respect to continuous homomorphisms.*

(2) *The duality pairing:*

$$
\langle g, \chi \rangle_{G,\widehat{G}} : G \times \widehat{G} \to U(1) \tag{D.1.1.1}
$$

*is separating and it induces a canonical isomorphism of topological groups*

$$
\iota_G : G \to \widehat{\widehat{G}} \tag{D.1.1.2}
$$

*via the assignment:*

$$
\iota_G(g)(\chi) := \chi(g) \tag{D.1.1.3}
$$

(3) *$G$ is compact if and only if $\widehat{G}$ is discrete.*

PROOF. The first assertion in (1) is [Ru, Thm. 1.2.6(d)] (topological groups in [Ru] are Hausdorff by definition), and the rest of (1) is clear. Assertion (2) is [Ru, Thm. 1.7.2], and (3) is [Ru, 1.7.3(a)]. $\square$

We recall that for any fixed arbitrary choice of Haar measure $\mu_G$ on $G$, there exists a Fourier transform, defined on $f \in L^1(G,\mu_G)$ on $G$ by the assignment

$$
\mathcal{F}_G(f)(\chi) := \widehat{f}(\chi) := \int_G f(g) \overline{\chi(g)} \, \mathrm{d}\mu_G(g), \tag{D.1.1.4}
$$

noting that $f \overline{\chi}$ is integrable since $\chi$ is bounded over $G$ (and continuous).

We further recall that for $f_1, f_2 \in L^1(G,\mu_G)$ there exists a convolution product $f_1 \ast f_2$ defined by

$$
(f_1 \ast f_2)(x) := \int_G f_1(g) f_2(g^{-1}x) \, \mathrm{d}\mu_G(g), \tag{D.1.1.5}
$$

with $f_1 \ast f_2$ a $\mu_G$-measurable function defined $\mu_G$-almost everywhere on $G$ and $\mu_G$-integrable on $G$ with $L^1$-norm satisfying

$$
\|f_1 \ast f_2\|_1 \le \|f_1\|_1 \cdot \|f_2\|_1 \tag{D.1.1.6}
$$

by [Ru, Thm. 1.1.6], and convolution is a commutative algebra structure on $L^1(G,\mu_G)$.

We collect here basic properties of the Fourier transform for later reference, denoting by $\|\cdot\|_u : C_0(G) \to \mathbf{R}_{\ge 0}$ the sup-norm on the space of continuous functions on $G$ vanishing at infinity.

LEMMA D.1.1.2. *Let $G$ be a Hausdorff locally compact abelian group, $f, f_1, f_2 : G \to \mathbf{C}$ three $\mu_G$-measurable functions.*

(1) *If $f \in L^1(G,\mu_G)$ then $\widehat{f} \in C_0(\widehat{G})$.*

(2) *The Fourier transform $\mathcal{F}_G : L^1(G,\mu_G) \to C_0(\widehat{G})$ is an injective linear operator satisfying*

$$
\|\widehat{f}\|_u \le \|f\|_1 \tag{D.1.1.7}
$$

## PDF page 747

D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP · 747

*(so in particular it is a continuous map).*

(3) *If $f_1, f_2 \in L^2(G,\mu_G)$ then $(f_1 \ast f_2)(x)$ is finite for all $x \in G$ and belongs to $C_0(G)$, satisfying*

$$
\|f_1 \ast f_2\|_u \le \|f_1\|_2 \cdot \|f_2\|_2. \tag{D.1.1.8}
$$

(4) *There exists a unique Haar measure $\mu_{\widehat{G}}$ on $\widehat{G}$, called the Plancherel measure, such that for any $f \in L^1(G,\mu_G) \cap L^2(G,\mu_G)$ we have*

$$
\|f\|_2 = \|\widehat{f}\|_2, \tag{D.1.1.9}
$$

*and the Fourier transform extends uniquely to a unitary isomorphism of Hilbert spaces:*

$$
\mathcal{F}_G : L^2(G,\mu_G) \to L^2(\widehat{G},\mu_{\widehat{G}}). \tag{D.1.1.10}
$$

(5) *If $f \in L^1(G,\mu_G)$ is such that $\widehat{f} \in L^1(\widehat{G},\mu_{\widehat{G}})$ then $f$ is continuous on $G$ and the inversion formula holds:*

$$
f(x^{-1}) = \mathcal{F}_{\widehat{G}}(\mathcal{F}_G(f))(x) \tag{D.1.1.11}
$$

*as functions of $x \in G$.*

(6) *For $f_1, f_2 \in L^1(G,\mu_G)$ we have*

$$
\mathcal{F}_G(f_1 \ast f_2) = \mathcal{F}_G(f_1) \cdot \mathcal{F}_G(f_2) \tag{D.1.1.12}
$$

*as functions in $C_0(\widehat{G})$.*

PROOF. (1) and (2) are [Ru, Thm. 1.2.4(a, d)], as well as [DE, Cor. 3.3.4] for the injectivity of $\mathcal{F}_G$.

(3) : This is [Ru, 1.1.6,(d)] and Hölder’s inequality (which establishes the norm-bound in (D.1.1.8)).

(4) : This is [DE, Thm. 3.4.8 and p. 77].

(5) : This is [DE, Thm. 3.5.8].

(6) : This is [Ru, Thm. 1.2.4(b)]. $\square$

**D.1.2. Weil’s Formula for the Haar Integral.** We recall here a fundamental result concerning integrable functions on a Hausdorff locally compact abelian group $G$ with respect to a choice of Haar measure $\mu$: the uniquely determined Haar measure $\nu$ on the quotient $G/H$ by a closed subgroup $H$ that has been equipped with a choice of Haar measure $\mu_H$.

THEOREM D.1.2.1 (Weil’s Quotient Integral Formula). *Let $G$ be a locally compact Hausdorff abelian group, $H \subset G$ a closed subgroup. There exists a Haar measure $\nu$ on $G/H$ uniquely determined by choices of a Haar measure $\mu_G$ on $G$ and $\mu_H$ on $H$ subject to the requirement that for every $f \in C_c(G)$, we have*

$$
\int_G f(g) \, \mathrm{d}\mu_G(g) = \int_{G/H} \int_H f(xh) \, \mathrm{d}\mu_H(h) \, \mathrm{d}\nu(x). \tag{D.1.2.1}
$$

*Moreover, for every $\mu_G$-measureable $f : G \to \mathbf{C}$ the assignment $f^H : x \mapsto \int_H f(xh) \, \mathrm{d}\mu_H(h)$ defines $\mu_G$-almost everywhere on $G$ a function that is $\nu$-measurable and if $f \in L^1(G)$ then $f^H$ is $\nu$-integrable on $G/H$ and (D.1.2.1) holds for $f$.*

All but the final assertion follow from [Lang-d, Ch. XII, Thm. 4.1, Cor. 2.4]. The final $L^1$ assertion is part of [DE, Thm. 1.5.3].

REMARK D.1.2.2. Theorem D.1.2.1 has an analogue for non-commutative $G$ but we only ever need it for $G$ commutative, which has the advantage of rendering the group unimodular.

LEMMA D.1.2.3. *Let $G$ be a locally compact Hausdorff abelian group, $H \subset G$ a closed subgroup, and $\mu_G$ and $\mu_H$ Haar measures on $G$ and $H$ respectively. Let $\nu$ be the unique invariant Haar measure on the quotient $G/H$ provided by Theorem D.1.2.1. Assume that $G$ is $\sigma$-finite. Let $f : G \to \mathbf{C}$ be a measurable function. If*

$$
\int_{G/H} \int_H |f(xh)| \, \mathrm{d}\mu_H(h) \, \mathrm{d}\nu(x) \tag{D.1.2.2}
$$

## PDF page 748

748 · CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS

*converges then $f$ is $\mu_G$-integrable over $G$ and (D.1.2.1) holds.*

PROOF. See [DE, Cor. 1.5.4]. $\square$

Here is a basic result on “measureable fundamental domains”:

PROPOSITION D.1.2.4. *Let $G$ be a Hausdorff locally compact abelian group, $H \subset G$ a closed subgroup. Let $\Delta \subset G$ a Borel measurable subset. Assume:*

(1) *$H$ is discrete and define $\mu_H$ to be the counting measure on $H$; let $\bar{\mu}$ being the unique Haar measure on $G/H$ induced by the pair $\mu_G, \mu_H$.*

(2) *The continuous quotient homomorphism $\pi_H : G \to G/H$ induces a bijection $\Delta \to G/H$.*

(3) *$G$ is second-countable.*

*For any $f \in L^1(G,\mu_G)$, the function $S(f) : H \to \mathbf{C}$ defined by*

$$
S(f)(h) := \int_{\Delta h} f(g) \, \mathrm{d}\mu_G(g) \tag{D.1.2.3}
$$

*is $\mu_H$-integrable and*

$$
\int_G f(g) \, \mathrm{d}\mu_G(g) = \sum_{h \in H} S(f)(h) \tag{D.1.2.4}
$$

*with the right side absolutely convergent.*

*If $f : G/H \to \mathbf{C}$ is a function, then $f$ is $\bar{\mu}$-measurable, respectively $\bar{\mu}$-integrable if and only if $1_\Delta \cdot (f \circ \pi_H)$ is $\mu_G$-measurable, respectively $\mu_G$-integrable. In the latter case,*

$$
\int_{G/H} f(\bar{g}) \, \mathrm{d}\bar{\mu}(\bar{g}) = \int_\Delta (f \circ \pi_H)(g) \, \mathrm{d}\mu_G(g). \tag{D.1.2.5}
$$

PROOF. The absolute summability of $S(f)$ in (D.1.2.3) follows from [Bou-II, Ch. VII, §2.10, Prop. 15] applied to $X = G$, $\mu = \mu_G$, $F = \Delta$, and to real and imaginary parts of $f$, using that multiplication by $h$ is continuous and a homeomorphism (so $\Delta h$ is Borel measurable and the function $n : G \to \mathbf{Z}_{\ge 0}$ is identically $1$).

The Borel-measurability, respectively $\bar{\mu}$-integrability criterion, and the identity in (D.1.2.5), is a consequence of [Bou-II, §2.10, Thm. 4(c)], where $\varphi_F = 1_\Delta$ in the notation of loc. cit (applied to the real and imaginary parts of $f$). $\square$

The following application of (D.1.2.5) records that integration on a measurable fundamental domain does not depend on the choice of fundamental domain.

COROLLARY D.1.2.5. *Let $G$ be a Hausdorff locally compact abelian group, $H \subset G$ a closed subgroup. Let $\Delta, \Delta' \subset G$ be two Borel-measurable subsets. Assume:*

(1) *$H$ is discrete and define $\mu_H$ to be the counting measure on $H$.*

(2) *The quotient homomorphism $\pi_H : G \to G/H$ induces bijections $\Delta \to G/H$ and $\Delta' \to G/H$.*

(3) *$G$ is second-countable.*

*Let $f : G \to \mathbf{C}$ be a $\mu_G$-measurable function invariant under translation by $H$ (so it is $\bar{f} \circ \pi_H$ for a $\mu_{G/H}$-measureable $\bar{f} : G/H \to \mathbf{C}$). If $1_\Delta f$ is $\mu_G$-integrable then so is $1_{\Delta'} f$ and*

$$
\int_\Delta f(g) \, \mathrm{d}\mu_G(g) = \int_{\Delta'} f(g) \, \mathrm{d}\mu_G(g). \tag{D.1.2.6}
$$

As an application of Weil’s Formula for the Haar integral (Theorem D.1.2.1), we next discuss a general form of the Poisson Summation Formula for ease of reference.

SITUATION D.1.2.6. We choose a Haar measure $\mu_G$ on $G$, a Haar measure $\mu_H$ on $H$, and we let $\mu_{G/H}$ be the unique Haar measure on $G/H$ determined by $\mu_G$ and $\mu_H$ as per Theorem D.1.2.1. We denote by $\mu_{\widehat{G}}$,

## PDF page 749

D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP · 749

$\mu_{\widehat{G/H}}$ the respective Plancherel measures, and choose on $H^\perp$ the unique Haar measure that pulls back to $\mu_{\widehat{G/H}}$ under the isomorphism of Hausdorff locally compact abelian groups $H^\perp \to \widehat{G/H}$ from Lemma D.1.4.6. We denote by $\mu_{H^\perp}$ such choice of Haar measure on $H^\perp$.

By [DE, Thm. 3.6.3] we have:

THEOREM D.1.2.7 (Poisson Summation Formula). *Let $G$ be a Hausdorff locally compact abelian group, $H \subset G$ a closed subgroup, as in Situation D.1.2.6.*

*Let $f \in L^1(G,\mu_G)$, so the $H$-invariant function*

$$
f^H(x) := \int_H f(hx) \, \mathrm{d}\mu_H(h) \tag{D.1.2.7}
$$

*defined for $\mu_{G/H}$-almost all $x \in G/H$ is $\mu_{G/H}$-measurable and $\mu_{G/H}$-integrable.*

(1) *Under the isomorphism $H^\perp \to \widehat{G/H}$, $\widehat{f^H}$ pulls back to $\widehat{f}|_{H^\perp} \in C(H^\perp)$.*

(2) *If $\widehat{f}|_{H^\perp}$ is $\mu_{H^\perp}$-integrable then the Poisson Summation Formula*

$$
\int_H f(h^{-1}x) \, \mathrm{d}\mu_H(h) = \int_{H^\perp} \widehat{f}(\chi) \chi(x) \, \mathrm{d}\mu_{H^\perp}(\chi) \tag{D.1.2.8}
$$

*holds for $\mu_G$-almost all $x \in G$.*

(3) *Assume:*

(i) *$f^H$ is defined for every $x \in G$, and it is continuous.*

(ii) *$\widehat{f}|_{H^\perp} \in L^1(H^\perp)$ (so the right side of (D.1.2.8) converges for all $x \in G$).*

*Then (D.1.2.8) holds for all $x \in G$.*

REMARK D.1.2.8. We note that for (D.1.2.8) to hold for every $x \in G$, it is necessary for $f^H$ to be continuous since the right side of (D.1.2.8) is continuous in $x$ when $\widehat{f}|_{H^\perp} \in L^1(H^\perp)$.

**D.1.3. Schwartz space of elementary Lie groups.** We fix integers $m, n, r \ge 0$, and a finite abelian group $F$, with $\mathbf{Z}^r \times F$ endowed with the discrete topology. We denote by $\mathbf{T} := \mathbf{R}/\mathbf{Z}$ the circle group, and define

$$
G := \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F. \tag{D.1.3.1}
$$

We parametrize $G$ with coordinates $g = (x, z, a, b)$, where $x \in \mathbf{R}^m$, $z \in \mathbf{T}^n$, $a \in \mathbf{Z}^r$ and $b \in F$. Topological groups isomorphic to such $G$ for a (unique) choice of integers $m, n, r \ge 0$ and finite abelian group $F$ are called elementary abelian Lie groups.

Throughout this section we will recall in what sense elementary abelian Lie groups are the building blocks of general Hausdorff locally compact abelian groups, and how to use them to define the Schwartz space $\mathcal{S}(G)$ as a locally convex topological vector space.

We define

$$
\phi : \mathbf{R}^m \times \mathbf{R}^n \times \mathbf{Z}^r \times F \to \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F = G \tag{D.1.3.2}
$$

by $\phi(x, t, a, b) := (x, (\exp(2\pi i t_j))_{1 \le j \le n}, a, b)$ for $t = (t_j) \in \mathbf{R}^n$, so $C^\infty(\mathbf{R}^m \times \mathbf{T}^n)$ is identified with the space of $\{0\} \times \mathbf{Z}^n$-invariant functions in $C^\infty(\mathbf{R}^m \times \mathbf{R}^n)$: let

$$
\iota_{m,n} : C^\infty(\mathbf{R}^m \times \mathbf{T}^n) \to C^\infty(\mathbf{R}^m \times \mathbf{R}^n)
$$

be the inclusion.

For every $\alpha \in \mathbf{N}^m$ and $\beta \in \mathbf{N}^n$, define

$$
D_x^\alpha D_z^\beta := \frac{\partial^{|\alpha|}}{\partial x_1^{\alpha_1} \cdots \partial x_m^{\alpha_m}} \circ \frac{\partial^{|\beta|}}{\partial t_1^{\beta_1} \cdots \partial t_n^{\beta_n}} \circ \iota_{m,n} : C^\infty(\mathbf{R}^m \times \mathbf{T}^n) \to C^\infty(\mathbf{R}^m \times \mathbf{R}^n) \tag{D.1.3.3}
$$

## PDF page 750

750 · CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS

with $|\alpha| := \sum_{i=1}^m \alpha_i$, $|\beta| := \sum_{i=1}^n \beta_i$. We have

$$
D_x^\alpha D_z^\beta(C^\infty(\mathbf{R}^m \times \mathbf{T}^n)) \subset \iota_{m,n}(C^\infty(\mathbf{R}^m \times \mathbf{T}^n)) \tag{D.1.3.4}
$$

due to invariance of the $\mathbf{C}$-linear operator $\partial^{|\beta|}/(\partial t_1^{\beta_1} \cdots \partial t_n^{\beta_n})$ under additive $\mathbf{Z}^n$-translation on the $\mathbf{R}^n$-factor, so $D_x^\alpha D_z^\beta$ induces a unique $\mathbf{C}$-linear endomorphism of $C^\infty(\mathbf{R}^m \times \mathbf{T}^n)$ that we denote by $\partial_x^\alpha \partial_z^\beta$.

For any $x \in \mathbf{R}^m$ and $\alpha \in \mathbf{N}^m$ we define

$$
x^\alpha := \prod_{i=1}^m x_i^{\alpha_i}. \tag{D.1.3.5}
$$

D.1.3.1. *Smooth, rapidly decaying functions on elementary abelian Lie groups.* Let’s assume not only that $G$ is an elementary abelian Lie group (i.e., isomorphic to one of the form $\mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F$) but rather that $G$ is such a product abelian Lie group. In effect, we fix a choice of “coordinates” on $G^0$ and on its discrete component group as well as a homomorphic lifting of the discrete component into $G$. This assumption will be in force until the end of §D.1.3

DEFINITION D.1.3.1. For an elementary abelian Lie group $G$, we say $f \in C^\infty(G)$ is of rapid decay (at infinity) over $G$ if and only if:

(1) for every $\alpha, \beta \in \mathbf{N}^m$ and $\gamma \in \mathbf{N}^n$ and $\delta \in \mathbf{N}^r$, the function

$$
\|\cdot\|_{\alpha,\beta,\gamma,\delta} : C^\infty(G) \to [0, +\infty] \tag{D.1.3.6}
$$

defined by

$$
\|\phi\|_{\alpha,\beta,\gamma,\delta} := \sup_{g \in G} |(a^\delta x^\alpha \partial_x^\beta \partial_z^\gamma \phi)(x, z, a, b)| \tag{D.1.3.7}
$$

is finite on $f$.

We denote by $\mathcal{S}(G)$ the $\mathbf{C}$-vector space of all smooth functions on $G$ that decay rapidly towards infinity. We topologize $\mathcal{S}(G)$ with the locally convex topology generated by the countable family $\{\|\cdot\|_{\alpha,\beta,\gamma,\delta}\}$ of seminorms. We call $\mathcal{S}(G)$ the Schwartz-Bruhat space of $G$.

REMARK D.1.3.2. The locally convex topological vector space $\mathcal{S}(G)$ is Hausdorff, by setting $\alpha, \beta, \gamma, \delta = 0$.

Beware that the specific seminorms on $C^\infty(G)$ defined above depend very much on the choice of coordinates on $G$. But the topology is independent of such a choice thanks to:

LEMMA D.1.3.3. *Let $G = \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F$ for a finite abelian group $F$ and integers $m, n, r \ge 0$. For every continuous automorphisms $\phi$ of $G$ and $f \in \mathcal{S}(G)$, the pullback $f \circ \phi : G \to \mathbf{C}$ belongs to $\mathcal{S}(G)$ and $f \mapsto f \circ \phi$ is a topological automorphism of $\mathcal{S}(G)$.*

PROOF. We will describe a general $\phi$ as a composition of finitely many types of automorphisms that can be analyzed directly. Since the unique maximal compact subgroup of $G$ is $\mathbf{T}^n \times F$ and its identity component is $\mathbf{T}^n$, Since all automorphisms of $\mathbf{R}^m$ and of $\mathbf{Z}^r$ are linear and of $\mathbf{T}^n$ arise from an element of $\mathrm{GL}_n(\mathbf{Z})$, it is clear that an automorphism arising from ones of the factors $\mathbf{R}^m$, $\mathbf{T}^n$, $\mathbf{Z}^r$, and $F$ has the desired properties. Thus, for a general $\phi$ we readily reduce to the case when $\phi$ is the identity on the factor group $\mathbf{T}^n$ and its restriction to each of the four factor groups yields the identity when projected back onto that factor.

By connectedness considerations, the effect of such a $\phi$ on $\mathbf{R}^m$ is given by $x \mapsto (x, f(x), 0, 0)$ for a continuous homomorphism $f : \mathbf{R}^m \to \mathbf{T}^n$. Automorphisms of the form $(x, z, a, b) \mapsto (x, f(x)z, a, b)$ are readily seen to preserve the Schwartz decay property because $f(x) = (f_1(x), \dots, f_n(x))$ for $f_j : \mathbf{R}^m \to \mathbf{T}$ given by $x \mapsto e^{2\pi i \langle x, c_j \rangle}$ for some $c_1, \dots, c_n \in \mathbf{R}^m$. Thus, we can further reduce to the case that $\phi$ is the identity on the factor group $\mathbf{R}^m$. $\phi(x, z, a, b) = (x + L_1(a), z L_2(a) L_3(b), a, b + L_4(a))$ for homomorphisms

$$
L_1 : \mathbf{Z}^r \to \mathbf{R}^m,\ L_2 : \mathbf{Z}^r \to \mathbf{T}^n,\ L_4 : \mathbf{Z}^r \to F,\ L_3 : F \to \mathbf{T}^n.
$$

## PDF page 751

D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP · 751

Hence, we can focus on the cases in which all but one of these homomorphisms is trivial. The family of seminorms (D.1.3.10) defining the Schwartz topology allows us to handle the $L_1$-cases and the $L_2$-cases (since we can explicitly describe the possibilities for such $L_1$ and $L_2$ via “linear” formulas). The $L_4$-cases are easily handled since in such cases $\phi$ commutes with every $\partial_x^\alpha$ and $\partial_z^\beta$. The $L_3$-cases are handled by again using the family of seminorms (D.1.3.10). $\square$

D.1.3.2. *Fundamental families of continuous seminorms.* We now discuss different families of seminorms on $\mathcal{S}(G)$ generating the same (Hausdorff) locally convex topology.

LEMMA D.1.3.4. *The following families of seminorms $\mathcal{S}(G) \to [0, +\infty)$ all define the topology on $\mathcal{S}(G)$:*

$$
\mathcal{P}_1 : \|f\|_{\mathcal{P}_1,(j,j',\alpha,\beta)} := \sup_{g \in G} \{(1 + |x|^j)(1 + |a|^{j'}) |\partial_x^\alpha \partial_z^\beta f(x, z, a, b)|\},\ j, j' \in \mathbf{N}, \alpha \in \mathbf{N}^m, \beta \in \mathbf{N}^n \tag{D.1.3.8}
$$

*(where $|x|, |a|$ denote Euclidean norms),*

$$
\mathcal{P}_2 : \|f\|_{\mathcal{P}_2,(\alpha,\beta,P)} := \sup_{g \in G} \{|P(x, a)| |\partial_x^\alpha \partial_z^\beta f(x, z, a, b)|\},\ \alpha \in \mathbf{N}^m, \beta \in \mathbf{N}^n, P \in \mathbf{C}[X_1, \dots, X_m, Y_1, \dots, Y_r], \tag{D.1.3.9}
$$

$$
\mathcal{P}_3 : \|f\|_{\mathcal{P}_3,(P,Q)} := \sup_{g \in G} \{|P(x, a) Q(\partial_x, \partial_z) f(x, z, a, b)|\} \tag{D.1.3.10}
$$

*for varying $P \in \mathbf{C}[X_1, \dots, X_m, Y_1, \dots, Y_r]$, $Q \in \mathbf{C}[X_1, \dots, X_m, Z_1, \dots, Z_n]$.*

PROOF. We show each collection of seminorms in turn defines the topology on $\mathcal{S}(G)$. First we consider $\mathcal{P}_1$. For every $q \in \mathcal{P}_1$, we have $q = \|\cdot\|_{\mathcal{P}_1,(j,j',\alpha,\beta)}$ for some integers $j, j' \ge 0$ and $\alpha \in \mathbf{N}^m$, $\beta \in \mathbf{N}^n$. For every $f \in \mathcal{S}(G)$, in terms of the seminorms in (D.1.3.7) we have:

$$
q(f) \le \|f\|_{(0,\alpha,\beta,0)} + C^{j'}_{r} \sum_{i'=1}^{m} \|f\|_{(0,\alpha,\beta,\gamma_{i'}(j'))} + C^{j}_{m} \sum_{i=1}^{m} \|f\|_{(\alpha_i(j),\alpha,\beta,0)} + C^{j'}_{r} C^{j}_{m} \sum_{1 \le i,i' \le m} \|f\|_{(\alpha_i(j),\alpha,\beta,\gamma_{i'}(j'))} \tag{D.1.3.11}
$$

where $C_m > 0$ is a constant for which $|x| \le C_m \max_i |x_i|$ for all $x \in \mathbf{R}^m$ and $C_r$ is likewise for $\mathbf{R}^r$, and $\alpha_i(j) = j e_i \in \mathbf{N}^m$, $\gamma_{i'}(j') = j' e'_{i'} \in \mathbf{N}^r$ (so $|x|^j \le C^{j}_{m} \sum_i |x^{\alpha_i(j)}|$, $|a|^{j'} \le C^{j'}_{r} \sum_{i'} |a^{\gamma_{i'}(j')}|$.

On the other hand, for every $\eta, \theta \in \mathbf{N}^m$ and $\gamma \in \mathbf{N}^r$, there exist real numbers $C_{\eta,m}, A_{\gamma,r} > 0$ such that $|x^\eta| \le C_{\eta,m} \cdot (1 + |x|^{|\eta|})$ and $|a^\gamma| \le A_{\gamma,r} \cdot (1 + |a|^{|\gamma|})$, showing that we also have

$$
\|f\|_{\eta,\theta,\beta,\gamma} \le C \cdot \|f\|_{\mathcal{P}_1,(|\eta|,|\gamma|,\theta,\beta)} \tag{D.1.3.12}
$$

for a real number $C > 0$ depending only on $\eta, \gamma$ (and $m$ and $r$). This settles $\mathcal{P}_1$.

Turning to $\mathcal{P}_2$, every $P \in \mathbf{C}[X_1, \dots, X_m, Y_1, \dots, Y_r]$ is of the form $P = \sum_{\alpha \in \mathbf{N}^m, \delta \in \mathbf{N}^r} c_{\alpha,\delta} X^\beta Y^\delta$ where all but finitely many of the $c_{\beta,\delta} \in \mathbf{C}$ are nonzero, and $X^\beta := \prod_{i=1}^m X_i^{\beta_i}$ and $Y^\delta := \prod_{i=1}^r Y_i^{\delta_i}$, so for every $f \in \mathcal{S}(G)$ we have

$$
\|f\|_{\mathcal{P}_2,(\beta,\gamma,P)} \le \sum_{\alpha \in \mathbf{N}^m, \delta \in \mathbf{N}^r} |c_{\alpha,\delta}| \|f\|_{\alpha,\beta,\gamma,\delta}. \tag{D.1.3.13}
$$

Since also $\|\cdot\|_{\alpha,\beta,\gamma,\delta} \in \mathcal{P}_2$ for every $\alpha, \beta \in \mathbf{N}^m$, $\gamma \in \mathbf{N}^n$, $\delta \in \mathbf{N}^r$, $\mathcal{P}_2$ also defines the topology on $\mathcal{S}(G)$.

Finally, since every $Q \in \mathbf{C}[X_1, \dots, X_m]$ is of the form $Q = \sum_{\alpha \in \mathbf{N}^m} c_\alpha X^\alpha$ with all but finitely many of the $c_\alpha \in \mathbf{C}$ being nonzero and $X^\alpha := \prod_{i=1}^m X_i^{\alpha_i}$, every element of $\mathcal{P}_3$ is bounded above by a finite sum of positive constants times elements of $\mathcal{P}_2$. Since likewise every seminorm in $\mathcal{P}_2$ belongs to $\mathcal{P}_3$, the locally convex topologies defined by the respective families $\mathcal{P}_2$ and $\mathcal{P}_3$ of seminorms are the same. $\square$

LEMMA D.1.3.5. *We have:*

## PDF page 752

752 · CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS

(1) *The locally convex topology on $\mathcal{S}(G)$ induced by the family of seminorms from (D.1.3.6) is equivalent to the locally convex topology on $\mathcal{S}(G)$ induced by the family of norms on $\mathcal{S}(G)$ defined by*

$$
\|f\|_N := \sum_{\alpha,\beta,\gamma,\delta : |\alpha|,|\beta|,|\gamma|,|\delta| \le N} \|f\|_{\alpha,\beta,\gamma,\delta},\ N \in \mathbf{N}. \tag{D.1.3.14}
$$

(2) *The locally convex topology on $\mathcal{S}(G)$ is Hausdorff and complete, promoting $\mathcal{S}(G)$ to a Fréchet space.*

PROOF. The proof of (1) is standard, similarly to any locally convex topology defined by a countable family of seminorms.

For (2), we first verify completeness by consider a Cauchy net $\{f_i\}_{i \in I}$ in $\mathcal{S}(G)$ for the locally convex topology induced by the family of seminorms $\|\cdot\|_{(\alpha,\beta,\gamma,\delta)}$ from (D.1.3.6), with $I$ a directed set. The uniform limit of $\{f_i\}_{i \in I}$ in $C_0(G)$ exists, since $C_0(G)$ equipped with the uniform norm is a Banach space. We denote such limit by $f$. The restriction to every fibre over the projection $G \to \mathbf{Z}^r \times F$ is a uniform limit of smooth functions with uniformity in each of its derivatives too. Formation of the derivatives $\partial_x^\alpha \partial_z^\beta f$, which exist fibre-wise over $\mathbf{Z}^r \times F$, is continuous over $G$ by uniformity of the convergence and so $f$ is smooth over $G$.

We now show $f_i \to f$ in the topology of $\mathcal{S}(G)$ by using the family of seminorms $\mathcal{P}_1$ in (D.1.3.8) to carry over the classical argument for the completeness of $\mathcal{S}(\mathbf{R}^m)$. We have, for every $\varepsilon > 0$ and uniformly with respect to $(x, z, a, b) \in G$, the net $\{f_i\}_{i \in I}$ being Cauchy in $\mathcal{S}(G)$ and since the locally convex topology on $\mathcal{S}(G)$ is, by Lemma D.1.3.4, equivalently generated by the family of seminorms $\mathcal{P}_1$:

$$
|(1 + |x|^p)(1 + |a|^{p'})(\partial_x^\beta \partial_z^\gamma f_i)(x, z, a, b) - (1 + |x|^p)(1 + |a|^{p'})(\partial_x^\beta \partial_z^\gamma f_j)(x, z, a, b)| < \varepsilon \tag{D.1.3.15}
$$

for all large enough $i, j \in I$ with respect to the partial ordering on $I$ (and depending on $\varepsilon > 0$ and on each choice of $p, p' \ge 0$ and $\beta \in \mathbf{N}^m$, $\gamma \in \mathbf{N}^n$).

The convergence of the net $\{f_i\}_{i \in I}$ to $f$ in $C_0(G)$ being uniform in all derivatives, we may pass to the limit in (D.1.3.15) over $j \in J$ and obtain

$$
|(1 + |x|^p)(1 + |a|^{p'})(\partial_x^\beta \partial_z^\gamma f_i)(x, z, a, b) - (1 + |x|^r)(1 + |a|^{r'})(\partial_x^\alpha \partial_z^\gamma f)(x, z, a, b)| \le \varepsilon \tag{D.1.3.16}
$$

with $(x, z, a, b)$ arbitrary. The exchange in the order of the limit and the derivatives is legitimate by uniformity of the convergence. We may therefore form the supremum in (D.1.3.16) over $(x, z, a, b) \in G$ and obtain that $f \in \mathcal{S}(G)$ and $\|f_i - f\|_{\mathcal{P}_1,(p,p',\beta,\gamma)} \le \varepsilon$ for every $p, p' \ge 0$ and $\beta \in \mathbf{N}^m$, $\gamma \in \mathbf{N}^n$.

This shows that $\{f_i\}_{i \in I}$ converges to $f$ in $\mathcal{S}(G)$, proving completeness of $\mathcal{S}(G)$. Since the collection of seminorms $\mathcal{P}_1$ from (D.1.3.8) is countable, $\mathcal{S}(G)$ is metrizeable. As such, $\mathcal{S}(G)$ is a Fréchet space. $\square$

D.1.3.3. *Nuclearity of the Schwartz-Bruhat space of an elementary abelian Lie group.* We claim the Fréchet locally convex topological $\mathbf{C}$-vector space $\mathcal{S}(G)$ is nuclear. In fact, we can identify it with the finite product of $\pi$-tensor products

$$
\prod_F (\mathcal{S}(\mathbf{R}^m) \widehat{\otimes}_\pi \mathcal{S}(\mathbf{T}^n) \widehat{\otimes}_\pi \mathbf{s}_r)
$$

where $\mathbf{s}_r$ is the (nuclear) space of rapidly decaying sequences $\mathbf{Z}^r \to \mathbf{C}$. This is shown in Lemma D.1.3.7 below.

REMARK D.1.3.6. We caution the reader that the nuclear Fréchet space $\mathfrak{s}$ of rapidly decreasing complex $\mathbf{N}$-indexed sequences is not $\mathbf{s}_r = \mathcal{S}(\mathbf{Z}^r)$ but there is a linear topological isomorphism $\mathbf{s}_r \to \mathfrak{s}$ for every integer $r \ge 1$ (though we will not use this fact).

We recall the construction of $\mathbf{s}_r$ (see [Tre, Remark 51.1, (51.1), p. 527]). Let $s(\mathbf{Z}^r)$ be the $\mathbf{C}$-vector space of $\mathbf{C}$-valued functions on $\mathbf{Z}^r$; i.e., complex sequences indexed by $\mathbf{Z}^r$. The $\mathbf{C}$-linear subspace $\mathbf{s}_r \subset s(\mathbf{Z}^r)$ consists of those sequences $\{s_a\}_{a \in \mathbf{Z}^r}$ such that

$$
p_j(\{s_a\}_{a \in \mathbf{Z}^r}) := \sum_{a \in \mathbf{Z}^r} (1 + |a|)^j |s_a| < \infty \tag{D.1.3.17}
$$

## PDF page 753

D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP · 753

for every integer $j \ge 0$. Endowed with the locally convex topology generated by the family $\{p_j\}_{j \ge 0}$ of seminorms, $\mathbf{s}_r$ is Fréchet since $p_j \le p_{j+1}$ and finiteness of (D.1.3.17) defines $L^1(\mathbf{Z}^r, \mu_j)$ for the measure $\mu_j$ with $\mu_j(\{a\}) = (1 + |a|)^j$. Explicitly, $\mathbf{s}_r$ is (topologically) the inverse limit of the inverse system of spaces $L^1(\mathbf{Z}^r, \mu_j)$. Nuclearity of $\mathbf{s}_r$ is [Tre, Thm. 51.5].

LEMMA D.1.3.7 (Nuclearity in the case of elementary abelian Lie groups). *We have:*

(1) *The injective $\mathbf{C}$-linear map*

$$
\phi : \mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n) \otimes \mathbf{s}_r \otimes \mathbf{C}^F \to \mathcal{S}(G) \tag{D.1.3.18}
$$

*defined by*

$$
\phi(f_1 \otimes f_2 \otimes (\{s_a\}_{a \in \mathbf{Z}^r}) \otimes c) := (f_1 \circ \mathrm{pr}_1) \cdot (f_2 \circ \mathrm{pr}_2) \cdot s \cdot c : G \to \mathbf{C} \tag{D.1.3.19}
$$

*where $s : G \to \mathbf{C}$ is $(x, z, a, b) \mapsto s_a$ and $c : F \to \mathbf{C}$ is a function) induces the projective tensor product topology on the source.*

(2) *The $\mathbf{C}$-linear map $\phi$ from (D.1.3.18) extends uniquely to a linear topological isomorphism$^1$*

$$
\phi : \mathcal{S}(\mathbf{R}^m) \widehat{\otimes}_\pi \mathcal{S}(\mathbf{T}^n) \widehat{\otimes}_\pi \mathbf{s}_r \widehat{\otimes}_\pi \mathbf{C}^F \to \mathcal{S}(G) \tag{D.1.3.20}
$$

(3) *The locally convex topological $\mathbf{C}$-vector space $\mathcal{S}(G)$ and its strong dual $\mathcal{S}(G)'_\beta$ are complete, nuclear, and Montel (reflexive with all closed bounded subsets compact). In particular, both are barrelled.*

Throughout the proof below, we will be using two ingredients from Appendix C.1 on locally convex spaces: Lemma C.2.2.2 on the topology of uniform convergence on the members of the equicontinuous subsets of the dual, together with Remark C.2.3.8 describing the equicontinuous subsets of the continuous dual of a binary injective tensor product (see also Proposition C.2.4.8 for a description of the latter dual as the space of “integral” continuous bi-linear forms).

The idea is to use nuclearity of the tensor factors (say $E, F$, for the sake of this introduction) occurring throughout the argument below, to access the equivalence of the $\pi$- and $\varepsilon$-tensor topologies, for then comparing either topology to the subspace topology induced from the topology of the Schwartz-Bruhat space of the appropriate fine product.

That one of the two topologies is finer than the subspace topology will be the simpler of the two refinement relations to be shown. It is in the proof of the reverse one that we use the $\varepsilon$-topology, and Lemma C.2.2.2 is used to descripbe such topology as the topology of uniform convergence on the subsets of $(E \otimes_\varepsilon F)'$ of the form $(A' \otimes B')^{\circ\circ}$ (bipolar), for $A' \subset E'$ and $B' \subset F'$ equicontinuous.

REMARK D.1.3.8 (On binary tensor products of tempered distributions). Before we can begin the proof of Lemma D.1.3.7, we need to review some facts from Appendix C.1 concerning Schwartz functions valued in certain locally convex spaces since this provides an essential technical tool we will use.

Let $m, m', n, n', r, r' \ge 0$ be fixed integers. Let $T \in \mathcal{S}(\mathbf{R}^m)'_\beta$ and $S \in \mathcal{S}(\mathbf{R}^{m'})'_\beta$ be two tempered distributions. Using Theorem C.5.1.30(4) from Appendix C, we can define the binary tensor product $T \otimes S$ as an element of the strong dual $\mathcal{S}(\mathbf{R}^{m+m'})'_\beta$ (as opposed to only in $\mathcal{S}(\mathbf{R}^m)'_\beta \otimes \mathcal{S}(\mathbf{R}^{m'})'_\beta$) as follows. The linear topological isomorphisms

$$
\rho_1 : \mathcal{S}(\mathbf{R}^{m+m'}) \to \mathcal{S}(\mathbf{R}^m, \mathcal{S}(\mathbf{R}^{m'})),\ \rho_2 : \mathcal{S}(\mathbf{R}^{m+m'}) \to \mathcal{S}(\mathbf{R}^{m'}, \mathcal{S}(\mathbf{R}^m)) \tag{D.1.3.21}
$$

from (C.5.1.48) lead to defining

$$
\langle f, T \otimes S \rangle_{E,E'} = \langle \langle \rho_1(f), S \rangle_{E_2,E_2'}, T \rangle_{E_1,E_1'}. \tag{D.1.3.22}
$$

---
$^1$Must expand proof to also yield $\mathcal{S}(\mathbf{R})^{\widehat{\otimes}_\pi m} \simeq \mathcal{S}(\mathbf{R}^m)$ and likewise for $\mathcal{S}(\mathbf{T}^n)$ and $\mathcal{S}(\mathbf{Z}^r)$.

## PDF page 754

754 · CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS

for $f \in E := \mathcal{S}(\mathbf{R}^{m+m'})$, $E_1 := \mathcal{S}(\mathbf{R}^m)$, and $E_2 := \mathcal{S}(\mathbf{R}^{m'})$. The same argument as in [Tre, Thm. 40.4, p. 416] shows that we have

$$
\langle \langle \rho_1(f), S \rangle_{E_2,E_2'}, T \rangle_{E_1,E_1'} = \langle \langle \rho_2(f), T \rangle_{E_1,E_1'}, S \rangle_{E_2,E_2'} \tag{D.1.3.23}
$$

for all $f \in E$. The assignment from (D.1.3.22) thereby defines a continuous functional on $E$, which we denote by $T \otimes S$ following [Tre, Def. 40.3, p. 417].

Moreover, the assignment $(T, S) \mapsto T \otimes S$ is a separately continuous bi-linear mapping:

$$
\mathcal{S}(\mathbf{R}^m)'_\beta \times \mathcal{S}(\mathbf{R}^{m'})'_\beta \to \mathcal{S}(\mathbf{R}^{m+m'})'_\beta. \tag{D.1.3.24}
$$

By [Tre, Thm. 41.1, p. 421], it is continuous, and therefore induces a continuous linear map:

$$
\mathcal{S}(\mathbf{R}^m)'_\beta \widehat{\otimes}_\pi \mathcal{S}(\mathbf{R}^{m'})'_\beta \to \mathcal{S}(\mathbf{R}^{m+m'})'_\beta. \tag{D.1.3.25}
$$

For $A \subset \mathcal{S}(\mathbf{R}^m)'$ and $B \subset \mathcal{S}(\mathbf{R}^{m'})$ equicontinuous subsets, we will be denoting by $A \otimes B$ the subset of $\mathcal{S}(\mathbf{R}^{m+m'})'_\beta$ defined by:

$$
A \otimes B := \{T \otimes S : T \in A, S \in B\} \subset \mathcal{S}(\mathbf{R}^{m+m'})' \tag{D.1.3.26}
$$

itself an equicontinuous subset.

The same construction applies to $\mathcal{S}(\mathbf{T}^n)$ and $\mathcal{S}(\mathbf{T}^{n'})$, as well as $\mathbf{s}_r$, $\mathbf{s}_{r'}$, replacing $\mathcal{S}(\mathbf{R}^m)$ and $\mathcal{S}(\mathbf{R}^{m'})$. The same notation introduced in (D.1.3.26) will therefore be in force.

PROOF OF LEMMA D.1.3.7. (1) : The map (D.1.3.18) is injective since $\mathrm{Map}(X, k) \otimes \mathrm{Map}(Y, k) \to \mathrm{Map}(X \times Y, k)$ is injective for any sets $X, Y$ and any field $k$. The proof of the topological aspect of (1) will proceed similarly to the proof of [Tre, Thm. 51.6] that treats $\mathbf{R}^m \times \mathbf{R}^n \simeq \mathbf{R}^{n+m}$.

Since boundedness constraints defined by means of the seminorms $q_{\alpha,\beta,\gamma,\delta}$ from (D.1.3.7) do not affect the $F$-factor in $G$, $\mathcal{S}(G)$ splits linearly and topologically as $\prod_F \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r)$, as does $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n) \otimes \mathbf{s}_r \otimes \mathbf{C}^F$ endowed with the projective tensor product topology. We therefore may and do assume that $F = 0$ and rename $\mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r$ as $G$. We now prove that the topology induced on $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n) \otimes \mathbf{s}_r$ by the linear map $\phi$ from (D.1.3.18) is the $\pi$-topology.

The bilinear map:

$$
\psi_1 : \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \times \mathbf{s}_r \to \mathcal{S}(G) \tag{D.1.3.27}
$$

is separately continuous. Since $\mathbf{s}_r$ and $\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n)$ are metrizable and $\mathbf{s}_r$ is Baire (even Fréchet), by [Scha, Ch. III, Cor1 to Thm. 5.1] we see that $\psi_1$ is continuous. As such, by [Scha, Ch. III, 6.2] the injection

$$
j : \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \otimes \mathbf{s}_r \hookrightarrow \mathcal{S}(G) \tag{D.1.3.28}
$$

is continuous for the $\pi$-topology on the source, so the subspace topology induced on the source is coarser than the $\pi$-topology. Since $\mathbf{s}_r$ is nuclear, so $E \otimes_\pi \mathbf{s}_r \to E \otimes_\varepsilon \mathbf{s}_r$ is a topological isomorphism for any locally convex space $E$, to check that the topology induced on $\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \otimes \mathbf{s}_r$ by $j$ is the $\pi$-topology it is enough to check that it is finer than the $\varepsilon$-topology.

We now use the general property for any Hausdorff locally convex topological $\mathbf{C}$-vector space $E$ (see [Scha, Ch. IV, Cor. 3 to 1.5]) that the given topology on $E$ is the same as the topology of uniform convergence on the equicontinuous subsets of $E'$, i.e. the $\mathfrak{S}$-topology on $E$ where $\mathfrak{S}$ is the set of the closed convex circled equicontinuous subsets of $E'_\sigma$ (all weakly compact by [Scha, Ch. III, Cor. to 4.3], hence weakly bounded). We further refer the reader to Lemma C.2.2.2, as well as to Remark C.2.3.8, describing the equicontinuous subsets of the continuous dual of a binary injective tensor product of Hausdorff locally convex topological $\mathbf{C}$-vector spaces (as being contained in the polar of a subset of the form $A \otimes B$, for $A, B$ equicontinuous subsets of the respective continuous duals).

## PDF page 755

D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP · 755

Under the continuous bi-linear mapping:

$$
B : \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n)'_\beta \times (\mathbf{s}_r)'_\beta \to \mathcal{S}(G)'_\beta \tag{D.1.3.29}
$$

from Remark D.1.3.8, we claim that subsets of the form

$$
U \otimes V := \{\varphi \otimes \theta : \varphi \in U, \theta \in V\} \subset \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n)' \otimes (\mathbf{s}_r)'
$$

for equicontinuous $U \subset \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n)'_\sigma$ and $V \subset (\mathbf{s}_r)'_\sigma$ are sent onto equicontinuous subsets of $\mathcal{S}(G)'$.

Letting $G_1 = \mathbf{R}^m \times \mathbf{T}^n$ and $G_2 = \mathbf{Z}^r$, we have a natural linear topological isomorphism $\mathcal{S}(G) \simeq \mathcal{S}(G_1, \mathcal{S}(G_2))$ and if $f \in \mathcal{S}(G)$ corresponds to a Schwartz-class function $\widetilde{f} : G_1 \to \mathcal{S}(G_2)$ then for $\phi_i \in \mathcal{S}(G_i)'$ the composite function $\phi_2 \circ \widetilde{f} : G_1 \to \mathbf{C}$ lies in $\mathcal{S}(G_1)$ (this is applying functoriality of $\mathcal{S}(G_1, E)$ in the locally convex space $E$) and

$$
(B(\phi_1, \phi_2))(f) = \phi_1(\phi_2 \circ \widetilde{f}).
$$

Since $\mathcal{S}(G)$ is a Fréchet space by Lemma D.1.3.5, it is barrelled (as for any Fréchet space [Scha, Ch. III, Cor. to 7.1]) Thus, to check equicontinuity of $B(U \otimes V)$ it suffices (by [Scha, Ch. III, Thm. 4.2]) to check that such subsets of $\mathcal{S}(G)'$ are bounded for the weak topology, which in turn (by the definition of the weak topology) is equivalent to having a bounded set of values on each $f \in \mathcal{S}(G)$. Given an equicontinuous set $U$ of tempered distributions on $\mathbf{R}^m \times \mathbf{T}^n$ and an equicontinuous subset $V$ of $\mathbf{s}'_r$, we need to show that the set of values $(B(u, v))(f) \in \mathbf{C}$ is bounded as $u$ varies through $U$ and $v$ varies through $V$.

The Schwartz property of $\widetilde{f} : G_1 = \mathbf{R}^m \times \mathbf{T}^n \to \mathcal{S}(G_2)$ expresses that each finite set of partials of $\widetilde{f}$ along $\mathbf{R}^m$ multiplied by any finite collection of polynomials on $\mathbf{R}^m$ lands inside a bounded subset of $\mathcal{S}(G_2)$, so by equicontinuity of $V \subset \mathcal{S}(G_2)'$ the subset $\{v \circ \widetilde{f}\}_{v \in V} \subset \mathcal{S}(G_1)$ is likewise bounded (here we recall that boundedness in a Hausdorff locally convex space can be detected using boundedness under all finite collections of seminorms defining the topology). But then by equicontinuity of $U$ it follows that $\{u(v \circ \widetilde{f})\}_{u \in U, v \in V} \subset \mathbf{C}$ is bounded, establishing the equicontinuity of $B(U \otimes V)$.

This implies, in light of the description of the $\varepsilon$-topology by means of the seminorms $\varepsilon_{U,V}$ from (C.2.3.7), that the identity map on $\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \otimes \mathbf{s}_r$ is continuous with respect to the subspace topology via (D.1.3.28) on the source and the $\varepsilon$-topology on the target, because (i) a net $\{T_i\}_{i \in I}$ in $\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \otimes_\varepsilon \mathbf{s}_r$ converges in $\mathcal{S}(G)$ if and only if it converges uniformly on the equicontinuous subsets of $\mathcal{S}(G)'$, and (ii) the subsets $U \otimes V \subset \mathcal{S}(G)'$ are examples of such equicontinuous subsets. But by Remark C.2.3.8, this means that $\{T_i\}_{i \in I}$ converges uniformly on the equicontinuous subsets of $(\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \otimes_\varepsilon \mathbf{s}_r)'$, and hence converges in $\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \otimes_\varepsilon \mathbf{s}_r$ by Lemma C.2.2.2. This proves that the $\varepsilon$-topology on $\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \otimes \mathbf{s}_r$ is at most as fine as the subspace topology arising from (D.1.3.28), and so it completes the proof that the inclusion (D.1.3.28) yields the $\pi$-topology as the subspace topology.

To pass from the single tensor product in (D.1.3.28) to the triple tensor product in (D.1.3.18), now let

$$
\psi_2 : \mathcal{S}(\mathbf{R}^m) \times \mathcal{S}(\mathbf{T}^n) \to \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n) \tag{D.1.3.30}
$$

be the canonical bilinear map. Since $\mathcal{S}(\mathbf{R}^m)$ and $\mathcal{S}(\mathbf{T}^n)$ are Fréchet spaces by Lemma D.1.3.5, the separately continuous bilinear map $\psi_2$ is continuous by [Scha, Ch. III, Cor. to Thm. 5.1]. In particular, the subspace topology arising from the associated linear injection

$$
j' : \mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n) \to \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n)
$$

is coarser than the $\pi$-topology on $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n)$.

We will next show that this subspace topology is also finer than the $\varepsilon$-topology on $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n)$. Once that is shown, since nuclearity of $\mathcal{S}(\mathbf{R}^m)$ (by [Tre, Cor. to Thm. 51.5, p. 530]) identifies that $\varepsilon$-topology with the $\pi$-topology, we would have proved the topology induced by $j'$ on $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n)$ is exactly the $\pi$-topology.

For $V \subset \mathcal{S}(\mathbf{T}^n)$ and $U \subset \mathcal{S}(\mathbf{R}^m)$ varying over neighborhood bases $\mathcal{V}, \mathcal{U}$ at $0$ for the locally convex topologies, the convex circled hull of the sets $U \otimes V := \{u \otimes v : u \in U, v \in V\}$ constitute a subbase of $0$-neighborhoods in

## PDF page 756

756 · CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS

$\mathcal{S}(\mathbf{R}^m) \otimes_\pi \mathcal{S}(\mathbf{T}^n)$ by the definition of the $\pi$-topology. For equicontinuous subsets $A \subset \mathcal{S}(\mathbf{R}^m)'$ and $B \subset \mathcal{S}(\mathbf{T}^n)'$, the subsets $A \otimes B \subset \mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n)'$ are equicontinuous by an argument similar to what we have seen above with $\mathcal{S}((\mathbf{R}^m \times \mathbf{T}^n) \times \mathbf{s}_r)$. Thus, exactly as before, it follows that the subspace topology via $j'$ is finer than the $\varepsilon$-topology, as desired.

Since $\phi = (\psi_2 \times \mathrm{id}_{\mathbf{s}_r}) \circ \psi_1$, it follows that the subspace topology induced on $(\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n)) \otimes \mathbf{s}_r$ by $\phi$ is the projective tensor product of the $\pi$-topology on $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n)$ and the locally convex topology on $\mathbf{s}_r$. The formation of projective tensor product topologies is associative by inspection of a base of $0$-neighborhoods, so the topology induced via (D.1.3.18) on $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n) \otimes \mathbf{s}_r$ from the topology on $\mathcal{S}(G)$ is the $\pi$-topology.

(2) : By (1) and completeness of $\mathcal{S}(G)$ (from Lemma D.1.3.5(2)), our task amounts to showing the denseness of the image of $\phi$ from (D.1.3.18), for which it is enough to treat the case $F = 0$.

Let $j \ge 0$ be an integer, and write $K'_j \subset \mathbf{Z}^r$ for the finite subset of those vectors $a \in \mathbf{Z}^r$ such that $|a| = \sum_{i=1}^r |a_i| \le j$. Let $\rho_j : G \to \mathbf{C}$ be the indicator function of $K_j := \mathbf{R}^m \times \mathbf{T}^n \times K'_j \subset \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r = G$. Let $f \in \mathcal{S}(G)$ be the arbitrary element, and denote by $f_j := f \cdot \rho_j : G \to \mathbf{C}$ the product function, for each integer $j \ge 0$, with $\rho_j$ the indicator function of $K_j$. Since $K_j$ is a subset of $G$, $f_j$ is an element of $\mathcal{S}(G)$, since it is smooth over $G$ and each of the seminorms $\|\cdot\|_{\alpha,\beta,\gamma,\delta}$ from (D.1.3.7) is finite on $f_j$, an upper bound on the value of each, being given by $\|f\|_{\alpha,\beta,\gamma,\delta}$. We’ll show the sequence $\{f_j\}_{j \ge 0} \subset \mathcal{S}(G)$ converges to $f$ in $\mathcal{S}(G)$. To see this, by Lemma D.1.3.4 it is enough to show that for every pair of integers $N, N' \ge 0$, every $\alpha \in \mathbf{N}^m$, and every $\beta \in \mathbf{N}^n$ we have

$$
\lim_{j \to +\infty} \|f - f_j\|_{\mathcal{P}_1,(N,N',\alpha,\beta)} = 0. \tag{D.1.3.31}
$$

Keeping in mind that we passed to the case $F = 0$, for every tuple of integers $N_i, N'_i \ge 0$ ($i = 1, 2$), every $\alpha \in \mathbf{N}^m$, $\beta \in \mathbf{N}^n$, by a standard compactness argument (similar to classical ones with Schwartz spaces of Euclidean spaces) there is a large enough positive real number $C$ and large enough integers $N_3 \ge N_2$ and $N'_3 \ge N'_2$ such that

$$
|(1 + |x|^{N_1})(1 + |a|^{N'_1})| \frac{|(1 + |x|^{N_2})(1 + |a|^{N'_2}) \partial_x^\alpha \partial_z^\beta h(x, z, a)|}{|(1 + |x|^{N_1})(1 + |a|^{N'_1})|} \le \frac{C}{|(1 + |x|^{N_1})(1 + |a|^{N'_1})|} \|h\|_{\mathcal{P}_1,(N_3,N'_3,\alpha,\beta)} \tag{D.1.3.32}
$$

for every $h \in \mathcal{S}(G)$.

To summarize, we obtain the estimate:

$$
\|h\|_{\mathcal{P}_1,(N_2,N'_2,\alpha,\beta)} \le \frac{C}{|(1 + |x|^{N_1})(1 + |a|^{N'_1})|} \|h\|_{\mathcal{P}_1,(N_3,N'_3,\alpha,\beta)} \tag{D.1.3.33}
$$

for all $(x, a) \in \mathbf{R}^m \times \mathbf{Z}^r$, $\alpha \in \mathbf{N}^m$, all integers $N_1, N'_1, N_2, N'_2 \ge 0$, and for all integers $N_3, N'_3 \ge 0$ large enough. We apply (D.1.3.33) to $h = f - f_j$ to obtain

$$
|(1 + |x|^{N_2})(1 + |a|^{N'_2}) \partial_x^\alpha \partial_z^\beta (f - f_j)(x, z, a)| \le \frac{C}{|(1 + |x|^{N_1})(1 + |a|^{N'_1})|} (\|f\|_{\mathcal{P}_1,(N_3,N'_3,\alpha,\beta)} + \|f_j\|_{\mathcal{P}_1,(N_3,N'_3,\alpha,\beta)}) \tag{D.1.3.34}
$$

and upon using $\|f_j\|_{\mathcal{P}_1,(N,N',\alpha,\beta)} \le \|f\|_{\mathcal{P}_1,(N,N',\alpha,\beta)}$ for all $N, N' \ge 0$ and $\alpha \in \mathbf{N}^m$, $\beta \in \mathbf{N}^n$, we get that for all integers $j \ge 0$:

$$
|(1 + |x|^N)(1 + |a|^{N'}) \partial_x^\alpha \partial_z^\beta (f - f_j)(x, z, a)| \le \frac{2C}{1 + |a|^{N'_1}} \|f\|_{\mathcal{P}_1,(N_3,N'_3,\alpha,\beta)} \tag{D.1.3.35}
$$

The left side of (D.1.3.35) is supported away from $K_j \subset G$, and so it is globally bounded above by the supremum over the complement of $K_j$ of the right side of (D.1.3.35), which, upon enlarging $j \ge 0$ (to increase $|a|$ for $a \notin K_j$), we may render as small as we please, uniformly over $\mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r$. This proves that (D.1.3.31).

## PDF page 757

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **757**

To prove the denseness of the image of $\phi$ from (D.1.3.18) within $\mathcal{S}(G)$, it is therefore enough to prove that $\phi$ maps $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n) \otimes C(K'_j)$ onto a dense subset of $\rho_j \cdot \mathcal{S}(G) \subset \mathcal{S}(G)$, since the union of the images of $\mathcal{S}(\mathbf{R}^m) \otimes \mathcal{S}(\mathbf{T}^n) \otimes C(K'_j)$ is contained in the image of $\phi$, and the union of the $\rho_j \cdot \mathcal{S}(G)$ is dense in $\mathcal{S}(G)$. Since $K_j$ is a finite set, which we enumerate as $K_j = \{x_{j1}, \ldots, x_{jN_j}\}$, for any $f \in \rho_j \cdot \mathcal{S}(G)$ we may write $f = \sum_{i=1}^{N_j} f_i$ with $f_i = \rho_{ij} \cdot f$ where $\rho_{ij}$ is the indicator function of the fibre in $\mathbf{R}^m \times \mathbf{T}^n \times K_j$ over $x_{ji}$. It is therefore enouh to prove that each $f_i$ can be approximated within $\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n \times \{x_{ji}\})$ by elements of the image of $\phi$.

We are therefore reduced to the case $G = \mathbf{R}^m \times \mathbf{T}^n$. The same method as above whereby we reduced ourselves to removing a $\mathbf{Z}^r$-factor could be applied if $\mathbf{T}^n$ were replaced with $\mathbf{Z}^n$. We shall access this idea by harness the Fourier transform. More specifically, by [Tre, Thm. 51.3], the Fourier transform for $\mathbf{T}^n$ induces a continuous bijection $\mathcal{F} : \mathcal{S}(\mathbf{T}^n) \to \mathcal{S}(\mathbf{Z}^n)$, which in turn is a topological isomorphism by the Open Mapping Theorem for Fréchet spaces. Thus, we get a linear topological isomorphism

$$
\mathcal{S}(G) \simeq \mathcal{S}(\mathbf{R}^m, \mathcal{S}(\mathbf{T}^n)) \overset{\mathcal{F}}{\simeq} \mathcal{S}(\mathbf{R}^m, \mathcal{S}(\mathbf{Z}^n)) \simeq \mathcal{S}(\mathbf{R}^m \times \mathbf{Z}^n)
$$

under which $\phi$ from (D.1.3.18) for $\mathbf{R}^m \times \mathbf{T}^n$ is carried over$^2$ to the analogue for $\mathbf{R}^m \times \mathbf{Z}^n$. Thus, the denseness assertion is converted into the case of the group $G = \mathbf{R}^m \times \mathbf{Z}^n$, and so then reduces to $G = \mathbf{R}^m$ that is obvious.

(3) : By Lemma D.1.3.5, $\mathcal{S}(G)$ is Hausdorff and complete. By (2), $\mathcal{S}(G)$ is isomorphic to the completed projective tensor product of $\mathcal{S}(\mathbf{R}^m)$, $\mathcal{S}(\mathbf{T}^n)$, $\mathbf{s}_r = \mathcal{S}(\mathbf{Z}^r)$ and $\mathbf{C}^F$. Each is nuclear (see [Tre, Cor. to Thm. 51.5] for $\mathcal{S}(\mathbf{R}^m)$ and [Tre, Thms. 51.3, 51.5] for $\mathcal{S}(\mathbf{T}^n)$ and $\mathbf{s}_r$), so $\mathcal{S}(G)$ is nuclear by [Scha, Ch. III, 7,5]. Since $\mathcal{S}(G)$ is a Fréchet space by Lemma D.1.3.5, its strong dual $\mathcal{S}(G)'_{\beta}$ is complete (as for any metrizable locally convex space) by [Scha, Ch. II, 8.1; Ch. IV, 6.1]. Likewise nuclearity of the strong dual is inherited from that of the Fréchet $\mathcal{S}(G)$ by [Tre, Prop. 50.6]. The Montel property for $\mathcal{S}(G)$ (in particular, reflexivity) holds as for all nuclear Fréchet spaces [Tre, Cor. 3 to Prop. 50.2], and the strong dual thereby inherits the Montel property (in particular, reflexivity) by [Scha, Ch. IV, 5.9]. Reflexive spaces are barrelled by [Scha, Ch. IV, p. 144], so $\mathcal{S}(G)$ and $\mathcal{S}(G)'_{\beta}$ are barrelled. $\square$

**D.1.4. Structure theory of Hausdorff locally compact abelian groups.** In this section, we recall the structure theory of Hausdorff locally compact abelian groups, in preparation for the definition of their Schwartz-Bruhat space of functions.

DEFINITION D.1.4.1. A Hausdorff locally compact abelian group $G$ is called *compactly generated* if and only if there exists a compact neighborhood $U \subset G$ of the identity that generates $G$ as a group.

THEOREM D.1.4.2. *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is locally Euclidean (as a topological space). There exist integers $m, n \ge 0$ and a discrete abelian group $D$ so that*

(D.1.4.1)
$$
G \xrightarrow{\simeq} \mathbf{R}^m \times \mathbf{T}^n \times D.
$$

This is [DE, Thm. 4.2.4]. We record here the following structural result on Hausdorff locally compact abelian groups, combined with Pontryagin duality:

THEOREM D.1.4.3. *Let $G$ be a Hausdorff locally compact abelian group.*

(1) *The group $G$ is compactly generated if and only if $\widehat{G}$ is locally Euclidean, and if $G$ is compactly generated then so is every closed subgroup $H$ and the quotient $G/H$.*

(2) *The group $G$ is compactly generated and locally Euclidean if and only if there exist integers $m, n, k \ge 0$, a finite abelian group $F$, and an isomorphism of Hausdorff locally compact abelian groups:*

(D.1.4.2)
$$
G \xrightarrow{\simeq} \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^k \times F.
$$

$^2$briefly address calculation for this compatibility of $\phi$

## PDF page 758

**758** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

The Theorem is [DE, Cors. 4.2.5, 4.2.6], apart from the assertions about $H$ and $G/H$ in (1). By the characterization of compact generatedness via the dual being locally Euclidean in (1), the assertions for $H$ and $G/H$ in (1) reduce via Theorem D.1.4.2 to the standard fact that for any $G$ as in (D.1.4.1) all closed subgroups $H$ and quotients $G/H$ are also of the same type (for possibility different $m, n, D$).

D.1.4.1. *Exhaustion by compactly generated open subgroups, approximation by abelian Lie groups.* Every Hausdorff locally compact abelian group $G$ can be written as a filtered colimit

(D.1.4.3)
$$
G = \operatorname*{\mathrm{colim}}_{H \in \mathrm{CG}(G)} H
$$

where $\mathrm{CG}(G)$ is the set of all *open* compactly generated abelian subgroups of $G$, filtered under open inclusions. As a consequence of Theorem D.1.4.2 and Theorem D.1.4.3, combined with Pontryagin duality and (D.1.4.3) applied to $\widehat{G}$, we get:

LEMMA D.1.4.4. *Let $G$ be a Hausdorff locally compact abelian group, and $\mathrm{CG}(\widehat{G})$ the set of all open compactly generated subgroups of $\widehat{G}$, cofiltered under open inclusions. Then the canonical continuous group homomorphism*

(D.1.4.4)
$$
G \to \lim_{H \in \mathrm{CG}(\widehat{G})} \widehat{H}
$$

*is an isomorphism of topological groups.*

In particular, every Hausdorff locally compact abelian group is canonically isomorphic to a cofiltered inverse limit of locally Euclidean groups. To define the Schwartz space $\mathcal{S}(G)$ of a general Hausdorff locally compact abelian group, we will therefore proceed as in [Bru]: first address the case of locally Euclidean groups, and then propagate the definition to general $G$ as a locally convex inductive limit topological $\mathbf{C}$-vector space using (D.1.4.4).

D.1.4.2. *Basic properties of duals and orthogonals.* Recall that Pontryagin duality provides a perfect continuous pairing

(D.1.4.5)
$$
\langle \cdot, \cdot \rangle_{G, \widehat{G}} : G \times \widehat{G} \to U(1) \subset \mathbf{C}^{\times}
$$

enabling us to construct the following subgroups of $G$ and $\widehat{G}$:

DEFINITION D.1.4.5. Let $G$ be a Hausdorff locally compact abelian group, and $H \subset G$ a subgroup. We define

(D.1.4.6)
$$
H^{\perp} := \{\chi \in \widehat{G} : \chi(H) = 1\}
$$

and refer to it as the *annihilator* of $H$ in $\widehat{G}$. By Pontryagin duality, for $\Gamma \subset \widehat{G}$ a subgroup we have

(D.1.4.7)
$$
\Gamma^{\perp} = \{g \in G : \chi(g) = 1 \text{ for all } \chi \in \Gamma\}.
$$

LEMMA D.1.4.6. *Let $G$ be a Hausdorff locally compact abelian group, $H \subset G$ a closed subgroup. Then:*

(1) $H^{\perp\perp} = H$ *as closed subgroups of $G$.*

(2) $H^{\perp} \to \widehat{G/H}$ *and* $\widehat{G}/H^{\perp} \to \widehat{H}$ *are topological isomorphisms.*

(3) *If $H$ is compact then $H^{\perp}$ is open in $\widehat{G}$.*

(4) *If $H$ is open in $G$ then $H^{\perp}$ is compact.*

PROOF. (1) and (2) are [DE, Prop.3.6.1]. By compact-discrete duality [DE, Prop. 3.1.5], (3) and (4) then follow from (2), noting that every open subgroup of $G$ is closed. $\square$

## PDF page 759

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **759**

D.1.4.3. *General structural results.* From Lemma D.1.4.4, if we denote by $i$ a general element of the set $\mathrm{CG}(\widehat{G})$ of open compactly generated abelian subgroups of $\widehat{G}$ and write $U_i$ for Pontryagin dual of the compactly generated open subgroup of $G$ that $i$ labels then

(D.1.4.8)
$$
\gamma : G \xrightarrow{\simeq} \lim_{i \in \mathrm{CG}(\widehat{G})} U_i.
$$

Using Lemma D.1.4.6, the natural continuous map

(D.1.4.9)
$$
\gamma_i : G \to U_i
$$

is a surjective quotient homomorphism with compact kernel

(D.1.4.10)
$$
K_i := \ker(\gamma_i) \subset G
$$

that is the annihilator of the open compactly generated subgroup $\widehat{U_i}$ of $\widehat{G}$. Since (D.1.4.8) is a topological isomorphism, the $U_i$'s become arbitrarily small around $1$ in $G$.

We denote by $j$ the general element of the set $\mathrm{CG}(G)$ of open compactly generated subgroups of $G$, and write $G_j$ for the open compactly generated subgroup of $G$ that $j$ labels. For any $i \in \mathrm{CG}(\widehat{G})$, since

$$
\operatorname*{\mathrm{colim}}_{j \in \mathrm{CG}(G)} G_j = G
$$

there exists a large enough (with respect to the partial ordering of $\mathrm{CG}(G)$ by upwards inclusion) $j_0 \in \mathrm{CG}(G)$ such that the inclusion homomorphism $K_i \to G$ factors through $G_j$ for all $j \ge j_0$. In other words, $K_i$ is a subgroup of $G_j$ for all $j \ge j_0$ in $\mathrm{CG}(G)$.

The compact $K_i$ is a closed subgroup of the open compactly generated subgroup $G_j$ of $G$ for every $j \ge j_0$. In particular, the quotient group

(D.1.4.11)
$$
A_{ij} := G_j / K_i
$$

is Hausdorff, locally compact, compactly generated and the quotient map $G_j \to A_{ij}$ is clearly open. Since $K_i$ is the kernel of $\gamma_i$ from (D.1.4.9), $A_{ij}$ is a subgroup of $U_i$ for every $j \ge j_0$ and the natural continuous homomorphism

$$
G_j \to \lim_i A_{ij}
$$

(carving out open subgroups on both sides of (D.1.4.8)) is an isomorphism. The group $A_{ij}$ is locally Euclidean since it is open in $U_i$ that is locally Euclidean (by Theorem D.1.4.3(1)).

By Lemma D.1.4.3(2), there exist integers $m, n, k \ge 0$ and a finite group $F$, together with an isomorphism of Hausdorff locally compact abelian groups

(D.1.4.12)
$$
A_{ij} \xrightarrow{\simeq} \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^k \times F
$$

We associate to each $i \in \mathrm{CG}(\widehat{G})$ the set $J_i := \{j \in \mathrm{CG}(G) : K_i \subset G_j\}$. Then $J_i$ inherits a partial order by upwards inclusion of open compactly generated subgroups of $G$. The collection of open subgroups $A_{ij} \subset U_i$ for all $j \in J_i$ exhausts $U_i$ by open compactly generated subgroups, and each $A_{ij}$ is an abelian Lie group with finite component group.

We therefore have, as Hausdorff locally compact abelian groups

(D.1.4.13)
$$
\gamma : G \xrightarrow{\simeq} \lim_{i \in \mathrm{CG}(\widehat{G})} \operatorname*{\mathrm{colim}}_{j \in J_i} A_{ij}
$$

(with open inclusions as transition maps in the colimit) because $U_i = \operatorname*{\mathrm{colim}}_{j \in J_i} A_{ij}$. The observation to make is as follows, as in [Wa, (1.3)]. For each $j \in \mathrm{CG}(G)$, we may form the set $I_j$ defined as

(D.1.4.14)
$$
I_j := \{i \in \mathrm{CG}(\widehat{G}) : K_i \subset G_j\} \subset \mathrm{CG}(\widehat{G})
$$

## PDF page 760

**760** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

(recall we noted that the $K_i$'s become arbitrarily small in $G$) which inherits a unique cofiltered set structure from the partial ordering by upwards inclusion on open subgroups of $\widehat{G}$, turned downwards by the Pontryagin duality functor. We thereby obtain:

LEMMA D.1.4.7 (Structure of Hausdorff locally compact abelian groups). *Let $G$ be a Hausdorff locally compact abelian group, $j \in \mathrm{CG}(G)$, and $G_j$ the corresponding open compactly generated subgroup. Then, as Hausdorff locally compact abelian groups, we have a canonical isomorphism:*

(D.1.4.15)
$$
\delta_j : G_j \xrightarrow{\simeq} \lim_{i \in I_j} A_{ij}.
$$

*In particular, each $G_j$ is, canonically, a cofiltered limit of abelian Lie groups with finite component group, and the $\delta_j$'s induce a unique isomorphism of Hausdorff locally compact abelian groups*

(D.1.4.16)
$$
\delta : G \xrightarrow{\simeq} \operatorname*{\mathrm{colim}}_{j \in \mathrm{CG}(G)} \lim_{i \in I_j} A_{ij}
$$

*(with open inclusions as transition maps in the colimit).*

The most important takeaways from Lemma D.1.4.7 and the discussion preceding it are that for any Hausdorff locally compact abelian group $G$, there exist a canonical collection of compact subgroups $k \subset G$ (forming an inverse system under reverse inclusion, and becoming arbitrarily small in $G$) such that

- $k^{\perp}$ is open and compactly generated in $\widehat{G}$ (in the discussion above, $K_i^{\perp} = \widehat{G/K_i} = \widehat{U_i}$ is compactly generated),
- each $k$ is contained in some open compactly generated subgroup $\Gamma$ of $G$ with such $\Gamma$'s directed and exhausting $G$ (e.g., the $\Gamma$'s can be taken to be the $G_j$'s in the preceding discussion),
- the quotient $\Gamma/k$ is an elementary abelian Lie group.

Moreover, each open compactly generated subgroup $\Gamma$ of $G$ is isomorphic to the inverse limit of quotients $\Gamma/k'$, where $k'$ varies through all sufficiently small $k$ as above.

**D.1.5. Schwartz-Bruhat space of a Hausdorff locally compact abelian group.** The scope of this subsection is to define the Schwartz-Bruhat space of an arbitrary Hausdorff locally compact abelian group $G$, and fill in the arguments for [Bru, §9, Prop. 11] in the special case when $G$ is second countable. We will only briefly indicate how the results extend beyond the second-countable case.

D.1.5.1. *Good subgroups and structural pairs.* Here is terminology and notation following [Bru, §9]:

DEFINITION D.1.5.1 (Structural pairs of $G$). Let $G$ be a Hausdorff locally compact abelian group.

(1) A closed subgroup $k \subset G$ is called *good* if and only if its annihilator $k^{\perp} \subset \widehat{G}$ is both open (equivalent to compactness of $k$) and compactly generated.

(2) A pair $(\Gamma, k)$ of subgroups of $G$ is called *structural* if and only if $\Gamma \subset G$ is an open compactly generated subgroup of $G$, $k \subset G$ is a good subgroup of $G$, and $k \subset \Gamma$.

We define $\mathcal{F}$ the set of structural pairs $(\Gamma, k)$ of $G$.

Note that if $k_1, k_2 \subset G$ are good subgroups then so is $k_1 \cap k_2$. To see this, it suffices to show that the evident inclusion $k_1^{\perp} k_2^{\perp} \subset (k_1 \cap k_2)^{\perp}$ is an equality. This amounts to surjectivity of $k_1^{\perp} \times k_2^{\perp} \to (k_1 \cap k_2)^{\perp}$, so it suffices to check that the injective dual map $G/(k_1 \cap k_2) \to (G/k_1) \times (G/k_2)$ has closed image. But this image is that of the closed diagonal in $G \times G$ under the quotient map $G \times G \to (G/k_1) \times (G/k_2)$ which is proper since the $k_i$'s are compact.

LEMMA D.1.5.2 (Properties of structural pairs). *Let $G$ be a Hausdorff locally compact abelian group. Then the set $\mathcal{F}$ of structural pairs of $G$ is filtered under the partial ordering:*

(D.1.5.1)
$$
(k_1, \Gamma_1) \preceq (k_2, \Gamma_2)
$$

## PDF page 761

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **761**

*when $\Gamma_1 \subset \Gamma_2$ and $k_1 \supset k_2$. Moreover, upon denoting by $\mu_G$ a fixed choice of Haar measure on $G$ and by $\mu_{\widehat{G}}$ the induced Plancherel measure on $\widehat{G}$, we have:*

(1) *For any structural pair $(k, \Gamma)$ of $G$, $\Gamma/k$ is an elementary abelian Lie group.*

(2) *The pair $(\Gamma^{\perp}, k^{\perp})$ is structural for $\widehat{G}$.*

(3) *Let $f : G \to \mathbf{C}$ be an $\mu_G$-integrable function with $\mu_{\widehat{G}}$-integrable Fourier transform, and $H \subset G$ a closed subgroup. Then $f$ is $H$-invariant if and only if the continuous Fourier transform $\widehat{f} : \widehat{G} \to \mathbf{C}$ of $f$ is supported on $H^{\perp}$. In particular, for $(k, \Gamma)$ a structural pair of $G$ and $f : G \to \mathbf{C}$ a $\mu_G$-integrable function with $\mu_{\widehat{G}}$-integrable Fourier transform, then $f$ is supported on $\Gamma$ and $k$-invariant if and only if $\widehat{f}$ is $\Gamma^{\perp}$-invariant and supported on $k^{\perp}$.*

PROOF. To see that the partial ordering defined by (D.1.5.1) is filtered, it is enough to check that for any two structural pairs $(k_1, \Gamma_1)$ and $(k_2, \Gamma_2)$, there exists a third $(k, \Gamma)$ satisfying $(k_i, \Gamma_i) \preceq (k, \Gamma)$ for $i = 1, 2$. Recalling that $k_1 \cap k_2$ is good, we have the relations among structural pairs

$$
(k_i, \Gamma_i) \preceq (k_i, \Gamma_1 \Gamma_2) \preceq (k_1 \cap k_2, \Gamma_1 \Gamma_2).
$$

(1) : This is a consequence of Theorem D.1.4.3(2) provided we can show the locally compact Hausdorff group $\Gamma/k$ is both compactly generated and locally Euclidean. It is compactly generated because it is a quotient of $\Gamma$ that is compactly generated. For the locally Euclidean property, it is the same as $\widehat{\Gamma/k}$ being compactly generated (by Theorem D.1.4.3(1)). Note that $\widehat{\Gamma/k} = k^{\perp} \cap \widehat{\Gamma}$ inside $\widehat{G}$, so it is a closed subgroup of the group $k^{\perp}$ that is compactly generated by the meaning of $(k, \Gamma)$ being good. Thus, we are done since compact generation is inherited by closed subgroups (Theorem D.1.4.3(1)).

(2) : By definition, $k^{\perp}$ is open and compactly generated as a subgroup of $\widehat{G}$. It contains $\Gamma^{\perp}$, and $(\Gamma^{\perp})^{\perp} = \Gamma \subset G$ is open and compactly generated.

(3) : Since $f$ that is $\mu_G$-integrable with Fourier transform $\widehat{f}$ that is $\mu_{\widehat{G}}$-integrable, by Lemma D.1.1.2(5) it follows that $f$ and $\widehat{f}$ are each continuous and Fourier Inversion (D.1.1.11) holds everywhere for both.

Assume $f$ is $H$-invariant. To show $\widehat{f} : \widehat{G} \to \mathbf{C}$ is supported in $H^{\perp}$, we pick $\chi \in \widehat{G}$ *not* lying inside $H^{\perp}$ and aim to show $\widehat{f}(\chi) = 0$. There certainly exists some $h_0 \in H$ such that $\chi(h_0) \ne 1$ (as $\chi \notin H^{\perp}$), so

$$
\widehat{f}(\chi) = \int_G f(g) \overline{\chi}(g) \mathrm{d}g = \int_G f(gh_0) \overline{\chi}(gh_0) \mathrm{d}g = \overline{\chi}(h_0) \widehat{f}(\chi)
$$

(the final equality uses the assumed $H$-invariance of $f$). This forces $\widehat{f}(\chi) = 0$ as desired. For the converse, if $\widehat{f}$ is supported on $H^{\perp}$ then to see $f$ is $H$-invariant we compute for $h \in H$ and $g \in G$ that $f(hg)$ is equal to

$$
\mathcal{F}_{\widehat{G}}(\widehat{f})(h^{-1}g^{-1}) = \int_{\widehat{G}} \widehat{f}(\chi) \chi(hg) \mathrm{d}\mu_{\widehat{G}}(\chi) = \int_{H^{\perp}} \widehat{f}(\chi) \chi(hg) \mathrm{d}\mu_{\widehat{G}}(\chi) = \int_{H^{\perp}} \widehat{f}(\chi) \chi(g) \mathrm{d}\mu_{\widehat{G}}(\chi),
$$

which is equal to $f(g)$ by Fourier inversion (since $\widehat{f}$ is supported on $H^{\perp}$). This is the $H$-invariance of $f$.

Applying the preceding with $H = \Gamma \subset G$ and then with $H = k^{\perp} \subset \widehat{G}$ (whose orthogonal in $G$ is $k$), it follows via Fourier Inversion in both directions that $f$ is supported in $\Gamma$ if and only if $\widehat{f}$ is $\Gamma^{\perp}$-invariant and $f$ is $k$-invariant if and only if $\widehat{f}$ is supported in $k^{\perp}$. $\square$

D.1.5.2. *The Schwartz-Bruhat space $\mathcal{S}(G)$.* For $G$ a Hausdorff locally compact abelian group, and $(k, \Gamma)$ a structural pair of $G$, we write:

(D.1.5.2)
$$
r_{(k, \Gamma)} : \Gamma \to \Gamma/k
$$

for the continuous quotient homomorphism. Recall that $k$ is one of the compact groups $K_i$ of (D.1.4.10) and Lemma D.1.4.7, indexed by the set $\mathrm{CG}(\widehat{G})$ of open compactly generated subgroups of $\widehat{G}$ (by associating to $k$ its annihilator), and $r_{(k, \Gamma)}$ is the continuous quotient homomorphism induced by $\gamma_i$ from (D.1.4.9).

## PDF page 762

**762** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

DEFINITION D.1.5.3 (Schwartz-Bruhat functions on Hausdorff locally compact abelian groups). Let $G$ be a Hausdorff locally compact abelian group, $f : G \to \mathbf{C}$ a function.

(1) Let $p \ge 0$ be an integer. We say $f$ is *$p$-times differentiable* if and only if there exists a good subgroup $k \subset G$ such that $f$ is $k$-invariant, and for every structural pair $(k, \Gamma)$ of $G$ the restriction $f|_{\Gamma}$ is such that the unique function $f_0 : \Gamma/k \to \mathbf{C}$ satisfying $f|_{\Gamma} = f_0 \circ r_{(k, \Gamma)}$ is $C^p$ on the Lie group $\Gamma/k$ (for its unique smooth structure respecting the group structure). We denote by $C^p(G)$ the $\mathbf{C}$-vector space of $p$-times differentiable functions on $G$. We say $f$ is *smooth* if and only if it is $p$-times differentiable on $G$ for every integer $p \ge 0$. We denote by $C^{\infty}(G)$ the $\mathbf{C}$-vector space of smooth functions on $G$.

(2) We say $f$ is a *Schwartz-Bruhat function* on $G$ if and only if:

(1) There exists a structural pair $(k, \Gamma)$ of $G$ such that $f$ is supported in $\Gamma$ and $k$-invariant.

(2) The unique $f_0 \in C^{\infty}(\Gamma/k)$ such that $f = r_{(k, \Gamma)} \circ f_0$ satisfies the following condition: for a choice of isomorphism

(D.1.5.3)
$$
\phi_0 : \Gamma/k \to \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F
$$

for unique integers $m, n, r \ge 0$ and a finite abelian group $F$, the smooth function $f_0 \circ \phi_0^{-1}$ is of rapid decay at infinity on $\Gamma/k$ in the sense of Definition D.1.3.1(2).

We denote by $\mathcal{S}(k, \Gamma)$ the $\mathbf{C}$-vector space of smooth functions on $G$ supported in $\Gamma$ and $k$-invariant, such that the unique $\mathbf{C}$-valued smooth function induced on the quotient $\Gamma/k$ has rapid decay at infinity on $\Gamma/k$. We topologize $\mathcal{S}(k, \Gamma)$ with the Hausdorff locally convex topology of $\mathcal{S}(\mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F)$ by transport of structure along the isomorphism $\phi_0$ of Hausdorff locally compact abelian groups provided by (D.1.5.3); this is well-defined by Lemma D.1.3.3.

We claim that the collection of function spaces $\mathcal{S}(k, \Gamma)$ on $G$ forms a directed system with respect to the partial ordering $(k_1, \Gamma_1) \preceq (k_2, \Gamma_2)$. For this we just have to check:

LEMMA D.1.5.4. *Pullback along the proper map $\Gamma_1/k_2 \twoheadrightarrow \Gamma_1/k_1$ carries $\mathcal{S}(\Gamma_1/k_1)$ to functions on the open subgroup $\Gamma_1/k_2 \subset \Gamma_2/k_2$ whose extension by $0$ to $\Gamma_2/k_2$ lies in $\mathcal{S}(\Gamma_2/k_2)$ (where each $\Gamma_i/k_i$ is an elementary abelian Lie group, so the open subgroup $\Gamma_1/k_2 \subset \Gamma_2/k_2$ is also an elementary abelian Lie group). The resulting inclusion $\mathcal{S}(\Gamma_1/k_1) \to \mathcal{S}(\Gamma_2/k_2)$ is a topological embedding (hence closed, by completeness of $\mathcal{S}(\Gamma_1/k_1)$).*

PROOF. We just have to check that for an elementary abelian Lie group $A$, compact subgroup $k \subset A$, and open subgroup $A' \subset A$:

(i) pullback along $A \twoheadrightarrow A/k$ carries $\mathcal{S}(A/k)$ into $\mathcal{S}(A)$ via a topological embedding onto the subspace of $k$-invariant elements.

(ii) Extension by zero carries $\mathcal{S}(A')$ into $\mathcal{S}(A)$ via a topological embedding.

First we settle (i). By consideration of the maximal compact subgroup of $A$ and the structure of connected compact abelian Lie groups, we can *choose* an isomorphism

$$
A \simeq \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F
$$

so that $k$ is the product of some of the $\mathbf{T}$-factors and a subgroup $F' \subset F$ *inside $A$*. Thus, we get compatible descriptions of $\mathcal{S}(A)$ and $\mathcal{S}(k)$, so also $\mathcal{S}(A/k)$, as completed tensor products in (D.1.3.20). This reduces us to the separate cases $A = \mathbf{R}^m, \mathbf{T}^n, \mathbf{Z}^r, F$. The cases of $\mathbf{R}^m$ and $\mathbf{Z}^r$ are obvious ($k = 0$), the case of $F$ is clear. For $A = \mathbf{T}^n$ we know $k^0$ is a torus that arises as a direct factor of $A$, so it suffices to separately treat the case $k = k^0$ and $k$ finite. Since $\mathcal{S}(\mathbf{T}^n) = C^{\infty}(\mathbf{T}^n)$ with the topology of uniform convergence in all derivatives, the case of finite $k$ is clear while for the case of $k$ a torus we have $\mathcal{S}(A) = \mathcal{S}(A') \widehat{\otimes}_{\pi} \mathcal{S}(k)$, from which the desired properties are immediate.

Turning to (ii), if we fix an isomorphism $A = \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F$ (so $F$ is the torsion subgroup of the component group of $A$) then the clopen $A'$ contains the identity component $\mathbf{R}^m \times \mathbf{T}^n$ and so is determined by

## PDF page 763

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **763**

its component group $\pi_0(A')$ as a subgroup of $\pi_0(A)$. Letting $F' = \pi_0(A')_{\mathrm{tor}}$, we have $A' \subset \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F'$ inside $A$. The special case $A' = \mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F'$ is immediate from (D.1.3.20) applied to $A$ and $A'$, so we may now assume $F' = F$. More precisely, now $F \subset A'$ inside $A$. Thus, $A'$ is determined by the maximal torsion-free quotient $M$ of $\pi_0(A')$ as a subgroup of the corresponding quotient $\mathbf{Z}^r$ for $A$.

The “elementary divisor” description of $M \subset \mathbf{Z}^r$ allows us to harness the infinite divisibility of $A^0 = \mathbf{R}^m \times \mathbf{T}^n$ to possibly *change* the identification of $A$ with $\mathbf{R}^m \times \mathbf{T}^n \times \mathbf{Z}^r \times F$ (adapted to a preliminary choice of analogous decomposition for $A'$) so that we have $A' = \mathbf{R}^m \times \mathbf{T}^n \times M \times F$ inside $A$ with $M \subset \mathbf{Z}^r$ equal to $\oplus_{i=1}^r (n_i \mathbf{Z})$ for some integers $n_i \ge 0$. The family of seminorms (D.1.3.9) applied to $A$ and $A'$ then yields the result. $\square$

We conclude that the directed system of $\mathcal{S}(k, \Gamma)$'s is *strict* in the sense that its transition maps are topological embeddings. Thus, the collection of all Schwartz-Bruhat functions on $G$ is a $\mathbf{C}$-vector space that we call the *Schwartz-Bruhat space* of $G$ and is made into a locally convex topological vector space via the locally convex inductive limit topology induced by the canonical linear isomorphism

(D.1.5.4)
$$
\mathcal{S}(G) = \operatorname*{\mathrm{colim}}_{(k, \Gamma) \in \mathcal{F}} \mathcal{S}(k, \Gamma)
$$

whose injective transition maps are topological embeddings.

From the construction it is clear that left translation of $G$ on itself carries $\mathcal{S}(G)$ onto itself, but it is less evident (in such generality) that the action map $G \times \mathcal{S}(G) \to \mathcal{S}(G)$ is continuous. Such continuity is proved in Proposition D.1.9.2.

REMARK D.1.5.5. For any Hausdorff locally compact abelian group $G$, define $C^{\infty}(G)$ to be the colimit of the spaces $C^{\infty}(\Gamma/k)$ of smooth functions (similarly to the colimit that defines $\mathcal{S}(G)$). Clearly $\mathcal{S}(G) \subset C^{\infty}(G)$.

Also, every $\chi \in \widehat{G}$ has smooth restriction to $\Gamma$ as a function $\chi : G \to \mathbf{C}^{\times} \subset \mathbf{C}$. Indeed, we can pick an open compactly generated subgroup $U \subset \widehat{G}$ containing $\chi$, so its annihilator $k$ in $G$ is compact by Lemma D.1.4.6(4), hence a good subgroup of $G$, and by design $\chi(k) = 1$. We may and do replace $k$ with $k \cap \Gamma$ so that $k \subset \Gamma$. Then $\chi|_{\Gamma}$ descends to a continuous character of the elementary abelian Lie group $\Gamma/k$. The latter character is smooth, so $\chi|_{\Gamma} \in C^{\infty}(\Gamma)$.

D.1.5.3. *Main Structure Theorems on Schwartz-Bruhat spaces.*

LEMMA D.1.5.6 (Strictness of the inductive system $\{\mathcal{S}(k, \Gamma)\}_{(k, \Gamma)}$). *Let $G$ be a second-countable Hausdorff locally compact abelian group, and $B \subset \mathcal{S}(G)$ a bounded subset.*

(1) *The topology on $\mathcal{S}(G)$ is Hausdorff and for any structural pair $(k, \Gamma)$ of $G$ the locally convex topology induced on $\mathcal{S}(k, \Gamma)$ by $\mathcal{S}(G)$ is the intrinsic locally convex topology of $\mathcal{S}(k, \Gamma) = \mathcal{S}(\Gamma/k)$.*

(2) *There exists a structural pair $(k, \Gamma)$ of $G$ such that $B$ is the image of a bounded subset of $\mathcal{S}(k, \Gamma)$ into $\mathcal{S}(G)$.*

This result holds without second-countability for $G$, but the proof is then more technical (e.g., (2) is proved by building a projector via integration over compact subgroups $k \subset G$) and we do not need it.

PROOF. Since $G$ is second-countable, there is a *countable* cofinal system of structural pairs $(k_n, \Gamma_n)$ and so $\mathcal{S}(G)$ is a “strict inductive limit” of a *sequence* of Hausdorff locally convex spaces $\mathcal{S}(k_n, \Gamma_n)$. But such inductive limits $E = \operatorname{colim} E_n$ always satisfy the two asserted properties: $E$ is Hausdorff with $E_n \to E$ a topological embedding [Scha, Ch. II, 6.4], and every bounded subset of $E$ arises from a bounded subset of some $E_n$ [Scha, Ch. II, 6.5]. $\square$

The following is the main result of this subsection, and a special case of [Bru, §9, Prop. 11]:

THEOREM D.1.5.7 (Main Structure Theorem on Schwartz-Bruhat spaces). *Let $G$ be a second-countable Hausdorff locally compact abelian group. The Hausdorff locally convex $\mathcal{S}(G)$ is barrelled and bornological,*

## PDF page 764

**764** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

*Moreover, both $\mathcal{S}(G)$ and its strong dual $\mathcal{S}(G)'_{\beta}$ are complete, nuclear, and Montel (hence reflexive). In particular, $\mathcal{S}(G)'_{\beta}$ is barrelled.*

PROOF. Since each $\mathcal{S}(k, \Gamma) = \mathcal{S}(\Gamma/k)$ is a Fréchet space by Lemma D.1.3.7, hence each of them is both barrelled and bornological [Scha, Ch. II, Cor. to 7.2, Cor. 1 to 8.2], the countable strict inductive limit $\mathcal{S}(G)$ is also barrelled and bornological by [Scha, Ch. II, Cor. to 7.1, 8.1].

Each $\mathcal{S}(k, \Gamma) = \mathcal{S}(\Gamma/k)$ is complete, nuclear, and Montel by Lemma D.1.3.7(3). These properties then hold for $\mathcal{S}(G)$ since each is inherited under countable strict inductive limits $E = \operatorname{colim} E_n$ of Hausdorff locally convex topological vector spaces: [Scha, Ch. II, 6.6] for completeness, [Scha, Ch. III, Cor. to 7.4] for nuclearity, and [Scha, Ch. IV, 5.8] for the Montel property (to be precise, the latter reference is for inheriting reflexivity, but for the Heine-Borel property of $E = \operatorname{colim} E_n$ we simply observe that a closed bounded subset $K \subset E$ arises from a bounded subset of some $E_n$ that in turn must be closed in $E_n$ since $E_n \to E$ is a topological embedding, so the Heine-Borel property of $E_n$ makes $K$ compact in $E_n$, thus also in $E$).

Turning to the strong dual $\mathcal{S}(G)'_{\beta}$, it inherits the Montel property from that of $\mathcal{S}(G)$ because the strong dual of a Montel space is always Montel [Scha, Ch. IV, 6.1]. For completeness, the strong dual $E'_{\beta}$ of any bornological (Hausdorff locally convex) $E$ is complete by [Scha, Ch. IV, 5.9]. For nuclearity for $\mathcal{S}(G)'_{\beta}$, we first note that since $\mathcal{S}(G)$ is nuclear and complete, the strong dual topology on $\mathcal{S}(G)'$ coincides with the Mackey topology $\tau(\mathcal{S}(G)', \mathcal{S}(G))$ (as for any complete nuclear $E$ [Tre, top of p. 522]). This is useful because the Mackey topology on the topological dual of a countable strict inductive limit $E = \operatorname{colim} E_n$ coincides with the inverse limit $\lim E'_{n, \tau}$ of the topological duals equipped with their Mackey topologies $\tau'_n = \tau(E'_n, E_n)$ [Scha, Ch. IV, Rem. to 4.5]. But with $E_n = \mathcal{S}(\Gamma_n/k_n)$ we likewise have $E'_{n, \tau'_n} = E'_{n, \beta}$, so the known nuclearity of $\mathcal{S}(A)'_{\beta}$ for elementary abelian Lie groups $A$ gives nuclearity for $\mathcal{S}(G)'_{\beta}$ since nuclearity is inherited under inverse limits of Hausdorff locally convex topological vector spaces by [Scha, Ch. III, Cor. to 7.4]. Barrelledness for $\mathcal{S}(G)'_{\beta}$ holds as a general property of reflexive spaces (see [Scha, Ch. IV p. 144]). $\square$

REMARK D.1.5.8. We note that if $G$ is not second-countable then (see [Bru, §9, Prop. 11] $\mathcal{S}(G)$ is still bornological, complete, and Montel but it is *never* nuclear: see the discussion in [Bru, top of p. 54], where the absence of second-countability causes the existence of an uncountable topological direct sum of copies of $\mathbf{C}$ to split off from $\mathcal{S}(G)$ linearly and topologically. That obstructs nuclearity because topological direct summands inherit nuclearity by [Scha, Ch.III, 7.2] but an uncountable direct sum of copies of $\mathbf{C}$ (with its locally convex inductive limit topology) is never nuclear, by [Tre, Thm. 51.2]. The proof of completeness of $\mathcal{S}(G)$ beyond the second-countable case requires some additional work when adapting the proof of completeness of $C^{\infty}_c(G)$ in [Bru, §4, Thm. 1], ultimately resting on Grothendieck's characterization of completeness [Scha, Ch. IV, Cor. 2 to Thm. 6.2].

We record below an important property of the Schwartz-Bruhat space $\mathcal{S}(G)$ of a second-countable Hausdorff locally compact abelian group called *acyclicity* (for which we refer the reader to §C.1.5). This is useful when inductive tensor products of nuclear Fréchet spaces carry linear topological embeddings to linear topological embeddings. This will be used throughout the proof of Theorem D.3.3.7(1).

PROPOSITION D.1.5.9 (Acyclicity of $\mathcal{S}(G)$ - I). *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is second-countable. Then $\mathcal{S}(G)$ is acyclic.*

PROOF. The space $\mathcal{S}(G)$ is a countable strict locally convex inductive limit of nuclear Fréchet spaces, hence complete by [Scha, Ch. II, 6.6]/ But acyclicity and completeness are equivalent for such inductive limits by [Wngr-2, §3, Thm. 3.3, p. 253], which applies because nuclear Fréchet space are always Montel (by [Scha, Ch. IV, 5.6] and [Tre, Cor. 1 to Prop. 50.2]). $\square$

The following Theorem is a consequence of Proposition D.1.5.9:

## PDF page 765

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **765**

THEOREM D.1.5.10 (Acyclicity of $\mathcal{S}(G)$ - II). *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is second-countable, and choose a sequence of structural pairs $(k_m, \Gamma_m)$ for $m\ge 0$ such that the short algebraically exact sequence*

(D.1.5.5)
$$
0\to \bigoplus_{m\ge 0}\mathcal{S}(k_m,\Gamma_m) \xrightarrow{\sigma} \bigoplus_{m\ge 0}\mathcal{S}(k_m,\Gamma_m) \xrightarrow{q} \mathcal{S}(G)\to 0,
$$

*where $\sigma((f_m)_{m\ge 0}):=(f_m-f_{m-1})_{m\ge 0}$ (upon defining $f_{-1}:=0$) and $q$ is the quotient map, is topologically exact; i.e. $\sigma$ is a linear topological embedding with closed range, and $q$ is a quotient map.*

PROOF. The quotient map $q$ is, explicitly, assigned by $q((f_m)_{m\ge 0})=\sum_{m\ge 0}f_m$, noting that for all but finitely many integers $m\ge 0$, we have $f_m=0$, and hence the sum converges in $\mathcal{S}(G)$. The continuity of $q$ and $\sigma$ follows from the universal property of locally convex direct sums, so $\ker(q)$ is closed due to the Hausdorff property of $\mathcal{S}(G)$.

The linear inverse of $\sigma$ is, explicitly:

(D.1.5.6)
$$
\sigma^{-1}((f_m)_{m\ge 0})=(\sum_{0\le j\le m}f_j)_{m\ge 0}.
$$

Indeed, we have $\sigma^{-1}(\sigma((f_m)_{m\ge 0}))=(\sum_{0\le j\le m}(f_j-f_{j-1}))_{m\ge 0}=(f_m)_{m\ge 0}$, following the convention $f_{-1}:=0$. Note that $\sigma^{-1}$ from (D.1.5.6) only makes sense on $\ker(q)$, which ensures that the sums $\sum_{0\le j\le m}f_j$ vanish for all large enough integers $m\ge 0$. The main difficulty is to show $\sigma^{-1}|_{\ker(q)}$ is continuous.

By Proposition D.1.5.9 the strict inductive limit $\mathcal{S}(G)$ is acyclic. Since $\{\mathcal{S}(k_m,\Gamma_m)\}_{m\ge 0}$ is a defining inductive sequence of the topology on $\mathcal{S}(G)$, by [Vogt-1, §1, Cor. 1.3, p. 60], the map $\sigma$ is a linear topological isomorphism onto its range. $\square$

We refer the reader to §C.1.5, for a discussion of acyclicity for locally convex inductive limits of Hausdorff locally convex topological $\mathbf{C}$-vector spaces, with applications to characterizing when a closed subspace $F\subset E=\lim E_n$ is a “limit subspace”: when is the natural continuous linear bijection $\lim(F\cap E_n)\to F$ a homeomorphism?

**D.1.6. Differential operators on Hausdorff locally compact abelian groups.** For $G$ a (real or complex) Lie group, we have the notion of its Lie algebra $\mathfrak{g}$, which, as a linear space is the tangent space at the neutral element of $G$, the Lie group being a differentiable manifold. The Lie algebra can be defined purely topologically. For an arbitrary Hausdorff locally compact abelian group, a Lie “algebra” can be defined as follows:

DEFINITION D.1.6.1. Let $G$ be a topological group. We define the *topological Lie algebra* of $G$ to be the set

(D.1.6.1)
$$
\mathcal{L}(G):=\mathrm{Hom}_{\mathrm{cont}}(\mathbf{R},G)
$$

of one-parameter subgroups of $G$, i.e. of all continuous homomorphisms $\mathbf{R}\to G$, topologized with the compact open topology.

REMARK D.1.6.2. The space $\mathcal{L}(G)$ makes sense for non-commutative $G$ too, and is defined in Definition D.1.6.1 for arbitrary topological groups. In special cases, it carries finer structures that approximate the defining elements of the Lie algebra of a Lie group. In general, we may write

(D.1.6.2)
$$
\exp_G:\mathcal{L}(G)\to G
$$

for the continuous map

(D.1.6.3)
$$
\exp_G(a):=a(1),\, a\in\mathcal{L}(G)
$$

## PDF page 766

**766** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

and refer to it as the *exponential map* of $G$. In favorable situations, it is possible to identify on $\mathcal{L}(G)$ the structure of a Lie algebra and construct on $G$ the structure of a Lie group. For instance, if $G$ admits a continuous faithful finite dimensional complex representation, then $G$ is a Lie group.

REMARK D.1.6.3. For $G$ a Hausdorff locally compact abelian group, $\mathcal{L}(G)$ is a Hausdorff locally convex topological $\mathbf{R}$-vector space. We will never need this, but let us briefly indicate where this topology comes from. A canonical $\mathbf{R}$-vector space structure is defined by pointwise addition and pre-composition with $\mathbf{R}$-scaling on itself. By Pontryagin duality, $G$ is isomorphic as a Hausdorff locally compact abelian group to its own Pontryagin bidual, and so by Lemma D.1.4.7 it admits a neighborhood base at the neutral element comprised of *quasi-convex* subsets: subsets $U\subset G$ such that for every $g\in G$ outside $U$ there exists $\chi\in\widehat{G}$ with $\mathrm{Re}(\chi(u))\ge 0$ for every $u\in U$ and $\mathrm{Re}(\chi(g))<0$ (such $\chi$ is an element of the analog of the polar set of $U$ as defined for subsets of locally convex topological $\mathbf{C}$-vector spaces). Thus, by [Au, Prop. 1.2(ii), (iii)], $\mathcal{L}(G)$ with its $\mathbf{R}$-linear structure is a Hausdorff locally convex $\mathbf{R}$-vector space.

The following description of $\mathcal{L}(G)$ for $G$ a Hausdorff locally compact abelian group is a consequence of Pontryagin duality. We endow

(D.1.6.4)
$$
\mathrm{Hom}_{\mathrm{cont}}(\widehat{G},\widehat{\mathbf{R}})
$$

with the compact-open topology. The topological space $\mathrm{Hom}_{\mathrm{cont}}(\widehat{G},\widehat{\mathbf{R}})$ from (D.1.6.4) is an abelian group upon defining the group operation pointwise.

LEMMA D.1.6.4. *Let $G$ be a Hausdorff locally compact abelian group. Then $\mathrm{Hom}_{\mathrm{cont}}(\widehat{G},\widehat{\mathbf{R}})$ is a Hausdorff locally compact abelian group. The assignment:*

(D.1.6.5)
$$
\Psi:\mathcal{L}(G)\to\mathrm{Hom}_{\mathrm{cont}}(\widehat{G},\widehat{\mathbf{R}})
$$

*defined by $a\mapsto\widehat{a}$ is an isomorphism of Hausdorff locally compact abelian groups.*

PROOF. Pontryagin duality ensures $\Psi$ is bijective, so we just need to check that $\Psi$ and its inverse are continuous. More broadly, for any locally compact abelian $G_1$ and $G_2$, the map $\mathrm{Hom}(G_1,G_2)\to\mathrm{Hom}(\widehat{G_1},\widehat{G_2})$ is checked to be continuous for the compact-open topologies. $\square$

D.1.6.1. *Degree-1 differential operators and differential characterization of smoothness.* We now characterize the notion of smooth complex valued function on a Hausdorff locally compact abelian group $G$. Using the topological Lie algebra $\mathcal{L}(G)$ of a Hausdorff locally compact abelian group, we can define differential operators on $G$. We will then use them to provide a characterization of smoothness, and check that the definition recovers the familiar one when $G$ is of the form $G=\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$, for integers $m,n,r\ge 0$ and a finite group $F$, the definition of which was initiated in Definition 2.1.1.4.

DEFINITION D.1.6.5. Let $G$ be a Hausdorff locally compact abelian group, and $a\in\mathcal{L}(G)$ a one-parameter subgroup. We define the following $\mathbf{C}$-linear map:

(D.1.6.6)
$$
\partial_a:C^1(G)\to C(G)
$$

by the assignment:

(D.1.6.7)
$$
(\partial_af)(g):=\lim_{t\to 0}\frac{f(ga(t))-f(g)}{t}
$$

the limit being formed within $\mathbf{C}$ (we’ll soon see this limit always exists). We refer to $\partial_a$ as the *invariant differential operator* of $a$.

We verify below that $g\mapsto(\partial_af)(g)$, for $f\in C^1(G)$, is defined for all $g$ and continuous over $G$.

## PDF page 767

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **767**

LEMMA D.1.6.6. *Let $G$ be a Hausdorff locally compact abelian group, and $f\in C^1(G)$. Then $\partial_af$ is a continuous function on $G$. Moreover, $\partial_a$ preserves the $\mathbf{C}$-linear subspace $C^{\infty}(G)\subset C^1(G)$ and satisfies*

$$
\partial_a(f_1f_2)=f_1\partial_a(f_2)+f_2\partial_a(f_1).
$$

We call the operators $\partial_a:C^{\infty}(G)\to C^{\infty}(G)$ *first-order differential operators.*

PROOF. Fix $f\in C^1(G)$ and a structural pair $(k,\Gamma)$ of $G$ such that $f$ is supported on $\Gamma$ and is $k$-invariant. Then the unique function $f_0\in C(\Gamma/k)$ such that $f_0\circ r_{(k,\Gamma)}=f$, for $r_{(k,\Gamma)}:\Gamma\to\Gamma/k$ the continuous quotient homomorphism from (D.1.5.2), is $C^1$ on the elementary abelian Lie group $\Gamma/k$ in the sense of Definition D.1.5.3(1). The one-parameter group $a:\mathbf{R}\to G$ has homomorphic image contained in a path-connected subgroup of $G$. In particular, it is contained in every open compactly generated subgroup, hence it lands in $\Gamma$. Thus, we have a one-parameter subgroup $a_0:\mathbf{R}\to\Gamma/k$ by composition with the continuous quotient homomorphism $r_{(k,\Gamma)}$, and by $k$-invariance of $f$ we have $f(ga(t))=f_0(\bar{g}a_0(t))$ where $\bar{g}:=r_{(k,\Gamma)}(g)$. Since $f_0\in C^1(\Gamma/k)$, we can rewrite (D.1.6.7) as

$$
\lim_{t\to 0}\frac{f_0(\bar{g}a_0(t))-f_0(\bar{g})}{t}.
$$

This reduces the claims in the lemma to the case when $G$ is an elementary abelian Lie group, say say isomorphic to $\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$ for integers $m,n,r\ge 0$ and a finite abelian group $F$. The image of $a$ is contained within $\mathbf{R}^m\times\mathbf{T}^n\times\{0\}\times\{0\}$. Since $\mathbf{R}$ and $\mathbf{R}^m\times\mathbf{T}^n$ are Lie groups, $a$ is smooth and $\partial_af$ is the directional derivative of $f$ along the smooth curve $a$. Now all of the assertions can be seen by inspection. $\square$

LEMMA D.1.6.7 (Invariance and commutation of degree-one differential operators). *Let $a,b:\mathbf{R}\rightrightarrows G$ be one-parameter subgroups; i.e., $a,b\in\mathcal{L}(G)$. Then:*

(1) *$\partial_a$ is a $G$-invariant $\mathbf{C}$-linear operator on $C^{\infty}(G)$ that depends $\mathbf{R}$-linearly on $a$, and it restricts to a continuous endomorphism of $\mathcal{S}(G)$.*

(2) *As $\mathbf{C}$-linear operators on $C^{\infty}(G)$, we have $[\partial_a,\partial_b]=0$; i.e., $\partial_a\partial_b=\partial_b\partial_a$.*

PROOF. Pick $f\in C^{\infty}(G)$, so $f\in C^{\infty}(\Gamma/k)$ ffor some compact subgroup $k\subset G$ with open compactly generated orthogonal $k^{\perp}$ and an open compactly generated subgroup $\Gamma\subset G$ containing $k$. In particular, $f$ is $k$-invariant and $\Gamma$ contains the support of $f$.

Since $U:=a(\mathbf{R})\cdot\Gamma\cup b(\mathbf{R})\cdot\Gamma$ is an open subset of $G$ that is a symmetric neighborhood of the neutral element, it generates an open subgroup of $G$ that is also compactly generated (since both $\mathbf{R}$ and $\Gamma$ are so). We may replace $\Gamma$ with this open subgroup so that $a,b$ are valued in $\Gamma$. The direct limit definitions of $C^{\infty}(G)$ and $\mathcal{S}(G)$ as well as of the topology on the latter thereby allows us to rename $\Gamma$ as $G$ to arrange that $G$ is compactly generated. Since $a$ and $b$ take values in the identity component of $G$, we can also assume without loss of generality that $G$ is connected.

It follows that $G/k$ is an abelian Lie group, and by design $f$ arises by pullback from some $f_0\in C^{\infty}(G/k)$. Thus, $\partial_af$ is the pullback of the output of the differential operator $\partial_{\bar{a}}$ on $f_0\in C^{\infty}(G/k)$ where $\bar{a}$ is the composition of $a$ with the quotient homomorphism $G\to G/k$. The same holds for $\partial_bf$ using the composition $\bar{b}$ of $b$ with the quotient homomorphism $G\to G/k$. To check (1) and (2) it now suffices to do so with $G$ replaced by $G/k'$ for each compact subgroup $k'\subset G$ with compactly generated orthogonal $k'^{\perp}$. In other words, we may rename $G/k$ as $G$ to assume that $G$ is a connected abelian Lie group. In this case the assertions are standard. $\square$

D.1.6.2. *General differential operators.* We now discuss general differential operators on Hausdorff locally compact abelian groups.

## PDF page 768

**768** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

DEFINITION D.1.6.8 (Differential operators on Hausdorff locally compact abelian groups). Let $G$ be a Hausdorff locally compact abelian group.

(1) Let $\mathrm{Diff}(G)$ be the commutative $\mathbf{C}$-subalgebra with identity inside $\mathrm{End}_{\mathbf{C}}(C^{\infty}(G))$ generated by the invariant differential operators $\{\partial_a\}_{a\in\mathcal{L}(G)}$. We refer to $\mathrm{Diff}(G)$ as the $\mathbf{C}$-algebra of *invariant differential operators* of $G$. We denote by $\mathrm{Diff}^1(G)$ the $\mathbf{C}$-linear subspace of $\mathrm{Diff}(G)$ generated by the set $\{\partial_a\}_{a\in\mathcal{L}(G)}$. We denote by $\mathrm{Diff}^1_r(G)$ the $\mathbf{R}$-linear subspace $\mathbf{R}$-linearly generated by the same set $\{\partial_a\}_{a\in\mathcal{L}(G)}$.

(2) Let $\mathcal{L}(G)^*$ be the set of (finite) words on the set $\mathcal{L}(G)$. For any $w\in\mathcal{L}(G)^*$, let $D_w\in\mathrm{Diff}(G)$ be the corresponding differential operator (understood to be the identity when $w$ is empty). For any $D\in\mathrm{Diff}(G)$, an identity of the form

(D.1.6.8)
$$
D=\sum_{w\in\mathcal{L}(G)^*}c_wD_w
$$

with $w$ varying over all the words on the elements $\mathcal{L}(G)$, $c_w\in\mathbf{C}$ with $c_w=0$ for all but finitely many $w$, as a *presentation* for $D$.

We define by $\mathcal{P}_D$ the set of all presentations of $D$ in $\mathrm{Diff}(G)$, and we define the *degree* of $D$ to be

(D.1.6.9)
$$
\deg(D):=\inf_{\mathcal{P}_D}\max_{c_w\ne 0}\ell(w)
$$

where $\ell(w)$ is the length of the finite word $w$ on $\mathcal{L}(G)$, the maximum is formed over all the finitely many words $w$ in a given presentation of $D$ whose complex coefficient $c_w$ is nonzero, and the infimum is formed over the set of presentations of $D$ in $\mathrm{Diff}(G)$.

REMARK D.1.6.9. The constants in $\mathrm{Diff}(G)$ have degree 0, and for every nonzero $a\in\mathcal{L}(G)$ we have $\deg(\partial_a)=1$, justifying the notation for $\mathrm{Diff}^1(G)$. Note that the differential operator $D=0$ has degree 0 but the presentation $\partial_a\partial_b-\partial_b\partial_a$ for it leads to the value $\max_{c_w\ne 0}\ell(w)=\max\{\ell(\partial_a\partial_b),\ell(\partial_b\partial_a)\}=2$.

The following is [Wa, §2, Def. 2.4]:

DEFINITION D.1.6.10. Let $G$ be a Hausdorff locally compact abelian group, $D\in\mathrm{Diff}(G)$ an invariant differential operator. We define the function

(D.1.6.10)
$$
p(D):\widehat{G}\to\mathbf{C}
$$

by the assignment

(D.1.6.11)
$$
p(D)(\chi):=(D\chi)(e)
$$

where $e\in G$ is the neutral element. We refer to $p(D)$ as the *polynomial* of $D$, or *symbol* of $D$.

REMARK D.1.6.11. Definition D.1.6.10 is meaningful since continuous characters of a Hausdorff locally compact abelian group are smooth on any open compactly generated subgroup $\Gamma$ by Remark D.1.5.5 and there is an evident restriction map $\mathrm{Diff}(G)\to\mathrm{Diff}(\Gamma)$ via the equality $\mathcal{L}(\Gamma)=\mathcal{L}(G)$ (since $\mathbf{R}$ has no proper open subgroup).

EXAMPLE D.1.6.12. For $G=\mathbf{R}$ we have $\widehat{G}=\{\chi_t=e^{2\pi it(\cdot)}\}_{t\in\mathbf{R}}$, anjd for $D=c\,d/dx$ with $c\in\mathbf{C}$ we have $p(D)(\chi_t)=2\pi ict$. For $G=\mathbf{T}=\mathbf{R}/\mathbf{Z}$ we have $\widehat{G}=\{\chi_m:x\mapsto\mapsto e^{2\pi imx}\}_{m\in\mathbf{Z}}$, and for $D=c\,d/dx$ with $c\in\mathbf{C}$ we have $p(D)(\chi_m)=2\pi icm$.

More broadly, consider $G=\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$ with elements denoted $(x,z,a,b)$ and its dual $\widehat{G}=\mathbf{R}^m\times\mathbf{Z}^r\times\mathbf{T}^r\times\widehat{F}$ with elements denoted $(\widetilde{x},\widetilde{a},\widetilde{z},\widetilde{b})$. A general 1-parameter subgroup $\lambda:\mathbf{R}\to\widehat{G}$ has the form $t\mapsto(t\widetilde{c},0,t\widetilde{c}'\bmod\mathbf{Z}^r,0)$ for unique $\widetilde{c}\in\mathbf{R}^m$, $\widetilde{c}'\in\mathbf{R}^r$, and when $G$ is viewed as the dual of $\widehat{G}$ the character $\chi_{(x,z,a,b)}:\widehat{G}\to\mathrm{U}(1)$ associated to $(x,z,a,b)\in G$ is

$$
(\widetilde{x},\widetilde{a},\widetilde{z},\widetilde{b})\mapsto e^{2\pi x\cdot\widetilde{x}}e^{2\pi iz\cdot\widetilde{a}}\,\widetilde{z}^a\,\widetilde{b}(b)
$$

## PDF page 769

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **769**

(using the standard dot products on $\mathbf{R}^m$ and $\mathbf{R}^r$).

The operator $\partial_{\lambda}$ is $\widetilde{c}\cdot\partial_{\widetilde{x}}+\widetilde{c}'\cdot\partial_{\widetilde{z}}$, so it is readily computed that

(D.1.6.12)
$$
p(\partial_{\lambda})(\chi_{(x,z,a,b)})=2\pi i(x\cdot\widetilde{c}+a\cdot\widetilde{c}').
$$

We will see in Lemma D.1.6.19(1) with the aid of Fourier transform that for every open compactly generated subgroup $\Gamma'\subset\widehat{G}$, the restriction of $p(D):\widehat{G}\to\mathbf{C}$ to $\Gamma'$ belongs to $C^{\infty}(\Gamma')$. In particular, $p(D)$ is continuous.

LEMMA D.1.6.13. *Let $G$ be a Hausdorff locally compact abelian group. For $\chi\in\widehat{G}$ and $a_1,\dots,a_n\in\mathcal{L}(G)$,*

$$
\partial_{a_n}\cdots\partial_{a_1}(\chi)=\left(\prod p(\partial_{a_i})(\chi)\right)\chi
$$

*as functions $G\to\mathbf{C}$ (equivalently, $(\partial_{a_n}\cdots\partial_{a_1}(\chi))\chi^{-1}$ is a constant function on $G$). In particular,*

(D.1.6.13)
$$
p(\partial_{a_n}\cdots\partial_{a_1})(\chi)=\prod p(\partial_{a_i})(\chi).
$$

*Moreover, for every compact subgroup $k'\subset\widehat{G}$ and $D\in\mathrm{Diff}(G)$, the function $p(D):\widehat{G}\to\mathbf{C}$ is $k'$-invariant.*

PROOF. The identity (D.1.6.13) follows from the first asserted identity by evaluating at $e\in G$. To prove the first assertion, by induction it suffices to treat the case $n=1$: $\partial_a(\chi)=c_a\chi$ as functions for some $c_a\in\mathbf{C}$ (and then $c_a=p(\partial_a)(\chi)$ by evaluating at the identity). From the definition of $\partial_a$,

$$
(\partial_a(\chi))(g)=\lim_{t\to 0}\frac{\chi(ga(t))-\chi(g)}{t}=\left(\lim_{t\to 0}\frac{\chi(a(t))-1}{t}\right)\chi(g).
$$

Thus, setting $c_a$ to be the final limit expression does the job.

For $k'$-invariance of $p(D)$, by $\mathbf{C}$-linearity in $D$ (and the fact that invariance is obvious for constant operators), it suffices to treat the case $D=\partial_{a_n}\cdots\partial_{a_1}$. for some $n\ge 1$. By (D.1.6.13) it further suffices to treat the case $n=1$: to show $p(\partial_a)(\chi\psi)=p(\partial_a)(\chi)$ for $\psi$ in a compact subgroup of $\widehat{G}$. The Leibniz rule gives $p(\partial_a)(\chi\psi)=p(\partial_a)(\chi)+p(\partial_a)(\psi)$, so we just want $p(\partial_a)$ to vanish on all compact subgroups $k'\subset\widehat{G}$. Such subgroups are precisely $\widehat{G/U}$ for an open subgroup $U\subset G$. But the characters $\chi\in\widehat{G/U}$ are exactly $U$-invariant characters on $G$, and any character of the latter type is constant near $e\in G$ (namely equal to 1), so applying $D$ kills it near $e$. $\square$

LEMMA D.1.6.14. *Let $G$ be a Hausdorff locally compact abelian group. Define the assignment:*

(D.1.6.14)
$$
\sigma:\mathrm{Diff}^1_r(G)=\{\partial_a\}_{a\in\mathcal{L}(G)}\to\mathrm{Hom}_{\mathrm{cont}}(\widehat{G},\mathbf{R})
$$

*by setting $\sigma(\partial_a):\widehat{G}\to\mathbf{R}$ to be the continuous homomorphism satisfying*

$$
\exp(2\pi i(\sigma(\partial_a)(\chi))t)=\langle a(t),\chi\rangle_{G,\widehat{G}}
$$

*as functions of $t\in\mathbf{R}$.*

*This map $\sigma$ is an $\mathbf{R}$-linear isomorphism, upon endowing the target with the pointwise $\mathbf{R}$-linear structure. The following diagram:*

(D.1.6.15)

```latex
\begin{tikzcd}
\mathcal{L}(G) \arrow[r, "\Psi"] \arrow[d, "a\mapsto\partial_a"'] & \mathrm{Hom}_{\mathrm{cont}}(\widehat{G},\widehat{\mathbf{R}}) \\
\mathrm{Diff}^1_r(G) \arrow[r, "\sigma"'] & \mathrm{Hom}_{\mathrm{cont}}(\widehat{G},\mathbf{R}) \arrow[u, "\simeq"']
\end{tikzcd}
```

*commutes, where the rightmost vertical arrow is induced by the isomorphism $\mathbf{R}\simeq\widehat{\mathbf{R}}$ defined by $t\mapsto e^{2\pi it(\cdot)}$.*

## PDF page 770

**770** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

PROOF. The top side of the diagram is a bijective homomorphism by Lemma D.1.6.4, and it is $\mathbf{R}$-linear by design. The right side is also an $\mathbf{R}$-linear isomorphism by design, and the left side is an $\mathbf{R}$-linear isomorphism by Lemma D.1.6.7(1). Thus, the bottom is an $\mathbf{R}$-linear isomorphism once it is shown that the diagram commutes. We now focus on the commutativity.

The map $t\mapsto\langle a(t),\chi\rangle_{G,\widehat{G}}=\chi(a(t))$ is a continuous character of $\mathbf{R}$. There therefore exists a unique $\lambda_{a,\chi}\in\mathbf{R}$ such that $\langle a(t),\chi\rangle_{G,\widehat{G}}=\exp(2\pi i\lambda_{a,\chi}t)$ as continuous functions of $t\in\mathbf{R}$. Formation of $\lambda_{a,\chi}$ is readily checked to be continuous in $(a,\chi)$ with respect to the compact-open topology on $\mathcal{L}(G)$ and the compact-open topology on $\widehat{G}$. The assignment $a\mapsto(\chi\mapsto\lambda_{a,\chi})$ is the composition of the top horizontal and (inverse of the) rightmost vertical arrows in (D.1.6.15).

The equation

(D.1.6.16)
$$
\langle a(t),\chi\rangle_{G,\widehat{G}}=\exp(2\pi i(\sigma(\partial_a)(\chi))t)
$$

determines the one-parameter subgroup $a:\mathbf{R}\to G$ uniquely by Theorem D.1.1.1(2). It follows that we have

$$
\lambda_{a,\chi}=\sigma(\partial_a)(\chi)
$$

for all $\chi\in\widehat{G}$, and hence $a\mapsto(\chi\mapsto\lambda_{a,\chi})$ (which, recall, equals the composition of going across the top and right side of the diagram (D.1.6.15)) agrees with $a\mapsto(\chi\mapsto\sigma(\partial_a)(\chi))$ that is the composition along the left and bottom sides of (D.1.6.15). Thus, the diagram commutes. $\square$

COROLLARY D.1.6.15 (Values of the polynomials of degree-1 differential operators). *Let $G$ be a Hausdorff locally compact abelian group, $a\in\mathcal{L}(G)$ a 1-parameter subgroup. Then:*

(D.1.6.17)
$$
p(\partial_a)=2\pi i\sigma(\partial_a)
$$

*as functions $\widehat{G}\to\mathbf{C}$. In particular, $p(\partial_a)$ takes values within $\mathbf{R}(1)$.*

PROOF. In the proof of Lemma D.1.6.13 we saw

$$
p(\partial_a)(\chi)=\lim_{t\to 0}\frac{\chi(a(t))-1}{t},
$$

which is the derivative at $t=0$ of $\chi(a(t))=\exp(2\pi i(\sigma(\partial_a))(\chi)t)$ (equality by (D.1.6.16)). This derivative value is clearly $2\pi i(\sigma(\partial_a))(\chi)$. $\square$

We conclude with a “coordinate-free” characterization of smooth functions on an elementary abelian Lie group $G$ that are of rapid decay at infinity.

LEMMA D.1.6.16. *Let $G$ be an elementary abelian Lie group, $f:G\to\mathbf{C}$ a smooth function on $G$. The following conditions on $f$ are equivalent:*

(1) *$f$ is a Schwartz-Bruhat function.*

(2) *For every pair $(D_1,D_2)\in\mathrm{Diff}(G)\times\mathrm{Diff}(\widehat{G})$, the product function $p(D_2)\cdot D_1(f)$ on $G$ is continuous and globally bounded (with the bound depending on $D_1$ and $D_2$).*

REMARK D.1.6.17. Since $D_2\in\mathrm{Diff}(\widehat{G})$, we use the natural isomorphism $G\simeq\widehat{\widehat{G}}$ to view $p(D_2)$ as a function on $G$.

PROOF. Consider $f\in C^{\infty}(G)$. There exists a structural pair $(k,\Gamma)$ of $G$ such that $f$ is supported on $\Gamma$ and the unique $f_0\in C^{\infty}(\Gamma/k)$ such that $f_0\circ r_{(k,\Gamma)}=f$ (with $r_{(k,\Gamma)}:\Gamma\to\Gamma/k$ the continuous quotient homomorphism of (D.1.5.2)), with $\Gamma/k$ an elementary abelian Lie group. (as $\Gamma/k$ is an elementary abelian Lie group; see also Lemma D.1.3.3). Clearly $D_1(f)$ is supported on $\Gamma$, and it is $k$-invariant since $D_1$ is built from invariant first-order differential operators. Thus, $D_1(f)$ arises from a function on $\Gamma/k$. The same then holds for $p(D_2)\cdot D_1(f)$ since this product is certainly supported in $\Gamma$ and $p(D_2)$ is $k$-invariant by the last assertion in Lemma D.1.6.13. Hence, we can rename $\Gamma/k$ as $G$ and assume $G=\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$ for integers

## PDF page 771

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **771**

$m,n,r\ge 0$ and a finite abelian group $F$. Any one-parameter subgroup $a:\mathbf{R}\to G$ has image contained in $\mathbf{R}^m\times\mathbf{T}^n\times\{0\}\times\{0\}$ by connectedness.

By $\mathbf{C}$-bilinearity in $D_1$ and $D_2$, we may focus on $D_1$ and $D_2$ that are each products of finitely many $\partial_a$’s for 1-parameter subgroups $a$ of $G$ and $\widehat{G}$ respectively. As a warm-up, let’s consider the case $D_1=\partial_{a_1}$ and $D_2=\partial_{a_2}$, with $a_1\in\mathcal{L}(G)$ and $a_2\in\mathcal{L}(\widehat{G})$. Viewing $\mathbf{T}$ as $\mathbf{R}/\mathbf{Z}$, we have $a_1(t)=(tc,tc'\bmod\mathbf{Z},0,0)$ for some unique $c\in\mathbf{R}^m$ and $c'\in\mathbf{R}^n$. Using the analogous description $\widehat{G}=\mathbf{R}^m\times\mathbf{Z}^n\times\mathbf{T}^r\times\widehat{F}$ (with elements denoted $(\widetilde{x},\widetilde{a},\widetilde{z},\widetilde{b})$), we likewise have $a_2(t)=(te,0,td,0)$ for unique $e\in\mathbf{R}^m$ and $d\in\mathbf{R}^r$. Then

(D.1.6.18)
$$
(p(\partial_{a_2})\cdot\partial_{a_1}f)(x,z,a,b)=p(\partial_{a_2})(x,z,a,b)\cdot\left(\sum_{j=1}^m c_j\,\partial_{x_j}f(x,z,a,b)+\sum_{\ell=1}^n c'_{\ell}\,\partial_{z_{\ell}}f(x,z,a,b)\right)
$$

where $p(\partial_{a_2})(x,z,a,b)=2\pi i(x\cdot e+a\cdot d)$ by (D.1.6.12). Thus, the right side of (D.1.6.18) equals

(D.1.6.19)
$$
2\pi i\sum_{j=1}^m(x\cdot e+a\cdot d)c_j\,\partial_{x_j}f(x,z,a,b)+2\pi i\sum_{\ell=1}^n(x\cdot e+a\cdot d)c'_{\ell}\,\partial_{z_{\ell}}f(x,z,a,b)
$$

for $e\in\mathbf{R}^m$, $d\in\mathbf{R}^r$ encoding $a_2$ and $c\in\mathbf{R}^m$, $c'\in\mathbf{R}^n$ encoding $a_1$.

In general, as we let $D_2$ vary through all non-empty products of finitely many $\partial_a$’s with $a$ varying through the 1-parameter subgroups of $\widehat{G}$ we see that $p(D_2):G\to\mathbf{C}$ varies through all products of linear forms in $(x,a)$; the empty product (corresponding to the constant operator $D_2=1$) has $p(D_2)=1$. Likewise, as we let $D_1$ vary through all such non-empty products with 1-parameter subgroups of $G$ clearly $D_1(f)$ varies through the output of $f$ when hit by all products of finitely many first-order linear differential operators in the $\partial_{x_j}$’s and $\partial_{z_{\ell}}$’s (and $D_1(f)=f$ for the empty product corresponding to $D_1=1$). The boundedness condition in (2) thereby expresses *exactly* the finiteness on $f$ for all seminorms in (D.1.3.9), and that condition defines $\mathcal{S}(G)$ as a subspace of $C^{\infty}(G)$ by Lemma D.1.3.4. $\square$

D.1.6.3. *Differential operators, symbols and the Fourier transform.* We conclude this review on the Schwartz-Bruhat space of a Hausdorff locally compact abelian group $G$, with a fundamental property of the Fourier transform $\mathcal{F}_G:L^1(G,\mu_G)\to C_0(G)$, where $\mu_G$ is a fixed choice of Haar measure on $G$, uniquely determining a dual Haar measure $\mu_{\widehat{G}}$ on $\widehat{G}$ (see Lemma D.1.1.2).

For a structural pair $(k,\Gamma)$ of $G$, we choose the volume-1 Haar measure on $k$ and denote it $\mu_k$, and together with the restriction $\mu_G$ to the open subgroup $\Gamma\subset G$ this uniquely determines a Haar measure $\mu_{\Gamma/k}$ on the elementary abelian Lie group $\Gamma/k$ by Theorem D.1.2.1. Likewise, the measures $\mu_G$ and $\mu_k$ determine a Haar measure $\mu_{G/k}$ on $G/k$. By Lemma D.1.1.2 we likewise get the Plancherel measures $\mu_{\widehat{G}}$ on $\widehat{G}$, $\mu_{\widehat{\Gamma/k}}$ on $\widehat{\Gamma/k}=k^{\perp}/\Gamma^{\perp}$, and $\mu_{k^{\perp}}$ on $k^{\perp}=\widehat{G/k}$. Then $\mu_{\widehat{\Gamma/k}}$ and $\mu_{k^{\perp}}$ determine a Haar measure $\mu_{\Gamma^{\perp}}$ on the compact subgroup $\Gamma^{\perp}\subset\widehat{G}$.$^3$

We use $\mu_k$ to define the continuous linear map $\pi_{(k,\Gamma)}:\mathcal{S}(G)\to\mathcal{S}(k,\Gamma)=\mathcal{S}(\Gamma/k)$ assigned by

(D.1.6.20)
$$
\pi_{(k,\Gamma)}(f)(x):=\int_k f(gx)\,\mathrm{d}\mu_k(g),\, x\in\Gamma
$$

on each $f\in\mathcal{S}(G)$. To check that this output really lies in $\mathcal{S}(\Gamma/k)$ and that the linear map is continuous, the inductive limit process defining the topology of $\mathcal{S}(G)$ reduces us to checking:

$^3$There are a variety of things to clarify that I am sure are implicit later: is $\mu_{k^{\perp}}$ the restriction of $\mu_{\widehat{G}}$ to the open subgroup $k^{\perp}$? Is $\mu_{k^{\perp}}$ the one determined just from $\mu_G$ and $\mu_k$ without mention of $\Gamma$ at all? Is $\mu_{\Gamma^{\perp}}$ the volume-1 measure? Can any of these be seen directly without much headache?

## PDF page 772

**772** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

LEMMA D.1.6.18. *If $A$ is an elementary abelian group and $k$ is a compact subgroup equipped with its volume-1 measure $\mu_k$ then for $f\in\mathcal{S}(A)$ the $k$-invariant function $x\mapsto\int_k f(xg)\,\mathrm{d}\mu_k(g)$ lies in $\mathcal{S}(A/k)$. Moreover, this map $\pi:\mathcal{S}(A)\to\mathcal{S}(A/k)$ is continuous and surjective.*

PROOF. Averaging over $k$ (say on continuous functions) is the composite of the analogous averaging over $k^0$ followed by averaging over $k/k^0$, so it suffices to separately treat the cases when $k$ is connected and when $k$ is finite.

First we treat finite $k$. In this case the $k$-averaging involves only finite sums and so the output of such averaging is seen to be valued in $\mathcal{S}(A)^k$ and continuous as an $\mathcal{S}(A)$-valued operation. We then just need to show the inclusion $\mathcal{S}(A/k)\to\mathcal{S}(A)^k$ is an equality and the resulting map $\pi:\mathcal{S}(A)\to\mathcal{S}(A/k)$ is continuous. Fix an identification

(D.1.6.21)
$$
A=\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F
$$

for finite $F$. Letting $F'\subset F$ be the image of $k$ under $A\to(A/A^0)_{\mathrm{tor}}=F$, it suffices to separately treat the cases $F'=0$ and $k\simeq F'$. In the latter case the containment $k\subset\mathbf{T}^n\times F$ and the infinite divisibility of $\mathbf{T}$ allows us to use compatible decompositions of $k\simeq F'$ and $F$ as products of cyclic groups to possibly *change* the identification (D.1.6.21) to arrange that $k\subset F$ as subgroups of $A$. Then we have compatible linear topological descriptions

$$
\mathcal{S}(A)=\mathcal{S}(\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r)\otimes\mathbf{C}^F,\, \mathcal{S}(A/k)=\mathcal{S}(\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r)\otimes\mathbf{C}^{F/k}
$$

from which all is clear.

Now assume $F'=0$, so $k\subset\mathbf{T}^n$ inside $A$ and hence (D.1.3.20) provides compatible identifications

$$
\mathcal{S}(A)=\mathcal{S}(\mathbf{R}^m\times\mathbf{Z}^r)\widehat{\otimes}_{\pi}\mathcal{S}(\mathbf{T}^n)\otimes\mathbf{C}^F,\, \mathcal{S}(A/k)=\mathcal{S}(\mathbf{R}^m\times\mathbf{Z}^r)\widehat{\otimes}_{\pi}\mathcal{S}(\mathbf{T}^n/k)\otimes\mathbf{C}^F
$$

(with $\mathbf{T}^n/k$ also a torus). We thereby reduce to the case $F=0$. Since the finite $k$ is contained in $\mathbf{T}^n$, via any of the families of seminorms in Lemma D.1.3.4 the $k$-action on $\mathcal{S}(A)$ is seen to be continuous and so the completed tensor product descriptions of $\mathcal{S}(A)$ and $\mathcal{S}(A/k)$ reduce checking $\mathcal{S}(A/k)=\mathcal{S}(A)^k$ to the special case $A=\mathbf{T}^n$ that is clear (since $\mathcal{S}(T)=C^{\infty}(T)$ for any torus $T$). The continuity of $\mathcal{S}(A)\to\mathcal{S}(A/k)$ is seen by using the family of seminorms (D.1.3.10) applied to $A$ and $A/k$ (via the compatible product decompositions of these groups as above and any choice of isomorphism $\mathbf{T}^n/k\simeq\mathbf{T}^n$).

It remains to treat $k$ connected, so $k$ is a torus and therefore contained in the unique maximal torus $\mathbf{T}^n\subset A$. Since any containment of tori splits as a topological group factor, we can choose (D.1.6.21) so that $k$ is a product of some of the $\mathbf{T}$-factors. In particular, $A=A'\times k$ for an elementary abelian Lie group $A'$. For the special case $A=k$, this $k$-averaging construction $\int_k:\mathcal{S}(k)\to\mathbf{C}$ is readily seen to be continuous. In general, by (D.1.3.20) we have naturally $\mathcal{S}(A')\widehat{\otimes}_{\pi}\mathcal{S}(k)\simeq\mathcal{S}(A)$. By Grothendieck’s explicit description of elements of completed projective tensor products of Fréchet spaces [Scha, Ch. III, 6.4], everything in this completed tensor product can be written in the form

$$
\sum_{n\ge 1}\lambda_n(f_n\otimes F_n)
$$

for an absolutely summable sequence $(\lambda_n)$ in $\mathbf{C}$ and sequences $(f_n)\subset\mathcal{S}(A')$ and $(F_n)\subset\mathcal{S}(k)$ that converge to 0. In particular, a general $f\in\mathcal{S}(A)$ can be written pointwise as an absolutely summable series

$$
f(a',g)=\sum_{n\ge 1}\lambda_n f_n(a')F_n(g)
$$

for $(a',g)\in A'\times k=A$; note that the $f_n$’s and $F_n$’s are respectively uniformly bounded on $A'$ and $k$ respectively.

## PDF page 773

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **773**

Thus, for $x_0=(a'_0,g_0)\in A$ we have

$$
\int_k f(x_0g)\,\mathrm{d}\mu_k(g)=\sum_{n\ge 1}\lambda_n f_n(a'_0)\int_k F_n(g_0g)\,\mathrm{d}\mu_k(g)=\sum_{n\ge 1}\lambda_n f_n(a'_0)\int_k F_n\,\mathrm{d}\mu_k.
$$

In other words,

$$
\int_k f((a',g')g)\,\mathrm{d}\mu_k(g)=\sum_{n\ge 1}\lambda_n f_n(a')\int_k F_n\,\mathrm{d}\mu_k
$$

for all $(a',g')\in A'\times k=A$. Since the $F_n$’s are uniformly bounded and $f_n\to 0$ in $\mathcal{S}(A')$, the series

$$
\sum_{n\ge 1}\lambda_n f_n\int_k F_n\,\mathrm{d}\mu_k
$$

has Cauchy partial sums in $\mathcal{S}(A')=\mathcal{S}(A/k)$ and so converges in $\mathcal{S}(A/k)$ by completeness. This proves $k$-averaging is valued in $\mathcal{S}(A/k)$ and agrees with the visibly continuous linear $\mathrm{id}\widehat{\otimes}_{\pi}\int_k:\mathcal{S}(A')\widehat{\otimes}_{\pi}\mathcal{S}(k)\to\mathcal{S}(A')$. $\square$

Since $\mu_k(k)=1$, it is clear that $\pi_{(k,\Gamma)}:\mathcal{S}(G)\to\mathcal{S}(k,\Gamma)=\mathcal{S}(\Gamma/k)$ is also a projector. We likewise use $\mu_{\Gamma^{\perp}}$ to define the continuous linear map $\pi_{(\Gamma^{\perp},k^{\perp})}:\mathcal{S}(\widehat{G})\to\mathcal{S}(\Gamma^{\perp},k^{\perp})=\mathcal{S}(k^{\perp}/\Gamma^{\perp})$ by

(D.1.6.22)
$$
\pi_{(\Gamma^{\perp},k^{\perp})}(f)(x):=\int_{\Gamma^{\perp}}f(gx)\,\mathrm{d}\mu_{\Gamma^{\perp}}(g),\, x\in k^{\perp}
$$

on each $f\in\mathcal{S}(\widehat{G})$. That $\pi_{(\Gamma^{\perp},k^{\perp})}$ is also a projector amounts to checking $\mu_{\Gamma^{\perp}}(\Gamma^{\perp})=1$, but rather than carry out such a direct verification (which seems a bit complicated)$^4$ we get it immediately from the projector property for $\pi_{(k,\Gamma)}$ via Lemma D.1.6.19(2, 3) below, with that part (3) a consequence of the Poisson Summation Formula (see Theorem D.1.2.7 or [DE, Thm. 3.6.3]).

LEMMA D.1.6.19 (Fourier transform and differential operators on Schwartz-Bruhat spacees). *Let $G$ be a Hausdorff locally compact abelian group, and $(k,\Gamma)$ a structural pair of $G$. Let $\mu_G$ be a fixed choice of Haar measure on $G$, and $\mu_{\widehat{G}}$ the Plancherel measure on $\widehat{G}$ determined by $\mu_G$.*

(1) *For any invariant differential operator $D$ on $G$,*

(D.1.6.23)
$$
\mathcal{F}_G(Df)=p(D)\cdot\widehat{f}
$$

*for every $f\in\mathcal{S}(G)$; i.e., as functions of $\chi\in\widehat{G}$, we have*

(D.1.6.24)
$$
\widehat{Df}(\chi)=p(D)(\chi)\cdot\widehat{f}(\chi).
$$

(2) *The linear map $\mathcal{F}_G:\mathcal{S}(G)\to C_0(\widehat{G})$ is valued in $\mathcal{S}(\widehat{G})$ and continuous with respect to the locally convex topologies on $\mathcal{S}(G)$ and $\mathcal{S}(\widehat{G})$. As such, it is a linear topological isomorphism.*

(3) *The Fourier transform $\mathcal{F}$ interacts with the projectors $\pi_{(k,\Gamma)}$ and $\pi_{(\Gamma^{\perp},k^{\perp})}$ according to the following identity:*

(D.1.6.25)
$$
\mathcal{F}_G\circ\pi_{(k,\Gamma)}(f)=\int_{k^{\perp}}\widehat{f}(\chi)\,\chi\,\mathrm{d}\mu_{k^{\perp}}(\chi)
$$

*where $\mu_{k^{\perp}}$ is the Plancherel measure on $k^{\perp}$ uniquely determined by $\mu_{\Gamma/k}$ and $\mu_G$. In particular, we have*

(D.1.6.26)
$$
\mathcal{F}_G\circ\pi_{(k,\Gamma)}(f)=\pi_{(\Gamma^{\perp},k^{\perp})}\circ\mathcal{F}_{\widehat{G}}
$$

*intertwining $\mathcal{S}(k,\Gamma)$ and $\mathcal{S}(\Gamma^{\perp},k^{\perp})$.*

PROOF. (1) : This is a consequence of (1) in the proof of [Wa, Thm. 3.2] together with the calculations for (2) and (3) on [Wa, p. 313]. We record the calculation, because our convention in (D.1.1.4) to define the Fourier transform incorporate conjugation on the character, contrary to the definition in loc.cit.

$^4$I am skeptical the proof of the Lemma below invoked here really does not require knowing this volume-1 property in the details, in which case volume-1 should be proved directly.

## PDF page 774

**774** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

First we treat the special case $D=\partial_a$ for a 1-parameter subgroup $a:\mathbf{R}\to G$:

$$
\begin{aligned}
\mathcal{F}_G(\partial_af)(\chi) &= \int_G\lim_{t\to 0}\frac{f(ga(t))-f(g)}{t}\overline{\chi(g)}\,\mathrm{d}\mu_G(g)\\
&= \lim_{t\to 0}\left\{\int_G\frac{f(ga(t)^{-1}a(t))}{t}\overline{\chi(ga(t)^{-1})}\,\mathrm{d}\mu_G(ga(t)^{-1})-\int_G\frac{f(g)}{t}\overline{\chi}(g)\,\mathrm{d}\mu_G(g)\right\}\\
&= \lim_{t\to 0}\left\{\frac{\chi(a(t))}{t}\int_G f(g)\overline{\chi}(g)\,\mathrm{d}\mu_G(g)-\frac{1}{t}\int_G f(g)\overline{\chi}(g)\,\mathrm{d}\mu_G(g)\right\}\\
&= \lim_{t\to 0}\left\{\frac{\chi(a(t))-1}{t}\right\}\int_G f(g)\overline{\chi(g)}\,\mathrm{d}\mu_G(g)\\
&= p_{\partial_a}(\chi)\,\widehat{f}(\chi)
\end{aligned}
$$

where the exchange of the order of integration and formation of the limit is legitimate by Lebesgue’s Dominated Convergence, because $\chi^{-1}$ is bounded over $G$ and the family of Schwatz functions $g\mapsto\frac{f(ga(t))-f(g)}{t}$ on $G$ for $t\ne 0$ that converges pointwise to $\partial_af$ on $G$ as $t\to 0$ also converges to it in $L^1(G,\mu_G)$ as $t\to 0$.

To see the $L^1$-convergence, we shall use the group-theoretic analogue of Hadamard’s Lemma:

$$
\frac{f(ga(t))-f(g)}{t}=\int_0^1(\partial_af)(ga(tu))\,\mathrm{d}u.
$$

The right side as a function of $g$ for each $t\ne 0$ converges to $\partial_af$ in $L^1(G,\mu_G)$ as $t\to 0$, due to Fubini’s Theorem and the Dominated Convergence Theorem on $G\times[0,1]$ (as $(\partial_af)(ga(v))-(\partial_af)(g)\in L^1(G\times[0,1])$ by translation-invariance of $\mu_G$). As usual, really one works with arbitrary sequences $t_n\to 0$ to infer the conclusion for general $t\to 0$.

For general $D$, linearity reduces us to the special case that $D$ is a product of $\partial_{a_i}$’s for finitely many $a_1,\dots,a_n\in\mathcal{L}(G)$. The multiplicativity in (D.1.6.13) allows us to carry out induction on $n$ (the base case $n=1$ being settled above).

(2) : To check $\mathcal{F}_G(f)$ is Schwartz on $\widehat{G}$ for $f\in\mathcal{S}(G)$, the key point is to reduce to elementary abelian Lie groups. Pick a structural pair $(k,\Gamma)$ so that $f\in\mathcal{S}(k,\Gamma)$. The continuous $\widehat{f}$ is supported on $k^{\perp}$ and $\Gamma^{\perp}$-invariant by Lemma D.1.5.2(3). Strictly speaking, that result assumes $\widehat{f}\in L^1(\widehat{G})$ which we don’t yet know, but the required parts of the proof never use that hypothesis: $\widehat{f}$ is supported in $k^{\perp}$ because in the proof of Lemma D.1.5.2(3) the argument to show $\widehat{f}$ is supported in $H^{\perp}$ when $f$ is $H$-invariant for a closed subgroup $H\subset G$ only requires an $L^1$-condition on $f$ (in particular, pointwise Fourier inversion is not used). Likewise the $\Gamma^{\perp}$-invariance for $\widehat{f}$ can be shown by adapting a calculation from that earlier proof: if $\chi_0\in\Gamma^{\perp}$ then since $f$ is supported on the open subgroup $\Gamma$ we have

$$
\widehat{f}(\chi_0\chi)=\int_G f(g)\overline{\chi_0\chi}(g)\,\mathrm{d}\mu_G(g)=\int_{\Gamma}f(\gamma)\overline{\chi_0\chi}(g)\,\mathrm{d}\mu_G(\gamma)=\int_{\Gamma}f(\gamma)\overline{\chi}(g)\,\mathrm{d}\mu_G(\gamma)
$$

since $\chi_0(\gamma)=1$ (as $\chi_0\in\Gamma^{\perp}$). The calculation then runs in reverse to recover $\widehat{f}(\chi)$ as desired.

Thus, $\widehat{f}$ arises from a continuous function on $k^{\perp}/\Gamma^{\perp}$. As such, we claim $\widehat{f}$ viewed on $k^{\perp}/\Gamma^{\perp}=\widehat{\Gamma/k}$ is exactly $\mathcal{F}_{\Gamma/k}(f_0)$ for the continuous $L^1$-function $f_0$ on $\Gamma/k$ arising from $f$.$^5$ Thus, to prove $\widehat{f}\in\mathcal{S}(\widehat{G})$ it suffices to show $\widehat{f}_0\in\mathcal{S}(\widehat{\Gamma/k})$. Once this is proved, the resulting linear map $\mathcal{F}_G:\mathcal{S}(G)\to\mathcal{S}(\widehat{G})$ is the direct limit of Fourier transforms at the $(k,\Gamma)$-levels,$^6$ so the topological isomorphism property for $\mathcal{F}_G$ between Schwartz spaces reduces to the case of elementary abelian Lie groups.

So now $G=\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$. Differentiation under the integral sign, combined with the assumed Schwartz-Bruhat property of $f$ and the explicit description $\widehat{G}=\mathbf{R}^m\times\mathbf{Z}^n\times\mathbf{T}^r\times\widehat{F}$, shows $\widehat{f}$ is smooth. The

$^5$I am sure proving this requires clearing up the questions on measures posed in a prior footnote. Being off by a scalar will be harmless for this.

$^6$Up to some nonzero scalar depending on the level? Harmless if so.

## PDF page 775

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **775**

calculation even shows that all $\partial_{x_j}(\widehat{f})$’s and $\partial_{z_{\ell}}(\widehat{f})$’s are themselves Fourier transforms of Schwartz-Bruhat functions, and we can keep iterating. Thus, to verify the characterization in Lemma D.1.6.16 of the Schwartz-Bruhat property for smooth functions in the case of the smooth $\widehat{f}$ for general $f\in\mathcal{S}(G)$ it suffices to check that $p(D)\,\widehat{f}$ is bounded on $\widehat{G}$ for all $D\in\mathrm{Diff}(G)$. But this is immediate from (1) since $\mathcal{F}_G(Df)\in C_0(\widehat{G})$.

It remains to show the resulting linear map $\mathcal{F}_G:\mathcal{S}(G)\to\mathcal{S}(\widehat{G})$ is a topological isomorphism. But since $f$ and $\widehat{f}$ are now known to always be $L^1$ for $f\in\mathcal{S}(G)$, Fourier inversion holds pointwise in both directlons by Lemma D.1.1.2(5). Hence, as long as $\mathcal{F}_G$ is shown to be continuous for general elementary abelian Lie groups $G$ we can apply that to $\widehat{G}$ to get continuity in both directions (or use the Open Mapping Theorem for Fréchet spaces). We are going to harness (D.1.3.20) to reduce to the study of the factor groups $\mathbf{R}^m$, $\mathbf{T}^n$, $\mathbf{Z}^r$, and $F$, but we have to be careful since the completed tensor product there has no reason to interact well with an operation not yet known to be continuous.

To get around that problem, we will use Grothendieck’s explicit description of elements of completed projective tensor products $E\widehat{\otimes}_{\pi}F$ of Fréchet spaces [Scha, Ch. III, 6.4]: everything in the completed tensor product can be written in the form

$$
\sum_{j\ge 1}\lambda_j(e_j\otimes f_j)
$$

for an absolutely summable sequence $(\lambda_j)$ in $\mathbf{C}$ and sequences $(e_j)\subset E$ and $(f_j)\subset F$ that converge to 0. This will be applied to $\mathcal{S}(\mathbf{R}^m)\widehat{\otimes}_{\pi}\mathcal{S}(\mathbf{T}^n\times\mathbf{Z}^r\times F)$.

Before we cary that out, note that the Cauchy-Schwartz argument (as in [KG, Part I, Thm. 29, p. 72]) using multiplication and division by $1+|x|^N+|a|^N$ for $N\ge 2m,2r$ that shows the topology on $\mathcal{S}(G)$ can be defined using $L^1$-norms rather than sup-norms tells us that any sequence $\{\phi_j\}$ converging to 0 in $\mathcal{S}(G)$ has a uniform upper bound on all $\|\phi_j\|_1$’s, so in particular the Fourier transforms $\widehat{\phi}_j$ have uniformly bounded sup-norms over $G$. For $G_1=\mathbf{R}^m$ and $G_2=\mathbf{T}^n\times\mathbf{Z}^r\times F$, write a general $f\in\mathcal{S}(G)=\mathcal{S}(G_1)\widehat{\otimes}_{\pi}\mathcal{S}(G_2)$ in the form provided by Grothendieck:

$$
f=\sum_{j\ge 1}\lambda_j f_j\otimes F_j
$$

for an absolutely summable sequence $(\lambda_j)$ in $\mathbf{C}$ and sequences $f_j\in\mathcal{S}(G_1)$ tending to 0 and $F_j\in\mathcal{S}(G_2)$ tending to 0.

By Fubini’s Theorem, the Dominated Convergence Theorem, and the uniform bounds on the $L^1$-norms of all $\widehat{f}_j$’s and all $\widehat{F}_j$’s, we conclude that pointwise

$$
\widehat{f}(\chi_1,\chi_2)=\sum_{j\ge 1}\widehat{f}_j(\chi_1)\widehat{F}_j(\chi_2)
$$

for characters $\chi_i$ of $G_i$, and this is a uniformly convergent sum over $\widehat{G}$. It follows that if we know continuity of each $\mathcal{F}_{G_i}$ between Schwartz spaces then $\mathcal{F}_{G_1}\widehat{\otimes}_{\pi}\mathcal{F}_{G_2}$ makes sense on $\mathcal{S}(G)$ and coincides with $\mathcal{F}_G$, providing continuity of the latter. Thus, it suffices to separately treat $G_1$ and $G_2$.

We have peeled off $\mathbf{R}^m$ on its own, and in a similar way we can peel off $\mathbf{T}^n$ and then $\mathbf{Z}^r$ from $G_2$, so finally our task comes down to the separate cases of $\mathbf{R}^m$, $\mathbf{T}^n$, $\mathbf{Z}^r$, and $F$. The case of $F$ is trivial and the case of $\mathbf{R}^m$ (for which we only need to treat $m=1$) follows from the classical interaction of derivative and multiplication operators through the Euclidean Fourier transform. The remaining cases of $\mathbf{T}^n$ and $\mathbf{Z}^r$ are treated by [Tre, Thm. 51.3].

(3) : The identity (D.1.6.25) is a consequence$^7$ of the Poisson Summation Formula in its form of [DE, Thm. 3.6.3].$^8$ $\square$

$^7$Really? Need to say something about the calculation to make clear it isn’t hiding some real work with the measures to check it works on the nose.

$^8$Why is an external reference given here rather than citing (D.1.2.8) already stated in this document?

## PDF page 776

**776** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

Remark D.1.6.20. We note that by Lemma D.1.6.19(1), symbols of differential operators on $\widehat{G}$ are multipliers of the Schwartz-Bruhat space of $G$; i.e., for any $D\in\mathrm{Diff}(\widehat{G})$ and $f\in\mathcal{S}(G)$, $p(D)\cdot f\in\mathcal{S}(G)$.

For $G=\mathbf{R}$, the Lemma recovers the familiar compatibilities between Fourier transform and derivatives. Indeed, by Example D.1.6.12, $\sigma(\partial_x)=x$ as a function on $\mathbf{R}$ viewed as the character group of $\mathbf{R}$ itself, and (D.1.6.23) reads $\widehat{\partial_x f}=2\pi i x\cdot\widehat{f}$ by Corollary D.1.6.15, which is [Fol, Ch.8,Thm.8.22(e)].

**D.1.7. Distributional Poisson Summation.** We record here the following version of the Poisson Summation Formula (see Theorem D.1.2.7), with the aim of using it throughout Chapter ?? of this work. It is used in combination with Theorem 4.6.2.1, Theorem 4.6.1.5 and Lemma 4.4.2.6, to construct absolute Schauder bases in Theorem 7.3.1.6.

Theorem D.1.7.1 (Distributional Poisson Summation). *Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a choice of Haar measure on $G$. Let $k\subset G$ be a closed subgroup, and $\mu_k$ a choice of Haar measure on $k$. Let $\mu_{G/k}$ be the unique Haar measure on $G/k$ determined by the choices $\mu_G$ and $\mu_k$ as per Theorem D.1.2.1.*

*The linear map:*

$$
\Phi_k:\mathcal{S}(G)\to C(G/k)
\tag{D.1.7.1}
$$

*defined in (D.1.2.7) by*

$$
\Phi_k(\phi)(x):=\int_k\phi(hx)\,\mathrm{d}\mu_k(h)
\tag{D.1.7.2}
$$

*for all $x\in G$ is valued in $\mathcal{S}(G/k)$. The induced linear operator $\Phi_k:\mathcal{S}(G)\to\mathcal{S}(G/k)$ satisfies the following properties:*

*(1) The following identity holds for all $\phi\in\mathcal{S}(G)$, with $\widehat{\phi}$ the Fourier transform $\widehat{\phi}(\chi):=\int_G\phi(x)\overline{\chi}(x)\,\mathrm{d}\mu_G(x)$, and for all $x\in G$:*

$$
\Phi_k(\phi)(x)=\int_{k^{\perp}}\widehat{\phi}(\chi)\chi(x)\,\mathrm{d}\mu_{k^{\perp}}(\chi)
\tag{D.1.7.3}
$$

*where $\mu_{k^{\perp}}$ is the Haar measure on $k^{\perp}=\widehat{G/k}\subset\widehat{G}$ dual to $\mu_{G/k}$.*

*(2) The map $\Phi_k$ is a continuous and surjective. If $G$ is second-countable then it is a topological quotient map.*

Proof. When $G$ is an elementary abelian Lie group, everything apart from the identity in (1) is handled by Lemma D.1.6.18. We shall reduce all but (1) for general $G$ to such cases. The space $\mathcal{S}(G)$ is the locally convex inductive limit of spaces $\mathcal{S}(k',\Gamma')$ for structural pairs $(k',\Gamma')$ for $G$. Since $k\Gamma'/k$ is an open and compactly generated subgroup of $G/k$ in which $k'k/k'$ is a compact subgroup whose annihilator $k^{\perp}\cap k^{\prime\perp}\subset k^{\perp}=\widehat{G/k}$ is open in $\widehat{G/k}$ (as $k^{\prime\perp}$ is open in $\widehat{G}$) and compactly generated (as it is an open subgroup in $k^{\prime\perp}$ due to openness of $k^{\perp}$ in $\widehat{G}$, hence a closed subgroup of the compactly generated $k^{\prime\perp}$, so Theorem D.1.4.3(1) applies), we see that $(k'k/k',k\Gamma'/k)$ is a structural pair for $G/k$. The space $\mathcal{S}(G/k)$ is the locally convex inductive limit of spaces $\mathcal{S}(k'k/k,k\Gamma'/k)$ (since $G\to G/k$ is proper, so pairs of that special form are cofinal among all structural pairs for $G/k$).

Consider $\Phi_k$ applied to $f\in\mathcal{S}(k',\Gamma')=\mathcal{S}(\Gamma'/k')$. The resulting $k$-invariant function $\Phi_k(f)$ viewed on $G/k$ is $k'k/k$-invariant due to the $k'$-invariance of $f$, so averaging $\Phi_k(f)$ over $k'k/k$ has the effect of multiplying it by a volume for $k'k/k$ having nothing to do with $f$. But that further average is $\Phi_{k'k}(f)$, and $\Phi_{k'k}$ on $\mathcal{S}(k',\Gamma')$ is a nonzero scalar multiple of $\Phi_{k'k/k'}$ on $\mathcal{S}(\Gamma'/k')$. The settled case of elementary abelian Lie groups tells us that

$$
\Phi_{k'k/k'}:\mathcal{S}(\Gamma'/k')\to C(k\Gamma'/kk')
$$

## PDF page 777

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **777**

lands inside $\mathcal{S}(k\Gamma'/kk')$ and the resulting map $\mathcal{S}(\Gamma'/k')\to\mathcal{S}(k\Gamma'/kk')$ is a continuous surjection. Thus, $\Phi_k$ in general lands inside $\mathcal{S}(G/k)$ with $\Phi_k:\mathcal{S}(G)\to\mathcal{S}(G/k)$ a continuous surjection. When $G$ is second-countable, both $\mathcal{S}(G)$ and $\mathcal{S}(G/k)$ are strict $LF$-spaces. The Open Mapping Theorem for $LF$-spaces [Gro-f, Ch. 4, §5, Thm. 2(a), p. 148] then ensures $\Phi_k$ is a quotient map for such $G$.

It remains to prove (D.1.7.3). This is an application of Fourier inversion. Since $\Phi_k(\phi)$ and its Fourier transform are respectively Schwartz-Bruhat on $G/k$ and $\widehat{G/k}=k^{\perp}$, it satisfies Fourier inversion pointwise everywhere on $G/k$ by Lemma D.1.1.2(5). Since $\mu_{k^{\perp}}$ is the dual measure to $\mu_{G/k}$, for all $x\in G/k$ we have

$$
\Phi_k(\phi)(x)=\int_{k^{\perp}}\mathcal{F}_{G/k}(\Phi_k(\phi))(\chi)\chi(x)\,\mathrm{d}\mu_{k^{\perp}}(x)
$$

where $\mathcal{F}_{G/k}$ is defined using integration against $\mu_{G/k}$. Thus, it suffices to show

$$
\mathcal{F}_{G/k}(\Phi_k(\phi))(\chi)=\widehat{\phi}(\chi)
$$

for $\chi\in\widehat{G/k}=k^{\perp}$, where $\widehat{\phi}$ is defined using integration against $\mu_G$.

By definition,

$$
\widehat{\phi}(\chi)=\int_G\phi(g)\overline{\chi}(g)\,\mathrm{d}\mu_G(g)=\int_{G/k}\left(\int_k\phi(hg)\overline{\chi}(hg)\,\mathrm{d}\mu_k(h)\right)\mathrm{d}\mu_{G/k}(\overline{g}).
$$

In the integrand, $\chi(hg)=\chi(g)$ since $\chi\in k^{\perp}$, so the inner integral becomes

$$
\int_k\phi(hg)\overline{\chi}(g)\,\mathrm{d}\mu_k(h)=\Phi_k(\phi)(g)\overline{\chi}(g).
$$

This is what we needed.

$\square$

**D.1.8. Support of tempered distributions on Hausdorff locally compact abelian groups.** Let $G$ be a Hausdorff locally compact abelian group. Recall that $\mathcal{S}(G)$ is endowed with a natural Hausdorff locally convex topology, propagated from the special case $G$ is an elementary abelian Lie group (see §D.1.5, and [DE, Ch. 3, 4]) using the structure theory of Hausdorff locally compact abelian groups. In Theorem D.1.5.7 (which is [Bru, §10, Prop. 11]) the main properties of the Hausdorff locally convex topology on $\mathcal{S}(G)$ and its strong dual $\mathcal{S}(G)'_{\beta}$ were recorded when $G$ is second-countable.

We refer to $\mathcal{S}(G)'_{\beta}$ (the continuous dual of $\mathcal{S}(G)$, equipped with the Hausdorff locally convex “strong dual” topology of uniform convergence on the bounded subsets of $\mathcal{S}(G)$) as the space of *tempered distributions* on $G$. When $G$ is an elementary abelian Lie group, say $G\simeq\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$, the description of $\mathcal{S}(G)$ as a completed tensor product in (D.1.3.20) implies density of the image of the continuous injection $\mathcal{D}(G):=C_c^{\infty}(G)\to\mathcal{S}(G)$ by reduction to the classical case of $\mathbf{R}^m$ [KG, Thm. 30, p. 74] (where the proof for $m=1$ easily adapts to general $m$) and the straightforward case of $\mathbf{Z}^r$, so passage to direct limit with subspaces $\mathcal{S}(k,\Gamma)$ then gives the same density result for general $G$. In particular, the induced map on topological linear duals $\mathcal{S}(G)'\to\mathcal{D}(G)'$ is *injective* for general $G$. In this way we view the space of tempered distributions as a special subspace of the space of all distributions (continuous linear functionals on compactly supported smooth functions), equipped with a finer strong dual topology.

D.1.8.1. *Kernel Theorems.* We let $(m,k,r)\in\mathbf{N}^3$ be a triple of non-negative integers, $F$ a finite abelian group, and consider the elementary abelian Lie group:

$$
G:=\mathbf{R}^m\times\mathbf{T}^k\times\mathbf{Z}^r\times F.
$$

Describing tempered distributions on $G$ amounts to describing tempered distributions on $\mathbf{R}^m$, $\mathbf{T}^k$, $\mathbf{Z}^r$ and $F$, respectively, in light of the following:

## PDF page 778

**778** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

Lemma D.1.8.1 (Kernel Theorem for Schwartz-Bruhat spaces). *Let $G_1,G_2$ be Hausdorff locally compact abelian groups. Assume $G_1$ and $G_2$ are second-countable. Then:*

*(1) The canonical linear map from $\mathcal{S}(G_1)\otimes\mathcal{S}(G_2)$ to $\mathcal{S}(G_1\times G_2)$ is continuous with respect to the inductive tensor product topology on the source, and it extends to a continuous linear map*

$$
\mathcal{S}(G_1)\overline{\otimes}\mathcal{S}(G_2)\to\mathcal{S}(G_1\times G_2)
\tag{D.1.8.1}
$$

*which is a linear topological isomorphism.*

*(2) The canonical linear map $\mathcal{S}(G_1)'\otimes\mathcal{S}(G_2)'\to(\mathcal{S}(G_1)\otimes_{\iota}\mathcal{S}(G_2))'=(\mathcal{S}(G_1)\overline{\otimes}\mathcal{S}(G_2))'\simeq\mathcal{S}(G_1\times G_2)'$ extends to a continuous linear map*

$$
\mathcal{S}(G_1)'_{\beta}\widehat{\otimes}_{\pi}\mathcal{S}(G_2)'_{\beta}\to\mathcal{S}(G_1\times G_2)'_{\beta}
\tag{D.1.8.2}
$$

*which is a topological isomorphism.*

In (D.1.8.2) it is equivalent by Corollary C.2.3.12 to use $\widehat{\otimes}_{\varepsilon}$ since the spaces $\mathcal{S}(G_j)'_{\beta}$ are nuclear by Theorem D.1.5.7. For the proof of (2), we further refer the reader to [Al-B, Lemma 3, p. 803].

Proof. (1) : Assume first that $G_1$ and $G_2$ are elementary abelian Lie groups. In this case $\mathcal{S}(G_1)$ and $\mathcal{S}(G_2)$ are Fréchet spaces, so the inductive tensot product topology on $\mathcal{S}(G_1)\otimes\mathcal{S}(G_2)$ coincides with the projective tensor product topology by [Scha, Ch. III, 5.1]. Hence, the desired result in these cases is immediate from Lemma D.1.3.7(2).

In the general case, we note that for any second-countable Hausdorff locally compact abelian group $G$, the Hausdorff locally convex topological vector space $\mathcal{S}(G)$ is a strict LF-space since it is the inductive limit of Fréchet spaces $\mathcal{S}(k,\Gamma)\simeq\mathcal{S}(\Gamma/k)$ as $(k,\Gamma)$ varies over a *countable* cofinal system of structural pairs for $G$ (see Definition D.1.5.1); i.e., $\Gamma\subset G$ is an open and compactly generated subgroup, and $k\subset G$ is a compact subgroup contained in $\Gamma$ whose open orthogonal is compactly generated (noting that $\Gamma/k$ is therefore an abelian Lie group). That such a countable collection of pairs exists uses that $G$ is second-countable. The desired assertion then follows from Corollary C.2.3.12 and (the end of) Proposition C.2.3.13(2); the latter result rests on the countability aspect noted above.

(2) : If $G_1$ and $G_2$ are elementary abelian Lie groups then $\mathcal{S}(G_1)$ and $\mathcal{S}(G_2)$ are nuclear Fréchet spaces, so by (1) and Corollary C.2.3.12 the assertion is that the formation of the strong duals of these Schwartz spaces “commutes” with completed projective tensor products. This is a general property of nuclear Fréchet spaces [Tre, Prop. 50.7] (bearing in mind also that the strong dual of a nuclear Fréchet space is always nuclear [Tre, Prop. 50.6]).

In general, by expressing each $\mathcal{S}(G_j)$ as a countable strict inductive limit $\lim_{\longrightarrow}\mathcal{S}(\Gamma_{m,j}/k_{m,j})$ (whose topological embedding transition maps are closed embeddings by completeness of each $E_m:=\mathcal{S}(\Gamma_{m,1}/k_{m,1})$ and $F_m:=\mathcal{S}(\Gamma_{m,2}/k_{m,2})$), the argument at the end of the proof of Lemma C.1.6.1(2) gives the topological identifications

$$
\mathcal{S}(G_1)'_{\beta}=\lim E'_{m,\beta},\ \mathcal{S}(G_2)'_{\beta}=\lim F'_{m,\beta}.
$$

(with all transition maps surjective). Since $\mathcal{S}(G_1\times G_2)'_{\beta}$ is compatibly identified as a topological vector space with the inverse limit of the spaces $(\mathcal{S}(\Gamma_{m,1}/k_{m,1})\widehat{\otimes}_{\pi}\mathcal{S}(\Gamma_{m,2}/k_{m,2}))'_{\beta}$ by (1), the desired result thereby reduces to checking that for the countable inverse systems $\{E'_{m,\beta}\}$ and $\{F'_{m,\beta}\}$, the natural continuous linear map

$$
\lim E'_{m,\beta}\widehat{\otimes}_{\pi}\lim F'_{m,\beta}\to\lim(E_m\widehat{\otimes}_{\pi}F_m)'_{\beta}=\lim(E'_{m,\beta}\widehat{\otimes}_{\pi}F'_{m,\beta})
\tag{D.1.8.3}
$$

is a topological isomorphism (the passage of strong dual through the completed projective tensor product is an instance of (1)).

By [Jar, Section 16.3, Cor. 2], the formation of completed *injective* tensor products $\widehat{\otimes}_{\varepsilon}$ commutes with inverse limits of Hausdorff topological vector spaces in the natural manner. Thus, it suffices to show that the completed projective tensor products on each side of (D.1.8.3) are identified with the corresponding

## PDF page 779

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **779**

completed injective tensor products (via the natural map from $\widehat{\otimes}_{\pi}$ to $\widehat{\otimes}_{\varepsilon}$). For this it suffices by Corollary C.2.3.12 to check that one of the factor spaces in each such completed tensor product is nuclear. By [Tre, Prop. 50.6] each $E'_{m,\beta}$ and $F'_{m,\beta}$ is nuclear due to the $E_m$'s and $F_m$'s being nuclear Fréchet, so the right side of (D.1.8.3) is settled. For the left side of (D.1.8.3), we use that an inverse limit of nuclear spaces is nuclear [Scha, Ch. III, Cor. to 7.4].

$\square$

D.1.8.2. *Supports.* We recall that a tempered distribution $T$ on $G=\mathbf{T}^n$ is simply a distribution, since $\mathcal{S}(\mathbf{T}^n)=\mathcal{D}(\mathbf{T}^n)$ ($:=C_c^{\infty}(\mathbf{T}^n)$). In particular, the *support* of $T$ is (by definition) the smallest closed subset $K$ of $\mathbf{T}^n$ such that $\langle T,f\rangle_{\mathcal{S}(\mathbf{T}^n)',\mathcal{S}(\mathbf{T}^n)}=0$ for any $f\in\mathcal{S}(\mathbf{T}^k)$ supported in $\mathbf{T}^n-K$. Since the support of any $f\in\mathcal{S}(\mathbf{T}^n)$ is compact, using a smooth partition of unity it is equivalent to say that the support of $T$ is the closed subset $K\subset\mathbf{T}^n$ whose complement is the union of those open $U\subset\mathbf{T}^n$ such that $\langle T,f\rangle_{\mathcal{S}(\mathbf{T}^n)',\mathcal{S}(\mathbf{T}^n)}=0$ for every Schwartz function $f$ on $\mathbf{T}^n$ supported in $U$.

The notion of *support* of a tempered distribution on $\mathbf{R}^m$ is defined by adapting the notion of support of distributions on $\mathbf{R}^m$ as in [Horm, Ch. II, §2.2, Def. 2.2.2]: it is the closed subset $K\subset\mathbf{R}^m$ whose complement is the union of those open $U\subset\mathbf{R}^m$ such that $\langle T,f\rangle_{\mathcal{S}(\mathbf{R}^m)',\mathcal{S}(\mathbf{R}^m)}=0$ for every Schwartz function $f$ on $\mathbf{R}^m$ supported over $U$.

Definition D.1.8.2. Let $G$ be a Hausdorff locally compact abelian group. Let $T\in\mathcal{S}(G)'$ be a tempered distribution on $G$.

(1) The *vanishing locus* of $T$ is defined to be the union of all open subsets $U\subset G$ such that $\langle T,f\rangle_{\mathcal{S}(G)',\mathcal{S}(G)}=0$ for every $f\in\mathcal{S}(G)$ supported in $U$.

(2) The *support* of $T$, denoted $\mathrm{supp}(T)\subset G$, is defined to be the complement of $V(T)$ in $G$.

Proposition D.1.8.3. *Let $G=\mathbf{R}^m\times\mathbf{T}^k\times\mathbf{Z}^r\times F$ be an elementary abelian Lie group. Let $T\in\mathcal{S}(G)'$ be a tempered distribution of the form $T_1\otimes T_2\otimes T_3\otimes T_4$, for $T_1\in\mathcal{S}(\mathbf{R}^m)'$, $T_2\in\mathcal{S}(\mathbf{T}^n)'$, $T_3\in\mathcal{S}(\mathbf{Z}^r)'$, $T_4\in\mathcal{S}(F)'$. Then we have:*

$$
\mathrm{supp}(T)=\mathrm{supp}(T_1)\times\mathrm{supp}(T_2)\times\mathrm{supp}(T_3)\times\mathrm{supp}(T_4).
\tag{D.1.8.4}
$$

Proof. Define $G_1=\mathbf{R}^m$, $G_2=\mathbf{T}^n$, $G_3=\mathbf{Z}^r$, $G_4=F$. For the containment “$\supset$”, we prove the reverse for the complements: if $\xi\in G-\mathrm{supp}(T)$ then we want $\xi\notin\mathrm{supp}(T_1)\times\mathrm{supp}(T_2)\times\mathrm{supp}(T_3)\times\mathrm{supp}(T_4)$. By the definition of $\mathrm{supp}(T)$, there are open sets $U_i\subset G_i$ such that $\xi\in U:=U_1\times U_2\times U_3\times U_4$ and $T$ kills any $f\in\mathcal{S}(G)$ supported inside $U$. It suffices to show $U_j\subset G_j-\mathrm{supp}(T_j)$ for some $j$. If not, for each $1\le j\le 4$ there exists $f_j\in\mathcal{S}(G_j)$ supported inside $U_j$ such that $\langle T_j,f_j\rangle_{\mathcal{S}(G_j)',\mathcal{S}(G_j)}\ne 0$. Then for $f=f_1\otimes\cdots\otimes f_4\in\mathcal{S}(G)$ we have $\langle T,f\rangle_{\mathcal{S}(G)',\mathcal{S}(G)}=\prod\langle T_j,f_j\rangle_{\mathcal{S}(G_j)',\mathcal{S}(G_j)}\ne 0$. But $\mathrm{supp}(f)\subset\prod\mathrm{supp}(f_j)\subset U$, so this contradicts that $T$ kills all Schwartz-Bruhat functions on $G$ supported inside $U$.

For the reverse containment, if $\xi\in G$ has $j$th component $\xi_j\in G_j-\mathrm{supp}(T_j)$ for some $1\le j\le 4$ then we want to show $\xi\notin\mathrm{supp}(T)$. By definition of $\mathrm{supp}(T_j)$, there exists an open $U_j\subset G_j$ containing $\xi_j$ so that every $f_j\in\mathcal{S}(G_j)$ supported inside $U_j$ is killed by $T_j$. Shrinking $U_j$ allows us to assume it has compact closure. It suffices to show any $f\in\mathcal{S}(G)$ supported inside $(\prod_{i\ne j}G_i)\times U_j$ is killed by $T$. We will do this by first passing to the compactly supported case.

The construction in the proof of density of $C_c^{\infty}(\mathbf{R}^m)$ inside $\mathcal{S}(\mathbf{R}^m)$ in [KG, p. 76] via $\chi_N\varphi\to\varphi$ for $\chi_N(x)=\chi(x/N)$ for a smooth function $\chi$ equal to $1$ on $[-1,1]^m$ and supported inside $[-2,2]^m$ does not increase support, so we can apply it at the level of the completed tensor product description of $\mathcal{S}(G)$ in (D.1.3.20). We can make a similar density proof for $C_c(\mathbf{Z}^r)$ inside $\mathcal{S}(\mathbf{Z}^r)$ by using $\chi_N:\mathbf{Z}^r\to\mathbf{C}$ that is the characteristic function of $[-N,N]^r$. In this way, we can express any $f\in\mathcal{S}(G)$ supported inside $(\prod_{i\ne j}G_i)\times U_j$ as a limit of a sequence of functions $f_k\in C_c^{\infty}(G)$ supported inside $(\prod_{i\ne j}G_i)\times U_j$. By continuity of $T$ it

## PDF page 780

**780** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

suffices to show $\langle T,f_k\rangle_{\mathcal{S}(G)',\mathcal{S}(G)}=0$ for all $k$. In other words, it is enough to treat the case of compactly supported $f$.

The compact support $K\subset G$ of $f$ has compact image $K_j\subset U_j$. We can pick a smooth function $\psi$ on $U_j$ equal to $1$ on $K_j$ and having compact support $K'_j\subset U_j$. Multiplication by $\psi$ on $\mathcal{S}(G_j)$ has image inside the closed subspace $C_{K'_j}^{\infty}(G_j)$ of smooth functions on $G_j$ supported inside $K'_j\subset U_j$, so

$$
f=\psi f\in C_{K'_j}^{\infty}(G_j)\widehat{\otimes}_{\pi}\mathcal{S}(\prod_{i\ne j}G_i).
$$

Since $T_j$ kills $C_{K'_j}^{\infty}(G_j)$, we conclude that $T$ kills $f$.

$\square$

Lemma D.1.8.4. *Let $G$ be a Hausdorff locally compact abelian group, $T\in\mathcal{S}(G)'$ a tempered distribution. For each structural pair $(k,\Gamma)$ for $G$ (i.e., $\Gamma\subset G$ an open compactly generated subgroup, $k\subset G$ a compact subgroup with open compactly generated orthogonal $k^{\perp}$, and $k\subset\Gamma$; see Definition D.1.5.1), let $T_{(k,\Gamma)}\in\mathcal{S}(\Gamma/k)'$ denote composition of $T$ with the continuous map $\mathcal{S}(\Gamma/k)\simeq\mathcal{S}(k,\Gamma)\hookrightarrow\mathcal{S}(G)$ (see Definition D.1.5.3).*

*The open subset $V(T)=G-\mathrm{supp}(T)\subset G$ is contained in the union of the open preimages under $\Gamma\to\Gamma/k$ of $V(T_{(k,\Gamma)})\subset\Gamma/k$ as $(k,\Gamma)$ varies over the directed set of all structural pairs of $G$.*

Proof. A point $\overline{g}\in\Gamma/k$ belongs to $V(T_{(k,\Gamma)})$ if and only if there exists an open neighborhood $\overline{U}\subset\Gamma/k$ of $\overline{g}$ such that $\langle T_{(k,\Gamma)},f\rangle=0$ for every $f\in\mathcal{S}(\Gamma/k)$ supported in $\overline{U}$. This vanishing condition says

$$
\langle T,\widetilde{f}\rangle_{\mathcal{S}(G)',\mathcal{S}(G)}=0
$$

for $\widetilde{f}$ the extension by zero from $\Gamma$ to $G$ of the composition of $f$ with the quotient homomorphism $\Gamma\to\Gamma/k$. Such $f$'s are exactly the $k$-invariant Schwartz-Bruhat functions supported in the open preimage $U$ of $\overline{U}$ in $\Gamma$.

Now consider a point $g\in V(T)$. There exists an open and compactly generated subgroup $\Gamma\subset G$ containing $g$ and a compact subgroup $k\subset G$ contained in $\Gamma$ and with compactly generated orthogonal $k^{\perp}\subset\widehat{G}$. Note that $\Gamma$ is necessarily also closed in $G$. By definition of $V(T)$, there exists an open neighborhood $U\subset G$ of $g$ such that $\langle T,f\rangle_{\mathcal{S}(G)',\mathcal{S}(G)}=0$ for every $f\in\mathcal{S}(G)$ whose support is contained in $U$. We can shrink $U$ around $g$ so that $U\subset\Gamma$. By Lemma D.1.4.7, we can shrink $k$ so that $kg\subset U\subset\Gamma$, and then find an open $V\subset U$ around $g$ so that $kV\subset U$. Thus, we can replace $U$ with $kV$ to arrange that $U$ is the preimage in $\Gamma$ of an open subset $\overline{U}\subset\Gamma/k$ containing $\overline{g}:=g\bmod k$. This implies $\overline{U}\subset V(T_{(k,\Gamma)})$, so since the initial arbitrary choice of $g\in V(T)$ belongs to $U$, we have shown $V(T)$ is contained in the desired union.

$\square$

**D.1.9. Continuity of translation on Schwartz-Bruhat spaces.** With the aim to make Lemma 4.3.3.1 and its corollaries applicable, we discuss continuity properties of the left-translation action of a Hausdorff locally compact abelian group $G$ on its Schwartz-Bruhat space $\mathcal{S}(G)$. Since both $G$ and $\mathcal{S}(G)$ are generally studied via direct limits from the case of elementary abelian Lie groups, we begin with a basic lemma on inheritance of continuity through locally convex inductive limits.

Lemma D.1.9.1. *Let $H$ be a Hausdorff locally compact topological group that is the union of an increasing sequence of open subgroups $\{H_n\}_{n\ge 1}$. Let $\{E_n\}$ be a strict inductive system of Hausdorff locally convex topological vector spaces such that every $E_n$ is barrelled, and let $E=\lim_{\longrightarrow}E_n$.*

*If an action of $H$ on $E$ makes $H_n$ act continuously on $E_n$ for every $n$ then theaction map $H\times E\to E$ is continuous.*

Proof. The space $E$ is barrelled by [Scha, Ch. II, Cor. 1 to 7.2]. Each $h\in H$ lies in some $H_{n_0}$, so the $h$-action on $E$ carries $E_n$ into itself for all $n\ge n_0$ with $h:E_n\to E_n$ a topological isomorphism for such $n$ (since $H_n$ acts continuously on $E_n$). Thus, $h:E\to E$ is a topological isomorphism, so the $H$-action on $E$ is encoded in a group homomorphism $\rho:H\to\mathcal{L}(E)$ into the vector space of continuous linear endomorphisms of $E$. Since $H$ is locally compact, continuity for its action on $E$ is equivalent to the conjunction of two properties:

## PDF page 781

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **781**

(i) equicontinuity at $0\in E$ for the subset $\rho(K)\subset\mathcal{L}(E)$ for every compact subset $K\subset H$, (ii) for each $x\in E$ and $0$-neighborhood $U\subset E$ the existence of an $e$-neighborhood $\Omega\subset H$ such that $\Omega.x\subset x+U$.

First we verify (i). The barrelledness of $E$ ensures (by [Scha, Ch. III, 4.2]) that equicontinuity holds if the subset $K.x\subset E$ is weakly bounded for every $x\in E$: that is, $\{\ell(k.x)\}_{k\in K}$ is bounded in $\mathbf{C}$ for each continuous linear functional $\ell\in E'$. Thus, it suffices that $K.x$ is compact for each $x\in E$. The open cover $\{H_n\cap K\}$ of $K$ has a finite subcover, so $K\subset H_n$ for sufficiently large $n$. By taking $n$ big enough, also $x\in E_n$. Since $H_n$ acts continuously on $E_n$, we see that $K.x$ is compact inside $E_n$ and so the boundedness of $\ell(K.x)$ follows.

To verify (ii), pick $n$ for which $x\in E_n$. Since $H_n$ acts continuously on $E_n$, there is an $e$-neighborhood $\Omega\subset H_n$ such that $\Omega.x\subset x+(U\cap E_n)\subset x+U$. Since $H_n$ is open in $H$, we are done.

$\square$

Proposition D.1.9.2. *Let $G$ be a second-countable Hausdorff locally compact abelian group. The left-translation action $\rho:G\times\mathcal{S}(G)\to\mathcal{S}(G)$ is continuous. In particular, for any compact subset $K\subset G$ the map $K\times\mathcal{S}(G)\to\mathcal{S}(G)$ is uniformly continuous over $K$ in the sense that for any $0$-neighborhood $U\subset\mathcal{S}(G)$ there is a $0$-neighborhood $V\subset\mathcal{S}(G)$ such that $K.V\subset U$.*

Proof. If the $G$-action is continuous then the uniform continuity property for compact subsets $K\subset G$ is immediate from the fact that $k.0=0$ for all $k\in K$. To prove the continuity of the $G$-action we first reduce to the case that $G$ is an elementary abelian Lie group. Since $G$ is second-countable, there is a countable directed system of structural pairs $(k_n,\Gamma_n)$ (see Definition D.1.5.1) such that $\mathrm{colim}\,\mathcal{S}(k_n,\Gamma_n)\to\mathcal{S}(G)$ is a linear topological isomorphism with each injection $\mathcal{S}(\Gamma_n/k_n)=\mathcal{S}(k_n,\Gamma_n)\to\mathcal{S}(G)$ a topological embedding. We apply Lemma D.1.9.1 to $H=G$ with $H_n=\Gamma_n$ and $E_n=\mathcal{S}(k_n,\Gamma_n)\simeq\mathcal{S}(\Gamma_n/k_n)$ (so $E=\mathcal{S}(G)$). Note that the barrelledness of such $E_n$'s follows from $\mathcal{S}(A)$ being a Fréchet space for elementary abelian Lie groups $A$, since every Fréchet space is barrelled [Scha, Ch. II, Cor. to 7.1]. This reduces the continuity task to the case of the groups $\Gamma_n/k_n$ that are elementary abelian Lie groups.

We can write $G=\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$ for integers $m,n,r\ge 0$ and a finite abelian group $F$. By (D.1.3.20), $\mathcal{S}(G)$ is the completed projective tensor product of $\mathcal{S}(\mathbf{R}^m)$, $\mathcal{S}(\mathbf{T}^n)$, $\mathcal{S}(\mathbf{Z}^r)$, and $\mathcal{S}(F)=\mathbf{C}^F$. The left $G$-action on $\mathcal{S}(G)$ preserves the subspace given by the “uncompleted” projective tensor product. To reduce the continuity verification to the action of $G$ on the uncompleted projective tensor product, we apply:

Lemma D.1.9.3. *Let $E$ be a Hausdorff topological vector space and $H$ a topological group equipped with a left action on the completion $\widehat{E}$ preserving the subspace $E$. If each $h\in H$ acts continuously on $\widehat{E}$ and the action map $H\times E\to E$ is continuous then the action map $H\times\widehat{E}\to\widehat{E}$ is continuous.*

Proof. Since $H$ is a topological group whose elements individually act continuously on $\widehat{E}$ (by hypothesis), it suffices to prove the action map on $\widehat{E}$ is continuous at $(e,x)$ for each $x\in\widehat{E}$. A base of $x$-neighborhoods in $\widehat{E}$ is given by $x+\overline{U}$ for $0$-neighborhoods $U\subset E$. Thus, for each such $U$ we seek a $0$-neighborhood $V\subset E$ and an $e$-neighborhood $W\subset H$ such that $W.(x+\overline{V})\subset x+\overline{U}$. Since each $h\in H$ acts continuously on $\widehat{E}$, it is equivalent to show $W.(x+V)\subset x+\overline{U}$ for some $W$ and $V$. This holds for $x=0$: the assumed continuity of the $H$-action on $E$ provides a $0$-neighborhood $V\subset E$ and an $e$-neighborhood $W\subset H$ such that $W.V\subset U\subset\overline{U}$.

To handle general $x\in\widehat{E}$, pick a $0$-neighborhood $U'\subset E$ so that $U'+U'\subset U$ and then a $0$-neighborhood $U''$ so that $U''+U''-U''\subset U'$ By the verified continuity at $(e,0)$, there exists an $e$-neighborhood $W'\subset H$ and $0$-neighborhood $U_0\subset E$ such that $W'.\overline{U}_0\subset\overline{U''}$. Thus, for $x_0\in E$ with $x-x_0\in\overline{U''}$ we have

$$
W'.x\subset W'.(\overline{U}_0)+W'.x_0\subset\overline{U''}+W'.x_0.
$$

By the assumed continuity of the $H$-action on $E$, we can find an $e$-neighborhood $W''\subset W'$ so that $W''.x_0\subset x_0+U''$. Thus,

$$
W''.x\subset\overline{U''}+W''.x_0\subset\overline{U''}+U''+x_0\subset\overline{U''}+U''-\overline{U''}+x\subset x+\overline{U'}.
$$

## PDF page 782

**782** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

The continuity of the $H$-action on $E$ also provides an $e$-neighborhood $W\subset W''$ and a $0$-neighborhood $V\subset E$ such that $W.V\subset U'$. Hence,

$$
W.(x+V)\subset W.x+W.V\subset W''.x+U'\subset x+\overline{U'}+U'\subset x+\overline{U}
$$

as desired.

$\square$

We are reduced to proving the continuity of the $G$-action on the projective tensor product $\mathcal{S}(\mathbf{R}^m)\otimes_{\pi}\mathcal{S}(\mathbf{T}^n)\otimes_{\pi}\mathcal{S}(\mathbf{Z}^r)\otimes_{\pi}\mathcal{S}(F)$. To further reduce to the separate treatment of the cases $G=\mathbf{R}^m,\mathbf{T}^n,\mathbf{Z}^r,F$, we next apply:

Lemma D.1.9.4. *If $H$ is a topological group acting continuously on Hausdorff locally convex topological vector spaces $E_1,E_2$ then the natural action of $H$ on $E_1\otimes_{\pi}E_2$ is continuous.*

Proof. Since $H$ is a topological group whose elements individually act continuously on $\widehat{E}$ (by hypothesis), it suffices to prove continuity at $(e,x)$ for each $x\in E_1\otimes E_2$. By writing $x$ as a finite sum of elementary tensors, we reduce to the case that $x=x_1\otimes x_2$ is an elementary tensor. A neighborhood base of $x$ in $E_1\otimes_{\pi}E_2$ is given by the $x$-translates of the convex circled hulls of the sets $U_1\otimes U_2$ of elementary tensors $u_1\otimes u_2$ with $u_j\in U_j$ for a base of convex circled $0$-neighborhoods $U_j\subset E_j$. For a choice of $U_1$ and $U_2$, pick convex circled $0$-neighborhoods $U''_j\subset U'_j\subset E_j$ such that

$$
\mathrm{cch}(U'_1\otimes U'_2)+\mathrm{cch}(U'_1\otimes U'_2)+\mathrm{cch}(U'_1\otimes U'_2)+\mathrm{cch}(U'_1\otimes U'_2)\subset\mathrm{cch}(U_1\otimes U_2)
$$

and

$$
x_1\otimes U''_2\subset\mathrm{cch}(U'_1\otimes U'_2),\ U''_1\otimes x_2\subset\mathrm{cch}(U'_1\otimes U'_2)
$$

(we can use $U''_j=\lambda U'_j$ for a nonzero small $\lambda\in\mathbf{C}$ such that $\lambda x_i\in U'_i$ for $i=1,2$).

Continuity of the $H$-action on each $E_j$ provides a convex circled $0$-neighborhood $V_j\subset E_j$ and an $e$-neighborhood $W_j\subset H$ so that $W_j.V_j\subset U'_j$ and $W_j.x_j\subset x_j+U''_j$. Thus, $W:=W_1\cap W_2$ carries the convex circled hull of $V_1\otimes V_2$ into that of $U'_1\otimes U'_2$ and carries $x=x_1\otimes x_2$ into $x+x_1\otimes U''_2+U''_1\otimes x_2+U'_1\otimes U'_2$ (recall $U''_j\subset U'_j$). This implies

$$
W.(x+\mathrm{cch}(V_1\otimes V_2))\subset x+x_1\otimes U''_2+U''_1\otimes x_2+U'_1\otimes U'_2+\mathrm{cch}(U'_1\otimes U'_2)
\tag{D.1.9.1}
$$

$$
\subset x+\mathrm{cch}(U'_1\otimes U'_2)+\mathrm{cch}(U'_1\otimes U'_2)+\mathrm{cch}(U'_1\otimes U'_2)+\mathrm{cch}(U'_1\otimes U'_2)
$$

$$
\subset x+\mathrm{cch}(U_1\otimes U_2).
$$

The verifies the continuity of the action at $(e,x)$ for general $x\in\widehat{E}$.

$\square$

We are reduced to treating the separate cases $G=\mathbf{R}^m,\mathbf{T}^n,\mathbf{Z}^r,F$. The case $G=F$ a finite abelian group holds because the natural $F$-action on $\mathbf{C}^F$ is clearly continuous. Next suppose $G=\mathbf{R}^m$. It suffices to prove two properties: the continuity of $G\times\mathcal{S}(G)\to\mathcal{S}(G)$ at $(e,f)$ for each $f\in\mathcal{S}(G)$ and the equicontinuity at $0\in\mathcal{S}(G)$ for each compact subset $K\subset G$. For each $f\in\mathcal{S}(\mathbf{R}^m)$, $0$-neighborhood $U\subset\mathcal{S}(\mathbf{R}^m)$, and compact subset $K\subset\mathbf{R}^m$, we seek a $0$-neighborhood $\Omega\subset\mathbf{R}^m$ and a $0$-neighborhood $V\subset\mathcal{S}(\mathbf{R}^m)$ such that $\Omega.f\subset f+U$ and $K.V\subset U$. This says (i) if $\Omega$ is sufficiently small then $\Omega.f$ is sufficiently near $f$, and (ii) $K$ is equicontinuous at $0$.

For (i), we use the family of seminorms (D.1.3.8) defining the topology on $\mathcal{S}(\mathbf{R}^m)$. Given $\varepsilon>0$, $j\in\mathbf{N}$, and $\alpha\in\mathbf{N}^m$ it suffices to show that for all $c\in\mathbf{R}^m$ sufficiently near $0$ (depending on $\varepsilon$, $j$, $\alpha$ and $f$)

$$
\sup_{x\in\mathbf{R}^m}|(1+|x|^j)\partial_x^{\alpha}f(x+c)-(1+|x|^j)\partial_x^{\alpha}f(x)|\le\varepsilon.
$$

Since

$$
(1+|x+c|^j)-(1+|x|^j)=\left(1-\frac{1+|x|^j}{1+|x+c|^j}\right)(1+|x+c|^j)
$$

## PDF page 783

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **783**

with $|1-(1+|x|^j)/(1+|x+c|^j)|\le\varepsilon$ for all $x\in\mathbf{R}^m$ when $c$ is sufficiently near $0$, for such $c$ we have
$$
|(1+|x+c|^j)\partial_x^{\alpha}f(x+c)-(1+|x|^j)\partial_x^{\alpha}f(x+c)|\le\varepsilon\sup_{y\in\mathbf{R}^m}|(1+|y|^j)\partial_y^{\alpha}f(y)|
$$
where the supremum on the right side is finite. Thus, it suffices to instead show that for all $c\in\mathbf{R}^m$ sufficiently near $0$ (depending on $\varepsilon$, $j$, $\alpha$ and $f$) that
$$
\sup_{x\in\mathbf{R}^m}|(1+|x+c|^j)\partial_x^{\alpha}f(x+c)-(1+|x|^j)\partial_x^{\alpha}f(x)|\le\varepsilon.
$$
Since $f$ is Schwartz, there exists $R>0$ so that if $|x|>R$ then $|(1+|x|^j)\partial_x^{\alpha}f(x)|\le\varepsilon/2$. If $|c|\le R/2$ and $|x|>3R/2$ then $|x+c|>R$, so for such $c$ and $x$ we have
$$
|(1+|x+c|^j\partial_x^{\alpha}f(x+c)-(1+|x|^j)\partial_x^{\alpha}f(x)|\le\varepsilon/2+\varepsilon/2=\varepsilon.
$$
It instead $|x|\le 3R/2$ then continuity in $(x,c)$ for
$$
(1+|x+c|^j\partial_x^{\alpha}f(x+c)-(1+|x|^j)\partial_x^{\alpha}f(x)
$$
ensures that this difference has absolute value at most $\varepsilon$ whenever $|x|\le 3R/2$ provided that $c$ is sufficiently near $0$. This settles (i).

For (ii), we pick $\varepsilon>0$, $j\in\mathbf{N}$, and $\alpha\in\mathbf{N}^m$ and will show that for all $c\in K$ we have
$$
\sup_{x\in\mathbf{R}^m}|(1+|x|^j)\partial_x^{\alpha}f(x+c)|\le\varepsilon
\tag{D.1.9.2}
$$
provided that $\sup_{x\in\mathbf{R}^m}|(1+|x|^i)\partial_x^{\alpha}f(x)|$ is small enough (in terms of $\varepsilon$, $j$, and $K$) for all $0\le i\le j$. Since $|c|\le B_K$ for some constant $B_K$, the supremum in (D.1.9.2) can be rewritten as bounded from above:
$$
\sup_{y\in\mathbf{R}^m}|(1+|y-c|^j)\partial_y^{\alpha}f(y)|\le\sup_{y\in\mathbf{R}^m}|(1+(|y|+B_K)^j)\partial_y^{\alpha}f(y)|\le\sum_{i=0}^j\binom{j}{i}B_K^{j-i}\sup_{y\in\mathbf{R}^m}|(1+|y|^i)\partial_y^{\alpha}f(y)|.
$$
This upper bound is at most $\varepsilon$ when each of the terms in the sum is small enough (in terms of $\varepsilon$, $j$, and $B_K$). This settles (ii), and so completes the treatment of the case $G=\mathbf{R}^m$.

The case $G=\mathbf{T}^n$, so $\mathcal{S}(G)=C^{\infty}(\mathbf{T}^n)$, is an easier version of the argument for $\mathbf{R}^m$ with no polynomial multiplier thanks to compactness of the group $\mathbf{T}^n$ (and translation-invariance of the differential operators $\partial_{z_j}$ on $\mathbf{T}^n=\mathbf{R}^n/\mathbf{Z}^n$). The case $G=\mathbf{Z}^r$ is also an easier version of the argument for $\mathbf{R}^m$ with $\alpha=0$ (i.e., no differential operator). $\square$

D.1.10. Examples: global and $S$-local idele classes. As per the general definition of the $\mathbf{C}$-linear space of Schwartz-Bruhat functions on a Hausdorff locally compact abelian group $G$, upon calling $G$ either $C_F$ or $C_{F,S}$, then $\mathcal{S}(G)$ is the locally convex inductive limit of a system of Fréchet spaces $\mathcal{S}(\Gamma/k)$ where $\Gamma\subset G$ is open and compactly generated, $k\subset\Gamma$ is compact with (open and) compactly generated annihilator $k^{\perp}$ in $\widehat{G}$. In particular, if $G$ is second-countable then $\mathcal{S}(G)$ is a strict LF-space.

Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places. In this section we describe explicitly the Hausdorff locally convex topological $\mathbf{C}$-vector spaces $\mathcal{S}(C_{F,S})$ and $\mathcal{S}(C_F)$. We call $S_f:=S\cap\Sigma_{F,f}$. Recall that $\mathbf{A}_{F,S}$ is defined as $\prod_{v\in S}F_v\times\prod_{v\notin S}\mathcal{O}_{F_v}$, and is a topological subring of the global adele ring $\mathbf{A}_F$. For any finite subset $S$ of places of $F$ containing all Archimedean places, define the canonical insertion homomorphism
$$
i_{F,S}:\mathrm{GL}_1(\mathbf{A}_{F,S}\times\widehat{\mathcal{O}}_{\Sigma_F-S})=\mathrm{GL}_1(\mathbf{A}_{F,S})\times\widehat{\mathcal{O}}_{\Sigma_F-S}^{\times}\to\mathrm{GL}_1(\mathbf{A}_F)
\tag{D.1.10.1}
$$
with $\widehat{\mathcal{O}}_{\Sigma_F-S}:=\prod_{v\notin S}\mathcal{O}_{F_v}$. The $S$-idele class group is defined as
$$
C_{F,S}:=(\mathrm{GL}_1(\mathbf{A}_{F,S})\times\widehat{\mathcal{O}}_{\Sigma_F-S}^{\times})/\mathcal{O}_{F,S}^{\times}.
$$
The following result is straightforward.

## PDF page 784

**784** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

Lemma D.1.10.1. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places.*

*(1) The homomorphism $i_{F,S}$ from (D.1.10.1) is continuous injective and open, and is equivariant with respect to the diagonal continuous left-translation action of $\mathcal{O}_{F,S}^{\times}$ on source and target.*

*(2) The Hausdorff locally compact abelian group $\mathrm{GL}_1(\mathbf{A}_F)$ is the direct limit of the Hausdorff locally compact abelian groups $\mathrm{GL}_1(\mathbf{A}_{F,S})$ with transition homomorphisms induced by the $i_{F,S}$.*

*(3) The continuous homomorphism $i_{F,S}$ induces a unique continuous injective open homomorphism:*
$$
i_{F,S}:C_{F,S}\to C_F
\tag{D.1.10.2}
$$
*with finite cokernel $\mathrm{Pic}(\mathcal{O}_{F,S})$ (so it is an isomorphism between identity components $C_{F,S}^0\simeq C_F^0$ for all $S$, and an isomorphism for all sufficiently large $S$).*

D.1.10.1. *Complements on the locally convex topology on Schwartz-Bruhat spaces.* For convenient reference, we wish to record several families of seminorms that define the topology on $\mathcal{S}(G)$ for some classes of Hausdorff locally compact abelian groups $G$. To get started, the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{R})$ (whose construction is reviewed in Definition 2.1.1.4 for $\mathbf{R}^m$ with any $m\ge 1$) is usually defined using sup-norms but it can also be defined by a family of seminorms involving the Fourier transform and $L^2$-norms:

Proposition D.1.10.2. *Let $\mathcal{F}_{\mathbf{R}}:\mathcal{S}(\mathbf{R})\simeq\mathcal{S}(\mathbf{R})$ be the Fourier transform $\mathcal{F}_{\mathbf{R}}(f):x\mapsto\int_{\mathbf{R}}f(y)e^{-2\pi ixy}\,\mathrm{d}y$, and for integers $m,n\ge 0$ let $\nu_{m,n}:\mathcal{S}(\mathbf{R})\to\mathbf{R}_{\ge 0}$ be the seminorm*
$$
\nu_{m,n}(\phi):=\lVert\partial_x^m\mathcal{F}_{\mathbf{R}}(\partial_t^n\phi(t))(x)\rVert_{L^2(\mathbf{R},\mathrm{d}x)}.
\tag{D.1.10.3}
$$
*The family of seminorms $\{\nu_{m,n}\}_{m,n\ge 0}$ defines the usual locally convex topology on $\mathcal{S}(\mathbf{R})$.*

*In particular, for a subset $B\subset\mathcal{S}(\mathbf{R})$ to be bounded in the topological vector space $\mathcal{S}(\mathbf{R})$ it is necessary and sufficient that for each pair of integers $m,n\ge 0$ the subset*

$$
\nu_{m,n}(B)\subset\mathbf{R}_{\ge 0}
$$

*is bounded.*

Proof. The assertion on boundedness within $\mathcal{S}(\mathbf{R})$ follows from the rest because by [Scha, Ch. IV, 3.3] boundedness for a subset of a Hausdorff locally convex topological vector space is the same as weak boundedness (i.e., boundedness in the weak topology defined by continuous linear functionals).

By the usual identity for pulling a derivative operator out of a Fourier transform [Fol, Thm. 8.22(d)], for every $\phi\in\mathcal{S}(\mathbf{R})$ we have
$$
\nu_{m,n}(\phi)=(2\pi)^m\lVert x^m\partial_x^n\phi(x)\rVert_{L^2(\mathbf{R},\mathrm{d}x)}.
$$
Thus, for every integer $N\ge 1$ we have
$$
\nu_{m,n}(\phi)\le (2\pi)^m\lVert(1+|x|)^m\partial_x^n\phi(x)\rVert_{L^2(\mathbf{R},\mathrm{d}x)}\le (2\pi)^m\left(\int_{\mathbf{R}}\frac{1}{(1+|x|)^{2N}}\,\mathrm{d}x\right)^{1/2}\sup_{x\in\mathbf{R}}(1+|x|)^{m+N}|\partial_x^n\phi(x)|.
$$
In particular, since the seminorms $\nu'_{m,n}(\phi):=\sup_{x\in\mathbf{R}}|(1+|x|)^m\partial_x\phi(x)|$ generate the topology of $\mathcal{S}(\mathbf{R})$, each seminorm $\nu_{m,n}$ is continuous on $\mathcal{S}(\mathbf{R})$ for each integer $m,n\ge 0$. Thus, the family of seminorms $\{\nu_{m,n}\}_{m,n\ge 0}$ induces on $\mathcal{S}(\mathbf{R})$ a topology that is coarser than the usual topology on $\mathcal{S}(\mathbf{R})$ (defined in Definition 2.1.1.4).

## PDF page 785

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **785**

Since $\mathcal{F}_{\mathbf{R}}:\mathcal{S}(\mathbf{R})\simeq\mathcal{S}(\mathbf{R})$ is a topological automorphism, the identity for passing a derivative inside a Fourier transform implies that the topology on $\mathcal{S}(\mathbf{R})$ is also defined by the family of seminorms
$$
\sup_{x\in\mathbf{R}}|\partial_x^m\mathcal{F}_{\mathbf{R}}(\partial_t^n\phi(t))(x)|=\sup_{x\in\mathbf{R}}|\mathcal{F}_{\mathbf{R}}((-2\pi it)^m\partial_t^n\phi(t))(x)|
\tag{D.1.10.4}
$$
$$
\le (2\pi)^m\int_{\mathbf{R}}|t^m\partial_t^n\phi(t)|\,\mathrm{d}t\le (2\pi)^m\int_{\mathbf{R}}|(1+|t|)^m\partial_t^n\phi(t)|\,\mathrm{d}t.
$$
The final integral is equal to
$$
\int_{\mathbf{R}}\left|\frac{(1+|t|)^{m+N}\partial_t^n\phi(t)}{(1+|t|)^N}\right|\,\mathrm{d}t\le\left(\int_{\mathbf{R}}\frac{1}{(1+|t|)^{2N}}\,\mathrm{d}t\right)^{1/2}\lVert(1+|t|)^{m+N}\partial_t^n\phi\rVert_{L^2(\mathbf{R},\mathrm{d}x)}
\tag{D.1.10.5}
$$
$$
\le C_N\sum_{1\le k\le m+N}(2\pi)^{-k}\binom{m+N}{k}\nu_{k,n}(\phi)
$$
for
$$
C_N:=\left(\int_{\mathbf{R}}\frac{1}{(1+|t|)^{2N}}\,\mathrm{d}t\right)^{1/2}.
$$
Thus, by using $N=1$ (or any fixed choice of $N\ge 1$) we see that the topology defined by the $\nu_{m,n}$'s is also finer than the usual topology on $\mathcal{S}(\mathbf{R})$, so the two topologies coincide. $\square$

Next, we recall some families of seminorms using $L^p$ for $1\le p<\infty$ in place of $L^{\infty}$ to define the topology on $\mathcal{S}(\mathbf{R}^m)$ for $m\ge 1$, as well as an analogue for $\mathcal{S}(\mathbf{T}^n)$ for $n\ge 1$. This will in turn lead to a version for $\mathcal{S}(G)$ for "sufficiently large" elementary abelian Lie group quotients $G$ of the idele class group $C_F$ and the $S$-idele class group $C_{F,S}$ for a number field $F$.

Example D.1.10.3. The Hausdorff locally convex topology on $\mathcal{S}(\mathbf{R}^m)$ in Definition D.1.3.1 (with $r,n=0$ there) is defined by the seminorms
$$
p_{\alpha,\beta}(f):=\sup_{x\in\mathbf{R}^m}|x^{\alpha}\partial_x^{\beta}f(x)|
\tag{D.1.10.6}
$$
for $\alpha,\beta\in\mathbf{N}^m$. It is clearly equivalent to use the slightly modified family of seminorms $\{\lVert\cdot\rVert_{\alpha,\beta}\}$ from (2.1.1.3) for $\alpha,\beta\in\mathbf{N}^m$ (this is the special case of (D.1.3.8) with $r,n=0$). The topology is also defined by each of the following families based on integrals (for a proof see [KG, Part I, Ch. IV, Thm. 29, pp. 72-4]:

(1) for $\alpha,\beta\in\mathbf{N}^m$,
$$
p'_{\alpha,\beta}(f):=\lVert x^{\alpha}\partial_x^{\beta}f(x)\rVert_{L^1(\mathbf{R}^m,\mathrm{d}x)};
\tag{D.1.10.7}
$$

(2) for $\alpha,\beta\in\mathbf{N}^m$ and fixed $1<p<\infty$,
$$
p''_{\alpha,\beta,p}(f):=\lVert x^{\alpha}\partial_x^{\beta}f(x)\rVert_{L^p(\mathbf{R}^m,\mathrm{d}x)}
\tag{D.1.10.8}
$$
(the proof of equality of topologies in [KG, Part I, Ch. IV, Thm. 29, pp. 72-4] treats $p=2$, but the same method adapts readily to any $1<p<\infty$).

Example D.1.10.4. For $\mathbf{T}=\mathbf{R}/\mathbf{Z}$, the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{T}^n)=C^{\infty}(\mathbf{T}^n)$ in Definition D.1.3.1 (with $m,r=0$ there) is defined by the seminorms
$$
p_{\beta}(f):=\sup_{z\in\mathbf{T}^n}|\partial_z^{\beta}f(z)|
\tag{D.1.10.9}
$$
for $\beta\in\mathbf{N}^n$. The Sobolev Inequality allows this to be replaced with an $L^p$-counterpart for any $1\le p<\infty$. More precisely, for each such fixed $p$ we claim the family of seminorms
$$
p''_{\beta,p}(f):=\lVert\partial_z^{\beta}f(z)\rVert_{L^p(\mathbf{T}^n,\mathrm{d}z)}
\tag{D.1.10.10}
$$

## PDF page 786

**786** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

for $\beta\in\mathbf{N}^n$ defines the same topology on $C^{\infty}(\mathbf{T}^n)$.

For the convenience of the reader, we review the standard argument. Since the volume-1 measure is being used on $\mathbf{T}^n$, clearly $p''_{\beta,p}\le p_{\beta}$. To go in reverse and bound each $p_{\beta}$ from above in terms of finitely many $p_{\alpha,p}$'s for a fixed $1\le p<\infty$, it suffices to treat $p=1$ since Hölder's inequality on the compact $\mathbf{T}^n$ gives
$$
\lVert\phi\rVert_{L^1(\mathbf{T}^n,\mathrm{d}z)}\le\lVert 1\rVert_{L^q(\mathbf{T}^n,\mathrm{d}z)}\lVert f\rVert_{L^p(\mathbf{T}^n,\mathrm{d}z)}=\lVert f\rVert_{L^p(\mathbf{T}^n,\mathrm{d}z)}
$$
where $1/p+1/q=1$.

By the Sobolov Inequality (more precisely, [Wrn, Cor. (b) to 6.22]), for a fixed integer $s>n/2$ there is a constant $C>0$ such that for all $\phi\in C^{\infty}(\mathbf{T}^n)$ we have
$$
\sup_{z\in\mathbf{T}^n}|\phi(z)|\le C\lVert\phi\rVert_s
\tag{D.1.10.11}
$$
where the Sobolev norm $\lVert\cdot\rVert_s$ is defined by
$$
\lVert\phi\rVert_s^2:=\sum_{\xi\in\mathbf{Z}^n}(1+|\xi|^2)^s|\widehat{\phi}(\xi)|^2.
$$
Clearly $|\widehat{\phi}(0)|\le\lVert\phi\rVert_{L^1(\mathbf{T}^n,\mathrm{d}z)}$. For each nonzero $\xi\in\mathbf{Z}^n$ and a fixed integer $N\ge 1$ (we will soon require $N\ge s+(n+1)/2$) and an index $j$ (depending on $\xi$) such that $\lVert\xi\rVert_{\sup}=|\xi_j|$ we have via integration by parts along the $j$th factor $\mathbf{T}$ of $\mathbf{T}^n$ that
$$
\widehat{\phi}(\xi)=\frac{1}{(2\pi i\xi_j)^N}\widehat{\partial_{z_j}^N\phi}(\xi).
$$
Since the Fourier coefficients are each bounded above by the $L^1$-norm, for a constant $C_n$ satisfying $|x|\le C_n|x|_{\sup}$ for all $x\in\mathbf{R}^n$ we have
$$
|\widehat{\phi}(\xi)|\le\left(\frac{C_n}{2\pi|\xi|}\right)^N\max_{|\beta|=N}\lVert\partial_z^{\beta}\phi\rVert_{L^1(\mathbf{T}^n,\mathrm{d}z)}
$$
(with the multi-index $\beta\in\mathbf{N}^n$ varying with degree $N$). Thus, requiring $N\ge s+(n+1)/2$, we have
$$
\lVert\phi\rVert_s^2\le\lVert\phi\rVert_{L^1(\mathbf{T}^n,\mathrm{d}z)}^2+\left(\frac{C_n}{2\pi}\right)^{2N}\left(\sum_{\xi\in\mathbf{Z}^n-\{0\}}\frac{(1+|\xi|^2)^s}{|\xi|^{2N}}\right)\max_{|\beta|=N}\lVert\partial_z^{\beta}\phi\rVert_{L^1(\mathbf{T}^n,\mathrm{d}z)}^2
$$
where the sum over $\xi\in\mathbf{Z}^n-\{0\}$ is finite since $2N-2s\ge n+1$. Feeding this into (D.1.10.11), controlling the $L^1$-norms of all degree-$N$ partials of $\phi\in C^{\infty}(\mathbf{T}^n)$ controls $\phi$ uniformly pointwise over $\mathbf{T}^n$ as desired.

Example D.1.10.5. The Hausdorff locally convex topology on $\mathcal{S}(\mathbf{Z}^r)$ in Definition D.1.3.1 (with $m,n=0$ there) is defined by the family of seminorms
$$
p_{\gamma}(f):=\sup_{a\in\mathbf{Z}^r}|a^{\gamma}f(a)|
\tag{D.1.10.12}
$$
for $\gamma\in\mathbf{N}^r$. For a fixed integer $1\le p<\infty$, we claim that the topology is also defined by the family of seminorms
$$
p_{\gamma,p}(f)=\lVert a^{\gamma}f(a)\rVert_{L^p(\mathbf{Z}^r)}:=\left(\sum_{a\in\mathbf{Z}^r}|a^{\gamma}f(a)|^p\right)^{1/p}.
$$
Clearly $p_{\gamma}\le p_{\gamma,p}$ for each $\gamma$ (termwise domination), so it remains to show that each $p_{\gamma,p}$ is controlled by the $p_{\alpha}$'s for finitely many $\alpha\in\mathbf{N}^r$ (depending on $\gamma$).

Adapting the argument used for $\mathbf{R}^m$ in Example D.1.10.3 via Hölder's inequality, we multiply and divide by $(1+|a|^2)^r$ (whose reciprocal has finite $L^p$-norm since $2r\ge r+1$) to get
$$
p_{\gamma,p}(f)\le\lVert(1+|a|^2)^{-r}\rVert_{L^p(\mathbf{Z}^r)}\sup_{a\in\mathbf{Z}^r}|(1+|a|^2)^ra^{\gamma}f(a)|
$$

## PDF page 787

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **787**

with finite $L^p$-norm multiplier having nothing to do with $f$. Via binomial expansion, the supremum on the right side is controlled by the $p_{\alpha}(f)$'s for finitely many $\alpha$'s depending only on $\gamma$ (and $r$). This completes the proof.

The three preceding examples are the key ingredients in the proof of a coordinate-free variant of Lemma D.1.3.4 incorporating a version with $L^q$-norms for $1\le .q<\infty$, inspired by [Wa, §3, p. 312].

Proposition D.1.10.6. *Let $G$ be an elementary abelian Lie group. For each invariant differential operator $D'\in\mathrm{Diff}(\widehat{G})$ on the dual group $\widehat{G}$, let $p(D')\in C^{\infty}(G)$ be the associated symbol (smoothness via Lemma D.1.6.19(1)). The locally convex topology on $\mathcal{S}(G)$ is defined by each of the following families of seminorms:*

*(1) $\lVert p(D')\cdot D(f)\rVert_{\sup}$ for varying $D\in\mathrm{Diff}(G)$ and $D'\in\mathrm{Diff}(\widehat{G})$,*

*(2) for a fixed integer $1\le q<\infty$, $\lVert p(D')\cdot D(f)\rVert_{L^q(G)}$ for varying $D\in\mathrm{Diff}(G)$ and $D'\in\mathrm{Diff}(\widehat{G})$,*

*(3) for a basis $\{\partial_j\}_{1\le j\le d}$ of $\mathcal{L}(G)=\mathcal{L}(G^0)$ and a basis $\{\partial'_i\}_{1\le i\le d'}$ of $\mathcal{L}(\widehat{G})$, $\lVert p(\partial'^{\beta})\cdot\partial^{\alpha}(f)\rVert_{\sup}$ for $\alpha\in\mathbf{N}^d$, $\beta\in\mathbf{N}^{d'}$.*

*(4) for a fixed integer $1\le q<\infty$, a basis $\{\partial_j\}_{1\le j\le d}$ of $\mathcal{L}(G)=\mathcal{L}(G^0)$, and a basis $\{\partial'_i\}_{1\le i\le d'}$ of $\mathcal{L}(\widehat{G})$, $\lVert p(\partial'^{\beta})\cdot\partial^{\alpha}(f)\rVert_{L^q(G)}$ for $\alpha\in\mathbf{N}^d$, $\beta\in\mathbf{N}^{d'}$.*

By Lemma D.1.6.16, for any $f\in\mathcal{S}(G)$ the sup-norms in (1) and (3) are finite. Likewise, by Remark D.1.6.20 we see that $p(D')\cdot D(f)\in\mathcal{S}(G)$ for all pairs $(D,D')$, so the $L^q$-norms in (2) and (4) are finite.

Proof. Since the formation of $p(D')$ is linear in $D'$, it is clear that (1) and (3) define the same locally convex topology on $\mathcal{S}(G)$, as do (2) and (4). In particular, (3) and (4) are independent of the choice of such bases and it suffices to show (3) and (4) define the usual topology on $\mathcal{S}(G)$ for some common choice of such bases. Fixing an isomorphism
$$
G\simeq\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F
$$
for integers $m,n,r\ge 0$ and a finite abelian group $F$, we have compatibly
$$
\widehat{G}\simeq\mathbf{R}^m\times\mathbf{Z}^n\times\mathbf{T}^r\times\widehat{F}.
$$
For (3) we use the basis of $\mathcal{L}(G)=\mathcal{L}(\mathbf{R}^m\times\mathbf{T}^n)$ corresponding to the standard partial derivatives along the factors $\mathbf{R}$ of $\mathbf{R}^m$ and $\mathbf{T}=\mathbf{R}/\mathbf{Z}$ of $\mathbf{T}^n$, and for (4) we use the basis of $\mathcal{L}(\widehat{G})=\mathcal{L}(\mathbf{R}^m\times\mathbf{T}^r)$ corresponding to the standard partial derivatives along the factors $\mathbf{R}$ of $\mathbf{R}^m$ and $\mathbf{T}=\mathbf{R}/\mathbf{Z}$ of $\mathbf{T}^r$.

By Example D.1.6.12 and Lemma D.1.6.13, in terms of the "coordinates" $(x,z,a,b)\in\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$ we see that the operators $p(\partial'^{\beta})\cdot\partial^{\alpha}$ for varying $\alpha$ and $\beta$ are exactly $\mathbf{C}^{\times}$-multiples of the operators
$$
x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}:\mathcal{S}(G)\to\mathcal{S}(G).
$$
That (3) defines the usual topology on $\mathcal{S}(G)$ now follows from (D.1.3.9). It remains to prove that for each $1\le q<\infty$, the seminorms
$$
f\mapsto\lVert x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}(f)\rVert_{L^q(G)}
$$
on $\mathcal{S}(G)$ define the usual topology on $\mathcal{S}(G)$.

We shall do this by using each of Examples D.1.10.3–D.1.10.5. First we show that each sup-norm
$$
\lVert x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}(f)\rVert_{\sup}
$$
over $G$ is bounded above by a sum of $\mathbf{R}_{>0}$-multiples of finitely many $L^q$-seminorms over $G$ (with the constant multipliers and $L^q$-seminorms depending only on $\gamma$, $\delta$, $\lambda$, and $\mu$, not on $f$). Since
$$
\sup_{(x,z,a,b)}g(x,z,a,b)=\sup_{(z,a,b)}(\sup_x g(x,z,a,b)),
$$

## PDF page 788

**788** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

for each $(z,a,b)$ we view $x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}f(x,z,a,b)$ as an element of $\mathcal{S}(\mathbf{R}^m)$ and apply Example D.1.10.3 to get a finite set of pairs of multi-indices $(\gamma',\lambda')$ and positive constants $C_{\gamma',\delta'}$ depending only on $(\gamma,\lambda)$ so that
$$
\sup_{(x,z,a,b)}|x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}f(x,z,a,b)|\le\sup_{(z,a,b)}\sum_{(\gamma',\lambda')}C_{\gamma',\lambda'}\left(\int_{\mathbf{R}^m}|x^{\gamma'}\partial_x^{\lambda'}a^{\delta}\partial_z^{\mu}f(x,z,a,b)|^q\,\mathrm{d}x\right)^{1/q}
\tag{D.1.10.13}
$$
$$
\le\sum_{(\gamma',\lambda')}C_{\gamma',\lambda'}\left(\int_{\mathbf{R}^m}\sup_{(z,a,b)}|\partial_z^{\mu}a^{\delta}x^{\gamma'}\partial_x^{\lambda'}f(x,z,a,b)|^q\,\mathrm{d}x\right)^{1/q},
$$
where the sup inside the integral is a continuous function of $x\in\mathbf{R}^m$ since $z$ varies over the compact $\mathbf{T}^n$.

Writing $\sup_{(z,a,b)}=\sup_{(a,b)}\sup_z$, we next apply Example D.1.10.4 to get a finite set of multi-indices $\mu'$ and positive constants $C_{\mu'}$ depending only on $\mu$ so that the integrand at the end of (D.1.10.13) satisfies
$$
\sup_{(z,a,b)}|\partial_z^{\mu}a^{\delta}x^{\gamma'}\partial_x^{\lambda'}f(x,z,a,b)|^q\le\sup_{(a,b)}\sum_{\mu'}C_{\mu'}\int_{\mathbf{T}^n}|\partial_z^{\mu'}a^{\delta}x^{\gamma'}\partial_x^{\lambda'}f(x,z,a,b)|^q\,\mathrm{d}z
\tag{D.1.10.14}
$$
$$
\le\sum_{\mu'}C_{\mu'}\int_{\mathbf{T}^n}\sup_{(a,b)}|a^{\delta}\partial_z^{\mu'}x^{\gamma'}\partial_x^{\lambda'}f(x,z,a,b)|^q\,\mathrm{d}z.
$$
Thus,
$$
\sup_{(x,z,a,b)}|x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}f(x,z,a,b)|\le\sum_{(\gamma',\lambda')}C_{\gamma',\lambda'}\left(\sum_{\mu'}C_{\mu'}\int_{\mathbf{R}^m\times\mathbf{T}^n}\sup_{(a,b)}|a^{\delta}\partial_z^{\mu'}x^{\gamma'}\partial_x^{\lambda'}f(x,z,a,b)|^q\,\mathrm{d}z\,\mathrm{d}x\right)^{1/q}
$$
(the inner supremum over the countably many pairs $(a,b)$ is measureable).

Now by Example D.1.10.5, there is a finite set of multi-indices $\delta'$ and positive constants $C_{\delta'}$ depending only on $\delta$ so that
$$
\sup_{(a,b)}|a^{\delta}\partial_z^{\mu'}x^{\gamma'}\partial_x^{\lambda'}f(x,z,a,b)|^q\le\sup_b\sum_{\delta'}C_{\delta'}\int_{\mathbf{Z}^r}|a^{\delta'}\partial_z^{\mu'}x^{\gamma'}\partial_x^{\lambda'}f(x,z,a,b)|^q\,\mathrm{d}a
$$
(counting measure on $\mathbf{Z}^r$). Hence, the left side of (D.1.10.13) is bounded above by
$$
\sum_{(\gamma',\lambda')}C_{\gamma',\lambda'}\left(\sum_{(\mu',\delta')}C_{\mu'}C_{\delta'}\int_{\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r}\sup_{b\in F}|a^{\delta'}\partial_z^{\mu'}x^{\gamma'}\partial_x^{\lambda'}f(x,z,a,b)|^q\,\mathrm{d}a\,\mathrm{d}z\,\mathrm{d}x\right)^{1/q}.
$$
For any non-negative function $h$ on $F$ clearly $\sup_{b\in F}h(b)\le\sum_{b\in F}h(b)$, so we finally obtain
$$
\lVert x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}(f)\rVert_{\sup}\le\sum_{(\gamma',\lambda')}C_{\gamma',\lambda'}\left(\sum_{(\mu',\delta')}C_{\mu'}C_{\delta'}\lVert a^{\delta'}\partial_z^{\mu'}x^{\gamma'}\partial_x^{\lambda'}(f)\rVert_{L^q(G)}^q\right)^{1/q}
$$
where the finitely many multi-indices over which we sum and the positive constant multipliers on the right side only depend on the multi-indices on the left side. This shows that each of the sup-seminorms on $G$ is controlled by finitely many of the $L^q$-seminar's over $G$.

To go in reverse, we want to control each choice of $L^q$-seminorm on $\mathcal{S}(G)$ in terms of finitely many sup-seminorms. Fix one such $L^q$-seminorm $\nu$. We will use the isomorphism
$$
\mathcal{S}(G)\simeq\mathcal{S}(\mathbf{R}^m)\widehat{\otimes}_{\pi}\mathcal{S}(\mathbf{T}^n)\widehat{\otimes}_{\pi}\mathcal{S}(\mathbf{Z}^r)\widehat{\otimes}_{\pi}\mathcal{S}(F)
$$
from Lemma D.1.3.7(2). By Examples D.1.10.3–D.1.10.5 (along with the easy case of the finite-dimensional $\mathcal{S}(F)=\mathbf{C}^F$), on each of the four factor spaces in this completed tensor product the topology is defined by the corresponding family of $L^q$-norms. Thus, a base of $0$-neighborhoods in the uncompleted tensor product

## PDF page 789

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **789**

consists of convex combinations of elementary tensors whose constituent vectors have any specified finite collection of $L^q$-seminorms below any desired positive bound.

Hence, by the $L^q$-triangle inequality and Fubini's Theorem, in the topology of $\mathcal{S}(G)$ each $f\in\mathcal{S}(G)$ is an infinite series $\sum_{k\ge 0}f_k$ where every $f_k$ is a finite sum of elementary tensors and for every $k\ge 1$ we have $\nu(f_k)\le 1/2^k$. It follows that the infinite series is also $\nu$-convergent to $f$. Successive use of the explicit description of tensor product seminorms [Scha, Ch. III, 6.3] shows that on finite sums of elementary tensors we have
$$
\lVert x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}(\cdot)\rVert_{L^q(G)}\le\lVert x^{\gamma}\partial_x^{\lambda}(\cdot)\rVert_{L^q(\mathbf{R}^m)}\otimes_{\pi}\lVert\partial_z^{\mu}(\cdot)\rVert_{L^q(\mathbf{T}^n)}\otimes_{\pi}\lVert a^{\delta}(\cdot)\rVert_{L^q(\mathbf{Z}^r)}\otimes_{\pi}\lVert\cdot\rVert_{L^q(F)}.
$$
But $\nu(f)$ is the limit of $\nu(\sum_{k\le N}f_k)$ as $N\to\infty$ (with each partial sum $\sum_{k\le N}f_k$ a finite sum of elementary tensors), so we can pass to the limit and get
$$
\lVert x^{\gamma}a^{\delta}\partial_x^{\lambda}\partial_z^{\mu}(\cdot)\rVert_{L^q(G)}\le\lVert x^{\gamma}\partial_x^{\lambda}(\cdot)\rVert_{L^q(\mathbf{R}^m)}\widehat{\otimes}_{\pi}\lVert\partial_z^{\mu}(\cdot)\rVert_{L^q(\mathbf{T}^n)}\widehat{\otimes}_{\pi}\lVert a^{\delta}(\cdot)\rVert_{L^q(\mathbf{Z}^r)}\widehat{\otimes}_{\pi}\lVert\cdot\rVert_{L^q(F)}.
$$
In particular, the seminorms on the left side are all continuous on $\mathcal{S}(G)$. This proves that the $L^q$-seminorms on $\mathcal{S}(G)$ are each controlled by finitely many of the usual sup-norms on $\mathcal{S}(G)$, as desired. $\square$

D.1.10.2. *Families of continuous seminorms on $\mathcal{S}(C_F)$.* Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We denote by $C_F^1$, respectively $C_{F,S}^1$, the closed subgroups of idele classes of idelic norm 1 of the Hausdorff locally compact abelian groups $C_F$, respectively $C_{F,S}$ of idele classes. $C_F^1$ and $C_{F,S}^1$ are compact Hausdorff (see Theorem A.1.4.3).

The following are families of seminorms that generate the Hausdorff locally convex topology on $\mathcal{S}(C_{F,S}^0)$ and $\mathcal{S}(C_F^0)$, where $G^0$ denotes the identity component of a topological group $G$.

Proposition D.1.10.7 (Fundamental family of continuous seminorms on $\mathcal{S}(C_F^0)$). *Let $F$ be a number field. Let $\tau$ be a continuous homomorphic section to the idelic norm. Let $k\subset C_F^0$ be a compact subgroup (so $k\subset(C_F^0)^1=(C_F^1)^0$) with compactly generated orthogonal $k^{\perp}$ in the dual group of $C_F^0$.*

*If $k$ is sufficiently small then there exist continuous 1-parameter subgroups $\gamma_j:\mathbf{R}\to C_F^1$, $1\le j\le r_1+2r_2-1$ such that the set of seminorms*
$$
p_{r,m,\alpha}(f):=\sup_{g\in C_F^0/k}|\partial_{\tau}^m(\partial_{\gamma_1}^{\alpha_1}\cdots\partial_{\gamma_{r_1+2r_2-1}}^{\alpha_{r_1+2r_2-1}})(f)(g)(1+|\log|g|_F|^r)|
\tag{D.1.10.15}
$$
*for $r\in\mathbf{N}$, $m\in\mathbf{N}$, $\alpha\in\mathbf{N}^{r_1+2r_2-1}$ generate the Schwartz-Bruhat topology on $\mathcal{S}(k,C_F^0)$.*

Remark D.1.10.8. We note that the image of each $\gamma_j$ from Proposition D.1.10.7 is contained in $(C_F^1)^0$ since it is a connected subgroup of $C_F^1$.

Proof. Upon choosing a continuous homomorphic section $\tau$ to the idelic norm, we have an induced isomorphism of Hausdorff locally compact abelian groups:
$$
\overline{\theta}_{\tau}:\mathbf{R}_{>0}\times C_F^1\to C_F
\tag{D.1.10.16}
$$
defined as $\overline{\theta}_{\tau}(t,g):=\tau(t)g$.

By [AT, Ch. IX, §1. Thm. 3], the compact norm-1 subgroup $G\subset C_F^0$ is $(\mathbf{R}/\mathbf{Z})^{r_2}\times\mathbf{S}^{r_1+r_2-1}$ where $\mathbf{S}=\lim_{x\mapsto Nx}\mathbf{R}/\mathbf{Z}\simeq\mathbf{A}_{\mathbf{Q}}/\mathbf{Q}$. Since $G$ is compact, so all elementary abelian Lie group quotients of $G$ are compact, $\mathcal{S}(G)=C^{\infty}(G)$. Thus, Lemma D.1.8.1(1) identifies the Schwartz-Bruhat space $\mathcal{S}(G)=C^{\infty}(G)$ with

$$
C^{\infty}((\mathbf{R}/\mathbf{Z})^{r_2})\overline{\otimes} C^{\infty}(\mathbf{S}^{r_1+r_2-1})
$$

where $C^{\infty}((\mathbf{R}/\mathbf{Z})^{r_2})$ is equipped with the Fréchet topology of uniform convergence of functions and their derivatives or arbitrary order.

## PDF page 790

**790** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

Via the compatibility of $\overline{\otimes}$ with countable strict inductive limits in Proposition C.2.3.13(2), we claim that that for every integer $r\ge 0$ (such as $r=r_1+r_2-1$) the space $C^{\infty}(\mathbf{S}^r)$ is naturally identified with the countable strict locally convex inductive limit of copies of $C^{\infty}((\mathbf{R}/\mathbf{Z})^r)$ under the topological embedding transition operators induced by the positive integer-multiplication maps on $(\mathbf{R}/\mathbf{Z})^r$. To see this, we may pass to the case $r=1$ to reduce to checking that every smooth function on $\mathbf{S}$ factors through some finite layer $\mathbf{R}/\mathbf{Z}$ in the inverse limit defining $\mathbf{S}$. By definition, smooth functions on $\mathbf{S}$ are $K$-invariant for a proper compact subgroup $K\subset\mathbf{S}$ such that the nonzero orthogonal $K^{\perp}\subset\widehat{\mathbf{S}}=\mathbf{Q}$ is finitely generated, hence contained inside $(1/N)\mathbf{Z}$ for some $N\ge 1$. The latter provides a finite layer through which the $K$-invariant smooth functions factor, as desired.

Passing to a sufficiently large finitely generated subgroup $k^{\perp}\subset\widehat{G}=\mathbf{Z}^{r_2}\times\mathbf{Q}^{r_1+r_2-1}$ (a cofinal system of which is given by $\mathbf{Z}^{r_2}\times(1/N)\mathbf{Z}^{r_1+r_2-1}$) corresponds to passing to a sufficiently small compact subgroup $k\subset G$ with finitely generated orthogonal, so we may assume $k$ is the closed subgroup of $\mathbf{S}^{r_1+r_2-1}$ corresponding to kernel of projection to a finite layer $(\mathbf{R}/\mathbf{Z})^{r_1+r_2-1}$.

The completed inductive tensor product $\mathcal{S}((\mathbf{R}/\mathbf{Z})^{r_2})\overline{\otimes}\mathcal{S}(k,\mathbf{S}^{r_1+r_2-1})$, which by Corollary C.2.3.12 is topologically isomorphic to the completed projective tensor product $\mathcal{S}((\mathbf{R}/\mathbf{Z})^{r_2})\widehat{\otimes}_{\pi}\mathcal{S}(k,\mathbf{S}^{r_1+r_2-1})$, is therefore linearly topologically isomorphic to $\mathcal{S}(k,G)$ equipped with the topology of uniform convergence of functions and their directional derivatives of arbitrary order along the coordinate continuous 1-parameter subgroups induced by the continuous homomorphism
$$
\mathbf{R}^{r_2}\times(\mathbf{R}^{r_1+r_2-1}\times\{0\})\to(\mathbf{R}/\mathbf{Z})^{r_2}\times(\mathbf{R}^{r_1+r_2-1}\times\widehat{\mathbf{Z}})\to(\mathbf{R}/\mathbf{Z})^{r_2}\times\mathbf{S}^{r_1+r_2-1}
$$
further composed with the continuous quotient homomorphism $(\mathbf{R}/\mathbf{Z})^{r_2}\times\mathbf{S}^{r_1+r_2-1}\to(\mathbf{R}/\mathbf{Z})^{r_2}\times(\mathbf{S}^{r_1+r_2-1}/k)$ with $\mathbf{S}^{r_1+r_2-1}/k=(\mathbf{R}/\mathbf{Z})^{r_1+r_2-1}$. These induce continuous 1-parameter subgroups of $C_F^1$.

Since $\mathcal{S}(C_F^0/k)$ is linearly and topologically isomorphic to $\mathcal{S}(\mathbf{R}_{>0})\overline{\otimes}\mathcal{S}((C_F^1)^0/k)$ (equal to the completed projective tensor product since $(C_F^1)^0/k$ is an elementary abelian Lie group), we are reduced to showing that the Hausorff locally convex topology on $\mathcal{S}(\mathbf{R}_{>0})$ is induced by the set of seminorms
$$
p_{r,m}(f):=\sup_{t\in\mathbf{R}_{>0}}|((t\partial_t)^mf(t))(1+|\log(t)|^r)|.
$$
Upon performing the change of variables $t=e^x$ ($x\in\mathbf{R}$), the equality with the topology on $\mathcal{S}(\mathbf{R}_{>0})$ follows from Example D.1.10.3. $\square$

Proposition D.1.10.9 (Fundamental family of continuous seminorms on $\mathcal{S}(k,C_F)$). *Let $F$ be a number field. Let $\gamma_1,\dots,\gamma_{r_1+2r_2-1}$ be continuous 1-parameter subgroups of $C_F^1$ as in Proposition D.1.10.7. Let $\tau$ be a choice of continuous homomorphic section to the idelic norm.*

*For $k\subset\Gamma$ a sufficiently small compact subgroup whose annihilator is open and compactly generated in $\widehat{C_F}$, the following sets of seminorms on $\mathcal{S}(k,C_F)$ generate the subspace topology:*

*(1) for varying $r\in\mathbf{N}$, $m\in\mathbf{N}$, $\alpha\in\mathbf{N}^{r_1+2r_2-1}$, and a fixed real number $p\ge 1$, $\{\nu_{r,m,\alpha}^p\}$ defined on $\mathcal{S}(k,C_F)$ by*
$$
\nu_{r,m,\alpha}^p(f):=\left(\int_{\mathbf{R}_{>0}}\left(\int_{C_F^1}|(t\partial_t)^m(\partial_{\gamma_1}^{\alpha_1}\cdots\partial_{\gamma_{r_1+2r_2-1}}^{\alpha_{r_1+2r_2-1}})(f)(\tau(t)g)(1+|\log(t)|^r)|^p\,\mathrm{d}\overline{\mu}_1(g)\right)\frac{\mathrm{d}t}{t}\right)^{1/p}.
\tag{D.1.10.17}
$$

*(2) For the above sets of seminorms, the seminorms obtained upon replacing $1+|\log(\cdot)|^r$ by $|\log(\cdot)|^r$.*

*(3) For the above sets of seminorms, the seminorms obtained upon replacing $\{1+|\log(\cdot)|^r\}_{r\in\mathbf{N}}$ by the absolute value of all polynomials in $|\log(t)|$ with $\mathbf{C}$-coefficients and of arbitrary degree.*

Proof. We denote by
$$
D_j:=\partial_{\gamma_j}:\mathcal{S}(C_F)\to\mathcal{S}(C_F)
\tag{D.1.10.18}
$$

## PDF page 791

**D.1. SCHWARTZ-BRUHAT SPACE OF A HAUSDORFF LOCALLY COMPACT ABELIAN GROUP** · **791**

for $1\le j\le r_1+2r_2-1$ the linear differential operators induced by the continuous 1-parameter subgroups $\{\gamma_j\}_{1\le j\le r_1+2r_2-1}$ of $C_F^1\subset C_F$. Since each $a\in\mathcal{L}(C_F)$ takes value in the identity component $C_F^0$, we have $\mathcal{L}(C_F)=\mathcal{L}(C_F^0)$. By [AT, Ch. IX, §1, Thm. 3] we have an isomorphism of topological groups
$$
C_F^0\simeq(\mathbf{R}/\mathbf{Z})^{r_2}\times\mathbf{R}_{>0}\times\mathbf{S}^{r_1+r_2-1}
$$
for $\mathbf{S}=\mathbf{A}_{\mathbf{Q}}/\mathbf{Q}$, so as $\mathbf{R}$-vector spaces we have
$$
\mathcal{L}(C_F^0)\simeq\mathcal{L}((\mathbf{R}/\mathbf{Z})^{r_2})\oplus\mathcal{L}(\mathbf{R}_{>0})\oplus\mathcal{L}(\mathbf{S}^{r_1+r_2-1})
$$
where $\mathcal{L}(\mathbf{S}^{r_1+r_2-1})$ is $\mathbf{R}$-linearly isomorphic to $\mathcal{L}((\mathbf{R}/\mathbf{Z})^{r_1+r_2-1})$ via projection $\mathrm{pr}:\mathbf{S}\to\mathbf{R}/\mathbf{Z}$ to the initial layer since the transition maps among copies of $(\mathbf{R}/\mathbf{Z})^{r_1+r_2-1}$ realizing $\mathbf{S}^{r_1+r_2-1}$ as an inverse limit, are finite-degree covering maps (so inducing $\mathbf{R}$-linear isomorphisms on Lie algebras). In particular, $\dim_{\mathbf{R}}\mathcal{L}(C_F)=1+(r_1+2r_2-1)=[F:\mathbf{Q}]$ and so the $\mathbf{R}$-linearly independent $\{\partial_{\tau},D_j\}_{1\le j\le r_1+2r_2-1}$ are a basis of $\mathcal{L}(C_F)$.

In light of the isomorphism of Hausdorff locally compact abelian groups
$$
\overline{\theta}_{\tau}:\mathbf{R}_{>0}\times C_F^1\to C_F
\tag{D.1.10.19}
$$
induced by the choice $\tau$ of continuous homomorphic section to the idelic norm, to compute the $\mathbf{R}$-linear space of symbols of invariant differential operators on the dual group $C_F$ it is enough to compute the symbols of the linear differential operators on the dual group of $\mathbf{R}_{>0}$, since the dual of the compact $C_F^1$ is discrete (and so has no nonzero invariant differential operator).

We can $k$ small enough so that $C_F^0/k$ has the same dimension as $\mathcal{L}(C_F^0)$ (as we may clearly do). Integrating $k$-invariant functions on $C_F$ and over $C_F/k$ differs only in a constant multiplier by a volume, so via Proposition D.1.10.6 we see that for each real number $p\ge 1$, as we vary $P\in\mathbf{R}[X]$, $m\in\mathbf{N}$, and $\alpha\in\mathbf{N}^{r_1+2r_2-1}$ the associated seminorms
$$
\nu_{P,m,\alpha}^p(f):=\left(\int_{\mathbf{R}_{>0}}\left(\int_{C_F^1}|(t\partial_t)^m(\partial_{\gamma_1}^{\alpha_1}\cdots\partial_{\gamma_{r_1+2r_2-1}}^{\alpha_{r_1+2r_2-1}})(f)(\tau(t)g)|P(\log(t))||^p\,\mathrm{d}\overline{\mu}_1(g)\right)\frac{\mathrm{d}t}{t}\right)^{1/p}
$$
generate the Hausdorff locally convex topology on $\mathcal{S}(C_F)$. That the Schwartz-Bruhat topology on $\mathcal{S}(C_F)$ remains unaltered upon changing the seminorms $\nu_{r,m,\alpha}^p$ into the seminorms from (D.1.10.17), or those obtained upon replacing $(1+|\log(t)|^r)$ from (D.1.10.17) by $|\log(t)|^r$, is a consequence of the triangle inequality for $L^p$-norms. $\square$

D.1.10.3. *Families of continuous seminorms on $\mathcal{S}(C_{F,S})$.* The following is the analog of Proposition D.1.10.9 in the case of $C_{F,S}$, for $S$ a finite set of places of $F$ containing the Archimedean places.

Proposition D.1.10.10 (Fundamental family of continuous seminorms on $\mathcal{S}(k,C_{F,S})$). *Let $F$ be a number field, $S$ a finite set of places containing the Archimedean places. Let $\gamma_1,\dots,\gamma_{r_1+2r_2-1}$ be the continuous 1-parameter subgroups of the open subgroup $C_{F,S}^1\subset C_F^1$ of finite index provided by Proposition D.1.10.7. Let $\tau$ be a continuous homomorphic section to the $S$-idelic norm.*

*For $k\subset C_{F,S}$ a sufficiently small compact subgroup whose open annihilator is compactly generated in $\widehat{C_{F,S}}$, the following sets of seminorms on $\mathcal{S}(k,C_{F,S})$ generate the usual topology:*

*(1) for varying $r\in\mathbf{N}$, $m\in\mathbf{N}$, $\alpha\in\mathbf{N}^{r_1+2r_2-1}$, and a fixed real number $p\ge 1$, $\{\nu_{r,m,\alpha}^p\}$ on $\mathcal{S}(k,C_{F,S})$ defined by*
$$
\nu_{r,m,\alpha}^p(f):=\left(\int_{\mathbf{R}_{>0}}\left(\int_{C_{F,S}^1}|(t\partial_t)^m(\partial_{\gamma_1}^{\alpha_1}\cdots\partial_{\gamma_{r_1+2r_2-1}}^{\alpha_{r_1+2r_2-1}})(f)(\tau(t)g)(1+|\log(t)|^r)|^p\,\mathrm{d}\overline{\mu}_{S,1}(g)\right)\frac{\mathrm{d}t}{t}\right)^{1/p}.
\tag{D.1.10.20}
$$

*(2) For the above sets of seminorms, the seminorms obtained upon replacing $1+|\log(\cdot)|^r$ by $|\log(\cdot)|^r$.*

## PDF page 792

**792** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

(3) *For the above sets of seminorms, the seminorms obtained upon replacing $\{1+|\log(\cdot)|^r\}_{r\in\mathbf N}$ by the absolute value of the polynomials in $|\log(t)|$ of arbitrary degree.*

The proof of Proposition D.1.10.10 proceeds as for Proposition D.1.10.9, upon noting that we have $C^0_{F,S}=C^0_F$ for all $S$ by Lemma D.1.10.1(3). We further note that the seminorms in (D.1.10.20) agree with the seminorms in (D.1.10.17) for all large enough $S$, since $C_{F,S}=C_F$ for all sufficiently large $S$ by Lemma D.1.10.1(3).

**D.2. Schwartz-Bruhat functions on modulated groups**

In this section we introduce modulated groups, a special case of Hausdorff locally compact abelian groups $G$, unifying examples of interest to this work, such as global and $S$-local idele class groups. This section will enable systematic use of linear and topological properties of the Mellin transform for $G$ equipped with a proper continuous surjective homomorphism $|\cdot|_G:G\to\mathbf R_{>0}$; such a $G$ is called $\mathbf R_{>0}$-modulated.

**D.2.1. Preparations on modulated groups.** The *compact* Hausdorff abelian group $C^1_F$ acts on $\mathcal S(C_F)$ by continuous left-translation: $(g.f)(x)=f(g^{-1}x)$ (for the continuity property more broadly. See Proposition D.1.9.2).

The same holds for the compact Hausdorff abelian groups $C^1_{F,S}$ acting on $\mathcal S(C_{F,S})$, and $J^1_{F,S}$ acting on $\mathcal S(J_{F,S})$. The Hausdorff locally compact abelian groups $C_F$, $C_{F,S}$ and $J_{F,S}$ are three examples of “modulated” groups. This concept was discussed by Weil in [Weil-e, §3, p. 6] with the aim of treating certain representation-theoretic preparations towards the explicit formulas for Artin $L$-functions in a unified manner, encompassing Weil groups.

D.2.1.1. *Modulated groups: definition and canonical measure.* Let $G$ be a second-countable Hausdorff locally compact abelian group equipped with a continuous proper homomorphism

$$
|\cdot|_G:G\to\mathbf R_{>0}
$$

(so $G^1:=\ker(|\cdot|_G)$ is compact). For a choice of continuous character $\omega\in\widehat{G^1}$, let $\mathrm H^0(\omega,\mathcal S(G))\subset\mathcal S(G)$ denote the subspace of Schwartz-Bruhat functions $f$ on $G$ that are $\omega$-homogenous in the sense that $g.f=\omega(g)f$ for all $g\in G^1$; this is a closed subspace since the $G$-action on $\mathcal S(G)$ is continuous.

Recall from Theorem D.1.5.7 that the Hausdorff locally convex topological vector space $\mathcal S(G)$ is complete, and by Proposition D.1.9.2 every compact subset $K\subset G$ acts uniformly continuously on $\mathcal S(G)$; in particular, the $G^1$-action on $\mathcal S(G)$ is uniformly continuous. This allows us to build averaging operators over $G^1$ valued in $\mathcal S(G)$ via Pettis integration, as follows.

Define the $\mathbf C$-linear map

$$
\Phi_{G,\omega}:\mathcal S(G)\to\mathrm H^0(\omega,\mathcal S(G)) \tag{D.2.1.1}
$$

by

$$
\Phi_{G,\omega}(f)(h):=\frac{1}{\mu_1(G^1)}\int_{G^1}\overline{\omega}(g)f(g^{-1}h)\,\mathrm{d}\mu_1(g) \tag{D.2.1.2}
$$

with $\mu_1$ a fixed choice of Haar measure on $G^1$. It is clear from the definition that the function $\Phi_{G,\omega}(f):G\to\mathbf C$ is $\omega$-homogenous, but it is not so obvious that this function on $G$ belongs to $\mathcal S(G)$; this is where Pettis integration enters. We use Lemma 4.3.3.1(1) applied to the compact group $G^1$ acting uniformly continuously on the complete locally convex topological vector space $E=\mathcal S(G)$ via $f\mapsto\overline{\omega}(g)\,g.f$ and the collection of continuous linear functionals $\varphi\in E'$ given by evaluation at points $h\in G$. That is, we have an $\mathcal S(G)$-valued Pettis integral

$$
\Phi_{G,\omega}(f)=\frac{1}{\mu_1(G^1)}\int_{G^1}\langle\overline{\omega}(g)g.f,\cdot\rangle_{E,E'}\,\mathrm{d}\mu_{G^1}(g)\in E\subset (E')^*
$$

## PDF page 793

**D.2. SCHWARTZ-BRUHAT FUNCTIONS ON MODULATED GROUPS** · **793**

whose value at any $h\in G$ is the ordinary integral in (D.2.1.2). The averaging operator $\Phi_{G,\omega}:\mathcal S(G)\to\mathcal S(G)$ over $G^1$ is a continuous projector onto $\mathrm H^0(\omega,\mathcal S(G))$ by Lemma 4.3.3.1(1,2).

DEFINITION D.2.1.1 (Modulated groups). Let $G$ be a second-countable Hausdorff locally compact abelian group. We say $G$ is *modulated* if there is given a non-trivial continuous proper homomorphism

$$
|\cdot|_G:G\to\mathbf R_{>0}. \tag{D.2.1.3}
$$

We call $|\cdot|_G$ the *module* of $G$, and denote by $\Gamma$ the closed image of $|\cdot|_G$ in $\mathbf R_{>0}$. We define:

(1) $G^1:=\ker(|\cdot|_G)$, a the compact subgroup of $G$;

(2) the canonical Haar measure $\mu_{\mathrm{can}}$ on $G$ to be the unique Haar measure on $G$ such that for every real number $\Lambda>1$, upon denoting by $G^{[1/\Lambda,\Lambda]}$ the compact subset of $G$ defined as the pre-image of the compact interval $[1/\Lambda,\Lambda]\subset\mathbf R_{>0}$ under the proper homomorphism $|\cdot|_G$, we have

$$
\mu_{\mathrm{can}}(G^{[1/\Lambda,\Lambda]})=2\log(\Lambda)+O(1) \tag{D.2.1.4}
$$

as $\Lambda\to+\infty$ (such a measure exists because $|\cdot|_G$ is non-trivial).

The condition (D.2.1.4) uniquely determines $\mu_{\mathrm{can}}$, but to see the existence of $\mu_{\mathrm{can}}$ it is useful first to show (as one sees directly in all cases of interest) that $|\cdot|_G$ admits continuous homomorphic sections:

REMARK D.2.1.2. The closed subgroup $\Gamma\subset\mathbf R_{>0}$ is either of the form $t^{\mathbf Z}$ for a unique $t\in\mathbf R_{>1}$ or is $\mathbf R_{>0}$ (the case $|\cdot|_G$ is surjective), and in all cases we claim $|\cdot|_G$ admits continuous homomorphic sections $\tau:\Gamma\to G$ (each thereby inducing an isomorphism $G\simeq G^1\times\Gamma$ depending on the choice of $\tau$). This is clear when $\Gamma$ is infinite cyclic. When $|\cdot|_G$ is surjective, the existence of $\tau$ follows from the proper $|\cdot|_G:G\to\mathbf R_{>0}$ being a quotient map and $G$ necessarily having an open subgroup of the form $K\times\mathbf R^N$ for some compact group $K$ and integer $N\ge 1$ [Ru, Thm. 1.2.4].

Modulated groups are discussed by Weil in his paper on the explicit formulas for Artin $L$-functions of number fields; we refer the reader to [Weil-e, §3, pp. 5-6]. Many non-compact Hausdorff locally compact groups of arithmetic integer, abelian and non-abelian, are modulated. The examples throughout this work will be $(C_F,|\cdot|_F)$, $(C_{F,S},|\cdot|_F\circ i_{F,S})$, and $(J_{F,S},|\cdot|_{F,S})$, with $i_{F,S}:C_{F,S}\to C_F$ the continuous open injective homomorphism induced by the inclusion $\mathrm{GL}_1(\mathbf A_{F,S}\times\widehat{\mathcal O}_{\Sigma_F-S})\to\mathrm{GL}_1(\mathbf A_F)$.

REMARK D.2.1.3 (Canonical measure on modulated groups). For $G$ a Hausdorff locally compact modulated abelian group and $\tau:\Gamma\to G$ a continuous homomorphic section to the module $|\cdot|_G$ (which defines an isomorphism $G^1\times\Gamma\simeq G$), to build $\mu_{\mathrm{can}}$ we use

$$
\mu_{\mathrm{can}}=\mu_{1,\mathrm{can}}\times\mu_{\Gamma}
$$

where $\mu_{1,\mathrm{can}}$ is the volume-1 Haar measure on $G^1$ and $\mu_{\Gamma}$ is a Haar measure on $\Gamma\subset\mathbf R_{>0}$ satisfying

$$
\mu_{\Gamma}([1/\Lambda,\Lambda]\cap\Gamma)=2\log(\Lambda)+O(1) \tag{D.2.1.5}
$$

as $\Lambda\to+\infty$.

To see such a $\mu_{\Gamma}$ exists, we separately treat the cases $\Gamma=\mathbf R_{>0}$ and $\Gamma=t^{\mathbf Z}$ for some $t>1$. In the case $\Gamma=\mathbf R_{>0}$ we use $\mu_{\Gamma}=\mathrm{d}t/t$ (in this case the $O(1)$-term in (D.2.1.5) vanishes). In the case $\Gamma=t^{\mathbf Z}$ with $t>1$, take $\mu_{\Gamma}$ to be counting measure multiplied by $\log(t)$; this satisfies (D.2.1.5) because the difference between $2\log(\Lambda)$ and

$$
\#\{m\in\mathbf Z:1/\Lambda\le t^m\le\Lambda\}\log(t)
$$

is bounded (by $\log(t)$) as $\Lambda\to+\infty$.

REMARK D.2.1.4. In light of Remark D.2.1.3, we make the following observations on our choice of Haar measures $\overline{\mu}$ on $C_F$, $\overline{\mu}_1$ on $C^1_F$, $\overline{\mu}_S$ on $J_{F,S}$, and $\overline{\mu}_{S,1}$ on $J^1_{F,S}$. The Haar measures $\overline{\mu}_1$ on $C^1_F$ and its open

## PDF page 794

**794** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

subgroup $C^1_{F,S}$, and $\overline{\mu}_{S,1}$ on $J^1_{F,S}$, generally do *not* give $C^1_F$, $C^1_{F,S}$, and $J^1_{F,S}$ volume 1 and are therefore $\overline{\mu}$ and $\overline{\mu}_S$ not the “canonical” choices on $C_F$ and $J_{F,S}$ in the sense of $\mu_{\mathrm{can}}$ on a modulated group as discussed above. Since the pair of measures $\overline{\mu}$ on $C_F$ and $\overline{\mu}_1$ on $C^1_F$, as well as the pair $\overline{\mu}_S$ on $J_{F,S}$ and $\overline{\mu}_{S,1}$ on $J^1_{F,S}$, induces $\mathrm{d}t/t$ on the idelic-norm image $\mathbf R_{>0}$, it follows that the canonical measure $\mu_{\mathrm{can}}$ on $C_F$ is

$$
\mu_{\mathrm{can}}=\frac{1}{\overline{\mu}_1(C^1_F)}\overline{\mu} \tag{D.2.1.6}
$$

and similarly the canonical measure on $J_{F,S}$ is

$$
\mu_{S,\mathrm{can}}=\frac{1}{\overline{\mu}_{S,1}(J^1_{F,S})}\overline{\mu}_S. \tag{D.2.1.7}
$$

We will be adhering to our choice of normalizations $\overline{\mu}$ and $\overline{\mu}_S$ due to their general familiarity from Tate’s dissertation [CF, Ch. XV, §2.3] and their role in the proof of the Class Number Formula contained therein (see [CF, Ch. XV, §4, Thms. 4.3.2, 4.4.1]).

**D.2.2. Complements on the $G^1$-isotypes of $\mathcal S(G)$ for modulated groups $G$.** By Lemma 4.3.3.1(2) (applied to the $G^1$-action on $E=\mathcal S(G)$ defined by $f\mapsto\overline{\omega}(g)\,g.f$ for $g\in G^1$), $\Phi_{G,\omega}$ induces a linear topological isomorphism

$$
\Phi_{G,\omega}:\mathcal S(G)(\omega)\to\mathrm H^0(\omega,\mathcal S(G)) \tag{D.2.2.1}
$$

where $\mathcal S(G)(\omega)$ is the linear quotient $\mathcal S(G)/\ker(\Phi_{G,\omega})$ equipped with the quotient topology. The kernel of $\Phi_{G,\omega}$ is the closure in $\mathcal S(G)$ of the subspace of differences $\{f-\overline{\omega}(g)\,g.f:f\in\mathcal S(G),g\in G^1\}$ by Lemma 4.3.3.1(3), so $\mathcal S(G)(\omega)$ is the maximal Hausdorff quotient of the space of $G^1$-coinvariants of $\mathcal S(G)$ under the action $f\mapsto\overline{\omega}(g)\,g.f$ ($g\in G^1$). For this reason, $\mathcal S(G)(\omega)$ is also denoted $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(G))$.

For a Hausdorff locally convex topological $\mathbf C$-vector space $E$ equipped with a left action $\rho_G$ of $G$ by linear topological automorphisms, we say $\rho_G$ is *uniformly continuous* on a subset $\Sigma\subset G$ if and only if for every $0$-neighborhood $U\subset E$ there exists $0$-neighborhood $V\subset E$ so that $\rho_G(\sigma,x)\in U$ for all $\sigma\in\Sigma$. Equivalently, this says that for every net $\{x_i\}_{i\in I}\subset E$ converging to $x\in E$ and every $0$-neighborhood $U\subset E$ there exists $i_0$ so that $\rho_G(\sigma,x_i)-\rho_G(\sigma,x)=\rho_G(g,x_i-x)\in U$ for all $i\ge i_0$ and all $\sigma\in\Sigma$. For example, Proposition D.1.9.2 the $G$-action on $\mathcal S(G)$ is uniformly continuous on any compact subset $K\subset G$.

LEMMA D.2.2.1 ($G^1$-isotypes under coarsening of the topology - I). *Let $G$ be a Hausdorff locally compact modulated abelian group equipped with a module*

$$
|\cdot|_G:G\to\mathbf R_{>0}. \tag{D.2.2.2}
$$

*Let $\mu_1$ be a choice of Haar measure on the compact Hausdorff abelian group $G^1$. Let*

$$
i:\mathcal S(G)\hookrightarrow E
$$

*be a continuous injective linear map to a Hausdorff locally convex topological $\mathbf C$-vector space.*

*Assume $E$ is complete and is equipped with a uniformly continuous left action $\rho_G$ of $G$ making $i$ be $G$-equivariant (using the continuous left-translation action on the source). Choose a continuous character $\omega\in\widehat{G^1}$ and denote by*

$$
\Phi^E_{G,\omega}:E\to\mathrm H^0(\omega,E):=\{u\in E:\rho_G(g,u)=\omega(g)u\text{ for all }g\in G^1\} \tag{D.2.2.3}
$$

*the continuous linear averaging map*

$$
\Phi^E_{G,\omega}(u):=\frac{1}{\mu_1(G^1)}\int_{G^1}\overline{\omega}(g)\rho_G(g,u)\,\mathrm{d}\mu_1(g) \tag{D.2.2.4}
$$

*provided by Lemma 4.3.3.1 (applied to the $G^1$-action on $E$ defined by $u\mapsto\overline{\omega}(g)\rho_G(g,u)$ for $g\in G^1$).*

*The following hold:*

## PDF page 795

**D.2. SCHWARTZ-BRUHAT FUNCTIONS ON MODULATED GROUPS** · **795**

(1) *$i^{-1}(\ker(\Phi^E_{G,\omega}))=\ker(\Phi_{G,\omega})$ as closed subspaces of $\mathcal S(G)$, and $i$ induces continuous injective linear maps (each also denoted as $i$)*

$$
\mathcal S(G)(\omega)\to E(\omega):=E/\ker(\Phi^E_{G,\omega}),\ \mathrm H^0(\omega,\mathcal S(G))\to\mathrm H^0(\omega,E) \tag{D.2.2.5}
$$

(2) *We have $i^{-1}(\mathrm H^0(\omega,E))=\mathrm H^0(\omega,\mathcal S(G))$ as closed subspaces of $\mathcal S(G)$.*

(3) *If $i$ has dense range then so do the continuous linear maps in (D.2.2.5).*

(4) *For any $T\in\mathscr L(\mathcal S(G))$ continuous with respect to the Hausdorff locally convex topology induced on $\mathcal S(G)$ by $i$, if $i$ has dense range then $T$ extends by continuity to a unique $\overline{T}\in\mathscr L(E)$. If, furthermore, there exists a topological automorphism $\alpha$ of $G$ leaving $|\cdot|_G$ unaffected such that $T$ satisfies*

$$
T\circ\rho_G(g,\cdot)=\rho_G(\alpha(g),T(\cdot)) \tag{D.2.2.6}
$$

*for every $g\in G^1$ then the map $\overline{T}$ satisfies*

$$
\overline{T}\circ\rho_G(g,\cdot)=\rho_G(\alpha(g),\overline{T}(\cdot)) \tag{D.2.2.7}
$$

*and for $\alpha^*\omega:=\omega\circ\alpha^{-1}$ $^{9}$ there exist unique continuous linear maps $T_{\omega}$, $\overline{T}_{\omega}$ making the diagrams*

(D.2.2.8)

```latex
\begin{tikzcd}
\mathcal S(G) \arrow[r] \arrow[d, "T"'] & \mathcal S(G)(\omega) \arrow[r, "\Phi_{G,\omega}", "\simeq"'] \arrow[d, "T_{\omega}"] & \mathrm H^0(\omega,\mathcal S(G)) \arrow[d, "T"] \\
\mathcal S(G) \arrow[r] & \mathcal S(G)(\alpha^*\omega) \arrow[r, "\simeq", "\Phi_{G,\alpha^*\omega}"'] & \mathrm H^0(\alpha^*\omega,\mathcal S(G))
\end{tikzcd}
```

and

(D.2.2.9)

```latex
\begin{tikzcd}
E \arrow[r] \arrow[d, "\overline{T}"'] & E(\omega) \arrow[r, "\Phi^E_{G,\omega}", "\simeq"'] \arrow[d, "\overline{T}_{\omega}"'] & \mathrm H^0(\omega,E) \arrow[d, "\overline{T}"] \\
E \arrow[r] & E(\alpha^*\omega) \arrow[r, "\simeq", "\Phi^E_{G,\alpha^*\omega}"'] & \mathrm H^0(\alpha^*\omega,E)
\end{tikzcd}
```

*commute. The operator $\overline{T}_{\omega}$ is the unique extension by continuity of $T_{\omega}$.*

In both diagrams, the composites across the rows are the actual averaging operators $\Phi_{G,\omega}$, $\Phi^E_{G,\omega}$, etc., with the induced isomorphisms as the right arrows in the rows (denoted as $\Phi_{G,\omega}$, etc. via abuse of notation) due to the isomorphism in (4.3.3.2) (where the group denoted $G$ there is $G^1$ in the present setting).

PROOF. The formation of Pettis integrals (over the compact $G^1$) with values in the complete $E$ (equipped with a uniformly continuous $G^1$-action) is functorial with respect to $G^1$-equivariant continuous linear maps between such spaces $E$: see Lemma C.4.3.8. Thus, (1) and (2) are a consequence of the injectivity of $i$ and the definitions of $\Phi_{G,\omega}$ and $\Phi^E_{G,\omega}$.

Assertion (3) follows from Lemma 4.3.3.1(2) since the continuous linear maps $\Phi_{G,\omega}$ and $\Phi^E_{G,\omega}$ are both open onto the respective spaces of $\omega$-isotypic vectors. For (4), the existence and uniqueness of $\overline{T}$ arises from the universal mapping property of $E$ as the completion of $\mathcal S(G)$ with respect to the Hausdorff subspace topology on it arising from the complete $E$. The uniqueness of $T_{\omega}$ and $\overline{T}_{\omega}$ is due to the surjectivity of the left horizontal maps in the top row of the two diagrams, and the existence follows from $T$ and $\overline{T}$ taking $\omega$-isotypic vectors to $\alpha^*(\omega)$-isotypic vectors.

$\square$

In light of Lemma D.2.2.1, for $i:\mathcal S(G)\to E$ continuous linear with dense range and satisfying the assumptions of the Lemma, we will identify $E(\omega)$ and $\mathrm H^0(\omega,E)$ as the need arises, each equipped with their

$^{9}$Now composing with $\alpha^{-1}$, was composing with $\alpha$ before but seems need $\alpha^{-1}$: $T$ carries $\omega$-isotypic to $\omega\circ\alpha^{-1}$-isotypic.

## PDF page 796

**796** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

induced continuous action of $G$, without mentioning the linear topological isomorphism induced by $\Phi^E_{G,\omega}$. We will refer to such Hausdorff locally convex complete topological $\mathbf C$-vector spaces as the $\omega$-isotype of $\mathcal S(G)$, respectively $E$, for each continuous character $\omega\in\widehat{G^1}$.

Similarly, for $T\in\mathscr L(\mathcal S(G))$ compatible with the continuous left-translation action of $G^1$ on $\mathcal S(G)$ up to continuous automorphisms of $G$ (i.e. satisfying the identity in (D.2.2.6) for every $g\in G^1$) we will refer to $T_{\omega}$ and $\overline{T}_{\omega}$ as the operators induced by $T$ “on isotypes”. Constructions on isotypes of $\mathcal S(G)$ are inherited by the isotypes of $E$ under the assumptions of the Lemma on $E$ and on continuous endomorphisms of $\mathcal S(G)$ extending to $E$ compatibly with the continuous actions of $G$ on source and target.

Next we record a description of the isotypes of $\mathcal S(G)$ for $G$ a modulated Hausdorff locally compact abelian group. We refer the reader to §C.2.3.4, particularly Corollary C.2.3.12 and Proposition C.2.3.13, for the main properties of the inductive tensor product topology $\otimes_{\iota}$ and its completion $\overline{\otimes}$ that are used below.

LEMMA D.2.2.2 ($G^1$-isotypes under coarsening of the topology - II). *Let $G$ be a second-countable Hausdorff locally compact abelian modulated group, with module $|\cdot|_G$, and let $\tau$ be a continuous homomorphic section to the module $|\cdot|_G$.*

*(1) The section $\tau$ induces a linear topological isomorphism*

$$
\mathcal S(G^1)\overline{\otimes}\mathcal S(\Gamma)\to\mathcal S(G) \tag{D.2.2.10}
$$

*compatible with the continuous left-translation action of $G^1\times\Gamma$ on the source through the tensor factors, and of $G$ on the target.*

*(2) Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space that is complete and bornological and equipped with a continuous left action $\rho^E_G$ of $G$. Assume:*

*(i) The action $\rho^E_G$ of $G$ on $E$ is sequentially uniformly continuous (so the $E$-valued $\omega$-isotypic averaging operator $\Phi^E_{G,\omega}$ over $G^1$ via Lemma 4.3.3.1(b) makes sense, allowing us to define the quotient space $E(\omega)=\mathrm H_{0,\mathrm{cont}}(\omega,E):=E/\ker(\Phi^E_{G,\omega})$ of “continuous $\omega$-isotypic coinvariants”).*

*(ii) There exists a continuous injective linear map $i:\mathcal S(G)\to E$ with dense range that is equivariant with respect to the continuous left-translation action of $G$ on $\mathcal S(G)$ and the action $\rho^E_G$ on $E$.*

*(iii) For any continuous character $\chi\in\widehat{G}$, the continuous linear operator $M_{\chi}:\mathcal S(G)\to\mathcal S(G)$ defined as multiplication by the smooth function $\chi:G\to\mathbf C$ is also continuous with respect to the subspace topology on $\mathcal S(G)$ induced by $i$ from $E$.*

*Letting $\chi:G=G^1\times\Gamma\to\mathbf C^{\times}$ be defined by $\chi(g^1\tau(\gamma))=\overline{\omega}(g^1)$, the composite injective continuous linear map $\mathcal S(\Gamma)\xrightarrow{\tau}\mathcal S(G)\xrightarrow{i}E$ gives $\mathcal S(\Gamma)$ a (necessarily coarser Hausdorff locally convex) subspace topology whose completion maps isomorphically via $M_{\chi}$ onto the Hausdorff quotient $E(\omega)$ of $E$.*

The meaning of the final assertion is that under the linear topological automorphism $M_{\chi}$ of $\mathcal S(G)$ equipped with the subspace topology from $E$, the natural map $M_{\chi}(\mathcal S(\Gamma))\to E(\omega)$ identifies the target with the completion of the source.

PROOF. Assertion (1) is a special case of Lemma D.1.8.1(1). For assertion (2), we first treat the case $E=\mathcal S(G)$ with $i$ the identity. We have $\mathcal S(\Gamma)=\mathrm H^0(G^1,\mathcal S(G))$ (functions independent of the second component in $G=\Gamma\times G^1$), and $M_{\chi}(g.f)=\chi(g)(g.M_{\chi}(f))$ for $g\in G$, so $M_{\chi}$ carries the space of $G^1$-invariants onto the space of $\omega$-isotypic vectors. In other words, $M_{\chi}(\mathcal S(\Gamma))=\mathrm H^0(\omega,\mathcal S(G))$, Thus, the composite map $M_{\chi}(\mathcal S(\Gamma))\to\mathcal S(G)\hookrightarrow\mathcal S(G)(\omega)$ is a topological isomorphism due to (4.3.3.2) applied to $E=\mathcal S(G)$ and the group $G^1$ acting by $f\mapsto\overline{\omega}(g)\,g.f$ for $g\in G^1$. This settles the special case $E=\mathcal S(G)$ with $i$ the identity.

## PDF page 797

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH $I$-EXPONENTIAL DECAY** · **797**

Now we turn to the general case of (2). The assumed continuity of $M_{\chi}$ with respect to the topology on $\mathcal S(G)$ by $E$ under $i$ allows us to conclude by using Lemma D.2.2.1(4) with $T=M_{\chi}$ $^{10}$ provided that the Hausdorff quotient $E(\omega)$ of $E$ inherits completeness from $E$ and the continuous linear map $M_{\chi}(\mathcal S(\Gamma))\to E(\omega)$ is a topological embedding with dense image. Let us now verify these two properties.

The completeness of $E(\omega)$ holds because the natural map $\mathrm H^0(\omega,E)\to E(\omega)$ is a topological isomorphism (see (4.3.3.2)) and $\mathrm H^0(\omega,E)$ inherits completeness due to its closedness inside $E$. The map $M_{\chi}(\mathcal S(\Gamma))\to E(\omega)$ (where $\mathcal S(\Gamma))$ is given the subspace topology from $E$) is topologically identified with the map $\mathrm H^0(\omega,\mathcal S(G))\to\mathrm H^0(\omega,E)\simeq E(\omega)$ that is a topological embedding when $\mathcal S(G)$ is given the subspace topology from $E$. The image of this map is also dense because the map is linearly identified with $\mathcal S(G)(\omega)\to E(\omega)$ whose image is dense since $\mathcal S(G)$ is dense in $E$.

$\square$

D.2.2.1. *A kernel Theorem for $\mathbf R_{>0}$-modulated groups.* Lemma D.2.2.2 takes the following form for $G$ any modulated group such that the module $|\cdot|_G$ is surjective; i.e., for which $\Gamma=\mathbf R_{>0}$. (Examples of interest include $G=C_F,C_{F,S},J_{F,S}$.) We refer to these modulated groups as $\mathbf R_{>0}$-modulated.

COROLLARY D.2.2.3.$^{11}$ *Let $G$ be a second-countable $\mathbf R_{>0}$-modulated group; i.e., $\Gamma=\mathbf R_{>0}$. Fix a choice of $\omega\in\widehat{G^1}$ and a continuous homomorphic section $\tau$ to $|\cdot|_G$, and let $\chi:G=G^1\times\Gamma\to\mathbf C^{\times}$ be the character $\chi(g^1\tau(\gamma))=\overline{\omega}(g^1)$. Let $M_{\chi}:\mathcal S(G)\simeq\mathcal S(G)$ be multiplication by $\chi$.*

*(1) The natural continuous linear map $\mathcal S(\mathbf R_{>0})\simeq M_{\chi}(\mathcal S(\Gamma))\to\mathcal S(G)(\omega)$ is a topological isomorphism;*

*(2) Let $E$ be a complete Hausdorff locally convex topological vector space equipped with a continuous left $G$-action and a $G$-equivariant continuous linear injection $i:\mathcal S(G)\to E$ such that $M_{\chi}:\mathcal S(G)\to\mathcal S(G)$ is a topological isomorphism when $\mathcal S(G)$ is equipped with the subspace topology from $E$.*

*When $\mathcal S(\Gamma)\overset{\tau}{\hookrightarrow}\mathcal S(G)$ is equipped with the subspace topology from $E$, the natural map $M_{\chi}(\mathcal S(\Gamma))\to E(\omega)$ is a topological embedding that identifies the target with the completion of the source.*

PROOF. This is Lemma D.2.2.2 in the special case $\Gamma=\mathbf R_{>0}$.

$\square$

**D.3. Schwartz-Bruhat functions with $I$-exponential decay**

We now relate spaces of Schwartz-Bruhat functions on the positive real line with exponential or semi-exponential decay to spaces of holomorphic functions on the complex plane or half-planes, with rapid decay uniformly over vertical strips of bounded width.

**D.3.1. Schwartz-Bergman spaces.** We begin with the following application of the Asymptotic Residue Theorem (see Theorem B.3.2.1).

LEMMA D.3.1.1. *Let $I\subset\mathbf R$ be a non-empty open bounded interval, and $N\ge 0$ an integer. Let $\phi$ be a holomorphic function on the open vertical strip $\mathbf C_I$ of bounded width. Assume that for every non-empty open interval $J\subset\mathbf R$ strictly contained within $I$ (i.e., $\overline{J}\subset I$), $s^N\phi(s)$ is bounded over $\mathbf C_J$. Then for every integer $k\ge 0$, $\partial_s^k\phi$ satisfies the same condition.*

PROOF. We write $I:=(a,b)$ for real numbers $a<b$. For any non-empty open interval $J\subset\mathbf R$ strictly contained within $I$, there exists $\varepsilon>0$ small enough such that $a+2\varepsilon<b-2\varepsilon$ and $J\subset[a+2\varepsilon,b-2\varepsilon]$. By hypothesis, $s^N\phi$ is bounded over $\mathbf C_{[a+\varepsilon,b-\varepsilon]}$. We fix a point $z\in\mathbf C_{(a+2\varepsilon,b-2\varepsilon)}$.

$^{10}$No, that cited Lemma is not what we need since automorphisms $\alpha$ of $G$ are not relevant here; we are using a variant of the Lemma where $T$ intertwines the isotypic subspaces for two characters of $G^1$ without any automorphism of $G$ being relevant. For $\chi$ as just defined, $T(g.f)=\chi(g)\,g.(Tf)$, so $T$ carries $G^1$-invariants exactly onto $\mathrm H^0(\omega,\mathcal S(G))$.

$^{11}$This result is never cited anywhere, so why is it stated? The preceding result entirely subsumes it anyway.

## PDF page 798

**798** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

For $k\ge 0$ a fixed arbitrary integer, the function:

$$
f_z(s):=\frac{s^N\phi(s)}{(s-z)^{k+1}} \tag{D.3.1.1}
$$

is meromorphic over $\mathbf C_I$, with a pole of order at most $k+1$ at $s=z$. For $s=\sigma+iT$, the function of $T$ given by

$$
u_{\sigma}(T):=\frac{(\sigma+iT)^N\phi(\sigma+iT)}{(\sigma+iT-z)^{k+1}}=f_z(\sigma+iT)
$$

satisfies $\lim_{|T|\to+\infty}\sup_{\sigma\in[a+\varepsilon,b-\varepsilon]}|u_{\sigma}(T)|=0$ since

$$
|u_{\sigma}(T)|\le\frac{\sup_{s\in\mathbf C_{[a+\varepsilon,b-\varepsilon]}}|s^N\phi(s)|}{|\sigma+iT-z|^{k+1}}=\frac{\sup_{s\in\mathbf C_{[a+\varepsilon,b-\varepsilon]}}|s^N\phi(s)|}{(|\sigma+\mathrm{Re}(z)|^2+|T-\mathrm{Im}(z)|^2|^{(k+1)/2}}\le\frac{\sup_{s\in\mathbf C_{[a+\varepsilon,b-\varepsilon]}}|s^N\phi(s)|}{|T-\mathrm{Im}(z)|^{k+1}} \tag{D.3.1.2}
$$

where the right side of (D.3.1.2) is finite for $T\ne\mathrm{Im}(z)$.

*[Figure, redrawn from the PDF, p. 798:]*

```latex
\begin{tikzpicture}[x=1.5cm,y=1.2cm,>=stealth,mid/.style={decoration={markings,mark=at position 0.55 with {\arrow[scale=1.4]{>}}},postaction={decorate}},midv/.style={decoration={markings,mark=at position 0.66 with {\arrow[scale=1.4]{>}}},postaction={decorate}}]
\draw[<->] (0,0) -- (2.6,0);
\draw[<->] (0,-1.9) -- (0,1.9);
\draw[mid] (2, 1.5) -- (1, 1.5);
\draw[midv] (1, 1.5) -- (1, -1.5);
\draw[mid] (1, -1.5) -- (2, -1.5);
\draw[midv] (2, -1.5) -- (2, 1.5);
\fill (1,1.5) circle (1.5pt) node[left] {$c+iT$};
\fill (2,1.5) circle (1.5pt) node[right] {$c'+iT$};
\fill (1,0) circle (1.5pt) node[above left] {$c$};
\fill (2,0) circle (1.5pt) node[above right] {$c'$};
\fill (1,-1.5) circle (1.5pt) node[left] {$c-iT$};
\fill (2,-1.5) circle (1.5pt) node[right] {$c'-iT$};
\fill (0,0) circle (1.5pt) node[above left] {$0$};
\end{tikzpicture}
```

FIGURE 1. A counterclockwise rectangular contour, with $c=a+\varepsilon$, $c'=b-\varepsilon$

By the Cauchy Integral Formula applied to the contour in Figure 1, we have

$$
\partial_s^k(s^N\phi)|_{s=z}=-\frac{k!}{2\pi i}\int_{a+\varepsilon-iT}^{a+\varepsilon+iT}f_z(s)\,\mathrm{d}s+\frac{k!}{2\pi i}\int_{b-\varepsilon-iT}^{b-\varepsilon+iT}f_z(s)\,\mathrm{d}s+\frac{k!}{2\pi i}\int_{a+\varepsilon-iT}^{b-\varepsilon-iT}f_z(s)\,\mathrm{d}s-\frac{k!}{2\pi i}\int_{a+\varepsilon+iT}^{b-\varepsilon+iT}f_z(s)\,\mathrm{d}s. \tag{D.3.1.3}
$$

In light of (D.3.1.2), we have:

$$
\frac{k!}{2\pi}\int_{a+\varepsilon-iT}^{b-\varepsilon-iT}|f_z(s)|\,|\mathrm{d}s|+\frac{k!}{2\pi}\int_{a+\varepsilon+iT}^{b-\varepsilon+iT}|f_z(s)|\,|\mathrm{d}s|\le A\left\{\frac{1}{|T-\mathrm{Im}(z)|^{k+1}}+\frac{1}{|-T-\mathrm{Im}(z)|^{k+1}}\right\} \tag{D.3.1.4}
$$

where

$$
A:=\frac{k!(b-a-2\varepsilon)\sup_{s\in\mathbf C_{[a+\varepsilon,b-\varepsilon]}}|s^N\phi(s)|}{2\pi}>0.
$$

We deduce that for $k\ge 1$ we have

$$
|\partial_s^k(s^N\phi)||_{s=z}\le\frac{k!}{2\pi}\int_{-\infty}^{+\infty}\frac{|a+\varepsilon+it|^N|\phi(a+\varepsilon+it)|}{(|a+\varepsilon-\mathrm{Re}(z)|^2+|t-\mathrm{Im}(z)|^2)^{(k+1)/2}}\,\mathrm{d}t \tag{D.3.1.5}
$$

$$
+\frac{k!}{2\pi}\int_{-\infty}^{+\infty}\frac{|b-\varepsilon+it|^N|\phi(b-\varepsilon+it)|}{(|b-\varepsilon-\mathrm{Re}(z)|^2+|t-\mathrm{Im}(z)|^2)^{(k+1)/2}}\,\mathrm{d}t \tag{D.3.1.6}
$$

where the integrals converge since $s^N\phi(s)$ is bounded on vertical lines within $\mathbf C_I$ and $k+1>1$.

## PDF page 799

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH $I$-EXPONENTIAL DECAY** · **799**

Since $z\in\mathbf C_{(a+2\varepsilon,b-2\varepsilon)}$, then $|a+\varepsilon-\mathrm{Re}(z)|\ge\varepsilon$, and $|b-\varepsilon-\mathrm{Re}(z)|\ge\varepsilon$, and so the two integrals in (D.3.1.5), which are bounded independently of $\mathrm{Im}(z)$ (because $s^N\phi$ is bounded on $\mathbf C_{[a+\varepsilon,b-\varepsilon]}$), are bounded above by a positive constant independent of $\mathrm{Re}(z)$ too. In particular, $\partial_s^k(s^N\phi)$ is bounded over $\mathbf C_{(a+2\varepsilon,b-2\varepsilon)}$, and hence $\partial_s^k(s^N\phi)$ is bounded over $\mathbf C_J$ for every integer $k\ge 1$; this also holds for $k=0$ by hypothesis.

We want to show $s^N\partial_s^k\phi$ is bounded over $\mathbf C_J$ for every non-empty open interval $J$ with $\overline{J}\subset I$. For $k=0$ this is given in the hypotheses, and $N=0$ was settled above (for all $k$), so we now assume $k,N\ge 1$. We have

$$
\partial_s^k(s^N\phi)=\sum_{0\le m\le\min(k,N)}\binom{k}{m}\frac{N!}{(N-m)!}s^{N-m}\,\partial_s^{k-m}\phi(s)
$$

over $\mathbf C_I$, and by separating off the term for $m=0$ we see that if the desired boundedness assertion holds for $\partial_s^j\phi$ for every $0\le j\le k-1$ (i.e., for each such $j$, $s^N\partial_s^j\phi$ is bounded over $\mathbf C_J$ for any non-empty open interval $J$ with $\overline{J}\subset I$) then it also holds for $\partial_s^k\phi$. We conclude by induction on the integer $k\ge 0$.

$\square$

The following Lemma is reminiscent of properties of Bergman Spaces and their completeness (see [HKZ, Prop.1.2]), replacing the role of the open unit disc with that of an open vertical strip:

LEMMA D.3.1.2 (Uniform Schwartz topology and $L^p$-convergence on vertical lines). *Let $I\subset\mathbf R$ be a non-empty open interval, and $\mathcal S(\mathbf C_I)$ the $\mathbf C$-vector space of holomorphic functions on $\mathbf C_I$ that are Schwartz (in terms of vertical decay properties) uniformly on the vertical strips inside $\mathbf C_I$ of bounded width (so all functions $s^N\phi$ for $N\ge 0$ and $\phi\in\mathcal S(\mathbf C_I)$ are bounded on $\mathbf C_J$ for all open intervals $J$ with $\overline{J}\subset I$).*

*Let $p>1$ be a real number, and $a_{\bullet}:=\{a_m\}_{m\ge 0}\subset I$ a sequence of real numbers such that $\inf(I)$ and $\sup(I)$ are accumulation points of $a_{\bullet}$ (for instance, if $\inf(I)=0$ then $0$ is an accumulation point and if $\sup(I)=+\infty$ then $\limsup_{m\ge 0}a_m=+\infty$).*

*When $\mathcal S(\mathbf C_I)$ is endowed with the topology of $L^p$-convergence on all vertical lines $a_m+i\mathbf R$ for all $\{s^N\phi\}_{N\ge 0}$ for $\phi\in\mathcal S(\mathbf C_I)$ then it is a separable Fréchet space. This topology is equal to the Hausdorff locally convex topology of Schwartz convergence on every vertical line of $\mathbf C_I$. In particular, this topology does not depend on the choice of $p>1$ nor on the choice of $a_{\bullet}$.*

PROOF. We will treat the case $I=(0,+\infty)$ for the sake of clarity, the general case being established with the same method, with only notational differences. Let $a_{\bullet}:=\{a_m\}_{m\ge 0}\subset\mathbf Q_{>0}$ be a sequence of positive rational numbers such that $0$ is an accumulation point, and $\limsup_{m\ge 0}a_m=+\infty$. Consider the linear map

$$
A_{a_{\bullet}}:\mathcal S(\mathbf C_{>0})\to\prod_{m\ge 0}\prod_{N\ge 0}L^p(\mathbf R,\mathrm{d}x) \tag{D.3.1.7}
$$

*defined as $A_{a_{\bullet}}(\phi):=(s^N\phi(s)|_{\mathrm{Re}(s)=a_m})_{m,N\ge 0}$.*

The map $A_{a_{\bullet}}$ is injective since elements of $\mathcal S(\mathbf C_{>0})$ are holomorphic by definition . Let $\{\phi_k\}_{k\ge 0}\subset\mathcal S(\mathbf C_{>0})$ be a sequence, and assume that the sequence $\{A_{a_{\bullet}}(\phi_k)\}_{k\ge 0}$ converges, so $\{\phi_k|_{a_m+i\mathbf R}\}_{m\ge 0}$ converges to some $(\alpha_m)_{m\ge 0}\in\prod_{m\ge 0}L^p(\mathbf R,\mathrm{d}x)$.

Let $0<A<B$ be arbitrary real numbers, and consider the vertical strip $\mathbf C_{(A,B)}$ of bounded width within $\mathbf C_{>0}$ for $\mathrm{Re}(s)\in(A,B)$. There exist integers $m_1,m_2$ such that $a_{m_1}<A<B<a_{m_2}$. Since each $\phi_k$ is holomorphic over the vertical strip $\mathbf C_{(a_{m_1},a_{m_2})}$ and is uniformly Schwartz, by Theorem B.2.2.4 we obtain

$$
\phi_k(s)=-\frac{1}{2\pi i}\int_{a_{m_1}-i\infty}^{a_{m_1}+i\infty}\frac{\phi_k(z)}{z-s}\,\mathrm{d}z+\frac{1}{2\pi i}\int_{a_{m_2}-i\infty}^{a_{m_2}+i\infty}\frac{\phi_k(z)}{z-s}\,\mathrm{d}z \tag{D.3.1.8}
$$

*for any $s\in\mathbf C_{(A,B)}$.*

Since $a_{m_1}<A$ and $a_{m_2}>B$, the function $(z-s)^{-1}$ for $z\in(a_{m_1}+i\mathbf R)\cup(a_{m_2}+i\mathbf R)$ and $s\in\mathbf C_{(A,B)}$ is uniformly bounded. Since $\{\phi_k|_{a_{m_j}+i\mathbf R}\}_{k\ge 0}$ converges in $L^p(\mathbf R,\mathrm{d}x)$ for $j=1,2$, both integrals in (D.3.1.8) as

## PDF page 800

**800** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

sequences of functions of $s\in\mathbf C_{(A,B)}$ satisfy

$$
\int_{a_{m_j}-i\infty}^{a_{m_j}+i\infty}\left|\frac{\phi_k(z)-\alpha_{m_j}(\mathrm{Im}(z))}{z-s}\right||\mathrm{d}z|\le\left(\int_{\mathbf R}|\phi_k(a_{m_j}+ix)-\alpha_{m_j}(x)|^p\,\mathrm{d}x\right)^{1/p}\left(\int_{\mathbf R}\left|\frac{1}{a_{m_j}+ix-s}\right|^q\,\mathrm{d}x\right)^{1/q} \tag{D.3.1.9}
$$

for $j=1,2$ by Hölder’s Inequality, with $1/p+1/q=1$ (we have $q=p/(p-1)>1$).

The first of the two factors on the right side of (D.3.1.9) is arbitrarily small for $j=1,2$ as $k\to+\infty$ since $\phi_k\to\alpha_{m_j}$ on $a_{m_j}+i\mathbf R$ in the $L^p$-sense. The second factor on the right side, namely

$$
\left(\int_{\mathbf R}\left|\frac{1}{a_{m_j}+ix-s}\right|^q\,\mathrm{d}x\right)^{1/q}, \tag{D.3.1.10}
$$

is bounded above (upon writing $s=\sigma+i\tau$) by

$$
\left(\int_{\mathbf R}\left(\frac{1}{|a_{m_j}-\sigma|^2+|x-\tau|^2}\right)^{q/2}\,\mathrm{d}x\right)^{1/q}\le\left(\int_{\mathbf R}\frac{1}{(|a_{m_j}-A|^2+x^2)^{q/2}}\,\mathrm{d}x\right)^{1/q}<\infty. \tag{D.3.1.11}
$$

The final upper bound is a positive constant depending only on $a_{m_j}$, $A$, $B$ but not on $s\in\mathbf C_{(A,B)}$.

In particular, $\{\phi_k\}_{k\ge 0}$ as a sequence of holomorphic functions on the vertical strip $\mathbf C_{(A,B)}$ converges pointwise to some function $\phi(s)$, namely on the strip $a_{m_1}<\sigma<a_{m_2}$ we have

$$
\phi(s)=-\frac{1}{2\pi i}\int_{a_{m_1}+i\mathbf R}\frac{\alpha_{m_1}(\mathrm{Im}(z))}{s-z}\,\mathrm{d}z+\frac{1}{2\pi i}\int_{a_{m_2}+i\mathbf R}\frac{\alpha_{m_2}(\mathrm{Im}(z))}{s-z}\,\mathrm{d}z
$$

where both integrals are oriented upward and are absolutely convergent by Hölder’s Inequality: the corresponding $L^1$-norms for $j=1,2$ are bounded above by

$$
\frac{1}{2\pi}\left(\int_{\mathbf R}|\alpha_{m_j}(y)|^p\,\mathrm{d}y\right)^{1/p}\left(\int_{a_{m_j}+i\mathbf R}\frac{|\mathrm{d}z|}{|z-s|^q}\right)^{1/q}<\infty.
$$

The convergence to $\phi$ is uniform on $\mathbf C_{(A,B)}$, so $\phi$ holomorphic over the vertical strip $\mathbf C_{(A,B)}$.

Since $(A,B)\subset\mathbf R_{>0}$ is arbitrary (here we use that $0$ is an accumulation point of $a_{\bullet}$ and $\limsup_{m\ge 0}a_m=+\infty$, so given any $(A,B)\subset\mathbf R_{>0}$ we can always find $a_{m_1}<A$ and $a_{m_2}>B$ belonging to $a_{\bullet}$), we see that the limit in $\prod_{m\ge 0}L^p(\mathbf R,\mathrm{d}x)$ of the image under $A_{a_{\bullet}}$ from (D.3.1.7) of the sequence $\{\phi_k\}_{k\ge 0}\subset\mathcal S(\mathbf C_{>0})$, remains in $\mathscr{O}(\mathbf C_{>0})$; i.e., it is holomorphic over $\mathbf C_{>0}$.

Using (D.3.1.8) and adapting the preceding considerations with $s^N\phi_k$ in place of $\phi_k$ for each $N\ge 1$, the uniform Schwartz condition on the limit holomorphic function $\phi$ over the vertical strips within $\mathbf C_{>0}$ of bounded width is verified using the convergence of the sequence of integrals (for each integer $N\ge 1$) in

$$
|s^N\phi_k(s)|\le\frac{1}{2\pi}\int_{\mathbf R}\left|\frac{(a_{m_1}+ix)^N\phi_k(a_{m_1}+ix)}{a_{m_1}+ix-s}\right|\,\mathrm{d}x+\frac{1}{2\pi}\int_{\mathbf R}\left|\frac{(a_{m_2}+ix)^N\phi_k(a_{m_2}+ix)}{a_{m_2}+ix-s}\right|\,\mathrm{d}x. \tag{D.3.1.12}
$$

We note that since each $s^N\phi$ is bounded over the vertical strips of bounded width in $\mathbf C_{>0}$ (staying away from the left edge), so is each $s^N(\partial_s^k\phi)$ for each integer $k\ge 0$, as a consequence of Lemma D.3.1.1. It follows that we have $\phi\in\mathcal S(\mathbf C_{>0})$. It follows that $A_{a_{\bullet}}$ has (sequentially) closed range in $\prod_{m\ge 0}\prod_{N\ge 0}L^p(\mathbf R,\mathrm{d}x)$. Thus, $\mathcal S(\mathbf C_{>0})$ is a Fréchet space.

The preceding work (especially on the strip $a_{m_1}<\sigma<a_{m_2}$ with uniformity) shows that the topology on $\mathcal S(\mathbf C_I)$ agrees with $L^p$-convergence on every vertical line of $\mathbf C_I$. This in turn agrees with convergence in $\mathcal S(\mathbf R)$ on every such vertical line due to Example D.1.10.3, so it agrees with the topology defined via $A_{a_{\bullet}}$.

$\square$

DEFINITION D.3.1.3 (Schwartz-Bergman spaces). Fix $1<p<\infty$ and $I\subset\mathbf R$ a non-empty open interval. We define the *Schwartz-Bergman space* $A\mathcal{S}(\mathbf C_I)$ to be the $\mathbf C$-linear space $\mathcal S(\mathbf C_I)$ of holomorphic functions on $\mathbf C_I$ that are Schwartz uniformly on the vertical strips of bounded width within $\mathbf C_I$, topologized with the

## PDF page 801

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH $I$-EXPONENTIAL DECAY** · **801**

Hausdorff locally convex topology generated by the countable family of seminorms $\{p_{m,N}\}_{m,N\ge 0}$ defined as:

$$
p_{m,N}(\phi):=\lVert (a_m+ix)^N\phi(a_m+ix)\rVert_{L^p(\mathbf{R},\mathrm{d}x)},\ m,N\ge 0
$$

with $\{a_m\}_{m\ge 0}\subset I$ a choice of sequence of positive rational numbers as in Lemma D.3.1.2.

REMARK D.3.1.4. Lemma D.3.1.2 shows that $A\mathcal{S}(\mathbf{C}_I)$ is a separable Fréchet space, and its topology does not depend on the choice of $\{a_m\}_{m\ge 0}$, nor on the choice of $p>1$.

**D.3.2. Fourier-Mellin transform on $\mathcal{S}_I(\mathbf{R}_{>0})$.** We now relate the spaces of Schwartz-Bruhat functions $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$, $\mathcal{S}_{\mathrm{SE}}(\mathbf{R}_{>0})$ and $\check{\mathcal{S}}_{\mathrm{SE}}(\mathbf{R}_{>0})$ with the Schwartz-Bergman spaces $A\mathcal{S}(\mathbf{C}_I)$ for $I=\mathbf{R}$, $I=\mathbf{R}_{>0}$ and $I=(-\infty,0)$ by means of the Mellin transform. We begin with a definition.

DEFINITION D.3.2.1 (Schwartz-Bruhat functions on $\mathbf{R}_{>0}$ with $I$-exponential decay). Let $I\subset\mathbf{R}$ be a non-empty interval. We define $\mathcal{S}_I(\mathbf{R}_{>0})\subset C^\infty(\mathbf{R}_{>0})$ to be the linear subspace of those smooth functions $\phi$ on $\mathbf{R}_{>0}$ satisfying the following condition: $t^a\phi(t)\in\mathcal{S}(\mathbf{R}_{>0})$ for all $a\in I$.

We call $\mathcal{S}_I(\mathbf{R}_{>0})$ the $\mathbf{C}$-linear space of *Schwartz-Bruhat functions of $I$-exponential decay*. We topologize $\mathcal{S}_I(\mathbf{R}_{>0})$ with the (visibly Hausdorff) projective topology [Scha, Ch. II, §5] induced by the $t^a$-multipliiers

$$
T_a:\mathcal{S}_I(\mathbf{R}_{>0})\to\mathcal{S}(\mathbf{R}_{>0})
\tag{D.3.2.1}
$$

for every $a\in I$ (i.e., $T_a(\phi)=t^a\phi$). In other words, the topology on $\mathcal{S}_I(\mathbf{R}_{>0})$ is the subspace topology arising from the linear injection $T=\prod_{a\in I}T_a:\mathcal{S}_I(\mathbf{R}_{>0})\to\prod_{a\in I}\mathcal{S}(\mathbf{R}_{>0})$, Equivalently, a net $\{\phi_\alpha\}$ in $\mathcal{S}_I(\mathbf{R}_{>0})$ converges to $\phi\in\mathcal{S}_I(\mathbf{R}_{>0})$ if and only if $T_a(\phi_\alpha)\to T_a(\phi)$ in $\mathcal{S}(\mathbf{R}_{>0})$ for all $a\in I$.

REMARK D.3.2.2. Each operator $T_a$ intertwines with the left-translation action by $\mathbf{R}_{>0}$ up to a controlled scalar multiplication: $T_a(c.\phi)=c^a(c.(T_a(\phi)))$ for $c\in\mathbf{R}_{>0}$. Thus, $\mathcal{S}_I(\mathbf{R}_{>0})$ has a natural $\mathbf{R}_{>0}$-action via $(c.f)(t)=f(c^{-1}t)$ that is moreover *continuous*, and uniformly so for the action of compact subsets of $\mathbf{R}_{>0}$ (thanks to the known case of $\mathcal{S}(\mathbf{R}_{>0})\simeq\mathcal{S}(\mathbf{R})$).

D.3.2.1. *Basic properties of $\mathcal{S}_I(\mathbf{R}_{>0})$.*

LEMMA D.3.2.3. *Let $I\subset\mathbf{R}$ be a non-empty interval. The following hold:*

(1) *The Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}_I(\mathbf{R}_{>0})$ is Fréchet and nuclear (hence Montel).*

(2) *The Hausdorff strong dual $\mathcal{S}_I(\mathbf{R}_{>0})'_\beta$ is complete, nuclear, and Montel.*

(3) *If $0\in I$, then $\mathcal{S}_I(\mathbf{R}_{>0})$ is naturally a linear subspace of $\mathcal{S}(\mathbf{R}_{>0})$ and the resulting injective linear inclusion*

$$
\mathcal{S}_I(\mathbf{R}_{>0})\subset\mathcal{S}(\mathbf{R}_{>0})
$$

*is continuous.*

(4) *If $I=[0,+\infty)$ then $\mathcal{S}_I(\mathbf{R}_{>0})=\mathcal{S}_{\mathrm{SE}}(\mathbf{R}_{>0})$, as $\mathbf{C}$-linear subspaces of $\mathcal{S}(\mathbf{R}_{>0})$.*

(5) *If $I=(-\infty,0]$ then $\mathcal{S}_I(\mathbf{R}_{>0})=\check{\mathcal{S}}_{\mathrm{SE}}(\mathbf{R}_{>0})$, as $\mathbf{C}$-linear subspaces of $\mathcal{S}(\mathbf{R}_{>0})$.*

(6) *If $I=\mathbf{R}$ then $\mathcal{S}_I(\mathbf{R}_{>0})=\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$ as $\mathbf{C}$-linear subspaces of $\mathcal{S}(\mathbf{R}_{>0})$.*

The implication “nuclear Fréchet $\Rightarrow$ Montel” noted in (1) is a special case of [Tre, Cor. 3 to Prop. 50.2] (since all Fréchet spaces are barrelled [Scha, Ch. II, Cor. to 7.1]).

PROOF. (1) : Since the topology on $\mathcal{S}_I(\mathbf{R}_{>0})$ is the subspace topology inherited from the product topology on $\prod_{a\in I}\mathcal{S}(\mathbf{R}_{>0})$ via a linear injection $T=\prod_{a\in I}T_a:\mathcal{S}_I(\mathbf{R}_{>0})\to\prod_{a\in I}\mathcal{S}(\mathbf{R}_{>0})$, $\mathcal{S}_I(\mathbf{R}_{>0})$ is nuclear because arbitrary products and subspaces of nuclear spaces are nuclear [Scha, Ch. III, Thm. 7.4].

Since $\{a\}\subset I$ for every $a\in I$, we have a linear inclusion $S_a:\mathcal{S}_I(\mathbf{R}_{>0})\subset\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})$, and $S_a$ is clearly continuous. Letting $R_a:\mathcal{S}_{\{b\}}(\mathbf{R}_{>0})\simeq\mathcal{S}_{\{b+a\}}(\mathbf{R}_{>0})$ be the linear homeomorphism given by $t^{-a}$-multiplication for all $a,b\in\mathbf{R}$, the linear image of $\mathcal{S}_I(\mathbf{R}_{>0})$ within the product $\prod_{a\in I}\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})$ under the continuous linear

## PDF page 802

**802** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

map $\prod_{a\in I}S_a$ is the closed linear subspace of those elements $\{\phi_a:a\in I\}$ satisfying $(R_b^{-1}\circ R_a)(\phi_a)=\phi_b$ for all $a,b\in I$. Hence, $\mathcal{S}_I(\mathbf{R}_{>0})$ is complete since $\prod_{a\in I}S_a$ is a linear topological embedding and each $\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})$ is complete (being isomorphic to $\mathcal{S}_{\{0\}}(\mathbf{R}_{>0})=\mathcal{S}(\mathbf{R}_{>0})$).

We may write $I$ as the countable union of closed intervals $[a,b]\subset\mathbf{R}$, and by a similar argument $\mathcal{S}_I(\mathbf{R}_{>0})$ is therefore realized as a topological subspace (hence as a locally convex topological $\mathbf{C}$-linear subspace) of the countable product of the $\mathcal{S}_{[a,b]}(\mathbf{R}_{>0})$'s, the linear topological embedding being induced by the natural continuous linear maps $\mathcal{S}_I(\mathbf{R}_{>0})\to\mathcal{S}_{[a,b]}(\mathbf{R}_{>0})$.

We further claim that $\mathcal{S}_{[a,b]}(\mathbf{R}_{>0})$ is carried onto a closed subspace of the product $\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})\times\mathcal{S}_{\{b\}}(\mathbf{R}_{>0})$ via the “diagonal” map $f\mapsto (f,f)$. To see this, via the change of variables $e^x=t^{b-a}$ we reduce to showing (i) if $f\in\mathcal{S}(\mathbf{R})$ satisfies $e^xf\in\mathcal{S}(\mathbf{R})$ then $e^{cx}f\in\mathcal{S}(\mathbf{R})$ for all $0<c<1$, (ii) the space of pairs $(f_1,f_2)\in\mathcal{S}(\mathbf{R})$ with $f_2=e^xf_1$ is closed. Since $e^{cx}f=e^{(c-1)x}(e^xf)$ with $c-1<0$, by separately treating $x<0$ and $x>0$ we get (i). The closedness in (ii) follows from consideration of convergent sequences (as $\mathcal{S}(\mathbf{R})$ is metrizable). Finally, the continuous linear bijection $\mathcal{S}_{[a,b]}(\mathbf{R}_{>0})\to\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})\times\mathcal{S}_{\{b\}}(\mathbf{R}_{>0})$ onto a closed subspace is a topological embedding because the same calculations show that convergence in $\mathcal{S}_{\{c\}}(\mathbf{R}_{>0})$ for $a<c<b$ is controlled by simultaneous convergence in both $\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})$ and $\mathcal{S}_{\{b\}}(\mathbf{R}_{>0})$.

It follows that $\mathcal{S}_{[a,b]}(\mathbf{R}_{>0})$, and hence $\mathcal{S}_I(\mathbf{R}_{>0})$, is a Fréchet space (as a countable product of complete metric spaces is a complete metric space). Being nuclear and Fréchet, we are done.

(2) : By [Scha, Ch. II, 8.1; Ch. IV, 6.1], $\mathcal{S}_I(\mathbf{R}_{>0})'_\beta$ is complete. By [Tre, Prop. 50.6], $\mathcal{S}_I(\mathbf{R}_{>0})'_\beta$ is nuclear. Finally, by [Scha, Ch. IV, 5.9], $\mathcal{S}_I(\mathbf{R}_{>0})'_\beta$ is Montel.

(3) : If $0\in I$ then the inclusion of intervals $\{0\}\subset I$ induces an injective continuous linear operator $\mathcal{S}_I(\mathbf{R}_{>0})\to\mathcal{S}_{\{0\}}(\mathbf{R}_{>0})$. We conclude by observing that we have $\mathcal{S}_{\{0\}}(\mathbf{R}_{>0})=\mathcal{S}(\mathbf{R}_{>0})$ by definition.

Assertions (4), (5) and (6) are a consequence of the definitions (see Definition B.2.1.1).$^{12}$ $\square$

REMARK D.3.2.4 (On nuclearity of $\mathcal{S}_I(\mathbf{R}_{>0})$). Let $I\subset\mathbf{R}$ be a non-empty interval. The definition of $\mathcal{S}_I(\mathbf{R}_{>0})$ realizes it, through the proof of Lemma D.3.2.3(1), as a subspace of $\mathfrak{s}^{\mathbf{N}}$ where $\mathfrak{s}=\mathcal{S}(\mathbf{Z})$ is the nuclear Fréchet space of rapidly decreasing $\mathbf{Z}$-indexed sequences. The relation of such Schwartz functions to $\mathfrak{s}$ is explained in the proof of [Tre, Cor. to Thm. 51.5] via Fourier series, and the inheritance of nuclearity under passage to subspaces and arbitrary products is [Tre, (50.3), (50.5) in Prop. 50.1] (or see [Scha, Ch. III, 7.4]).

D.3.2.2. *Fourier-Mellin transform on $\mathcal{S}_I(\mathbf{R}_{>0})$.*

PROPOSITION D.3.2.5 (Fourier-Mellin transform on $\mathcal{S}_I(\mathbf{R}_{>0})$). *Let $I\subset\mathbf{R}$ be an open non-empty interval. The assignment $\phi\mapsto M(\phi)(s):=\int_{\mathbf{R}_{>0}}\phi(t)t^s\,\frac{\mathrm{d}t}{t}$ is defined on $\mathcal{S}_I(\mathbf{R}_{>0})$ and valued in $A\mathcal{S}(\mathbf{C}_I)$. It induces a linear topological isomorphism*

$$
M_I:\mathcal{S}_I(\mathbf{R}_{>0})\to A\mathcal{S}(\mathbf{C}_I).
\tag{D.3.2.2}
$$

PROOF. By Proposition B.2.2.3(2), the visibly holomorphic $M(\phi)$ on $\mathbf{C}_I$ is Schwartz uniformly on every vertical strip $\mathbf{C}_J$ for every open bounded interval $J$ with $\overline{J}\subset I$. It follows that $M(\phi)$ is an element of $A\mathcal{S}(\mathbf{C}_I)$. The resulting linear operator $M_I:\mathcal{S}_I(\mathbf{R}_{>0})\to A\mathcal{S}(\mathbf{C}_I)$, $M_I$ as in (D.3.2.2) is injective by Fourier Inversion. To show it is surjective. pick $u\in A\mathcal{S}(\mathbf{C}_I)$. By injectivity of $M_I$, without loss of generality we may assume that $I$ is bounded. Proposition B.2.1.8 implies that there exists a unique $\phi\in C_0^\infty(\mathbf{R}_{>0})$ such that $M(\phi)=u$ over $\mathbf{C}_I$. By Lemma D.3.1.1 combined with differentiation under the integral sign and the Identity Theorem,$^{13}$ $(\log(t))^mt^\sigma\phi\in C_0^\infty(\mathbf{R}_{>0})$ for every $\sigma\in I$ and for every integer $m\ge 0$. This forces $\phi\in\mathcal{S}_I(\mathbf{R}_{>0})$.

The map $M_I$ is sequentially continuous by continuity of Fourier transform on $\mathcal{S}(\mathbf{R})$ since $M_I(\phi_m)|_{\sigma+i\mathbf{R}}\to M_I(\phi)|_{\sigma+i\mathbf{R}}$ as Schwartz functions on $\mathbf{R}$ for any sequence $\{\phi_m\}_{m\ge 0}\subset\mathcal{S}_I(\mathbf{R}_{>0})$ converging to $\phi$ and any

$^{12}$There should really be a lemma after that earlier Definition which explains such consequences (4), (5), (6) using terminology and notation that makes sense back there.

$^{13}$clarify how the Identity Theorem is being used, via “injectvity” of $\phi\mapsto M(\phi)$ and $\log(t)=o(t^\varepsilon)$ as $t\to+\infty$ for all $\varepsilon>0$.

## PDF page 803

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH $I$-EXPONENTIAL DECAY** · **803**

$\sigma\in (a,b)$, which implies convergence in $A\mathcal{S}(\mathbf{C}_I)$ by design of the Hausdorff locally convex topology on $A\mathcal{S}(\mathbf{C}_I)$ from Definition D.3.1.3. Since $\mathcal{S}(\mathbf{C}_I)$ is a Fréchet space, as is $\mathcal{S}_I(\mathbf{R}_{>0})$ by Lemma D.3.2.3(1), sequential continuity of $M_I$ implies it is continuous. Thus, by the Open Mapping Theorem for Fréchet spaces, the continuous bijection $M_I$ is a linear topological isomorphism. $\square$

DEFINITION D.3.2.6 (Fourier-Mellin transform on $\mathcal{S}_I(\mathbf{R}_{>0})$). Let $I\subset\mathbf{R}$ be a non-empty open interval. We define the *Fourier-Mellin transform* on $\mathcal{S}_I(\mathbf{R}_{>0})$ to be the linear topological isomorphism $M_I$ from (D.3.2.2).

D.3.2.3. *Fundamental families of continuous seminorms on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$.* Next we provide a countable family of seminorms on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$ that generate its Hausdorff locally convex topology from Lemma D.3.2.3(6) for $I=\mathbf{R}$ (as $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})=\mathcal{S}_I(\mathbf{R}_{>0})$ for $I=\mathbf{R}$).

LEMMA D.3.2.7 (Countable fundamental families of seminorms on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$). *For $a\in\mathbf{R}_{>0}$, $b\in\mathbf{R}_{\ge 0}$, and $m\ge 0$ an integer, define $\lVert\cdot\rVert_{a,m}$ and $\lVert\cdot\rVert_{a,b,m}$ on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$ by*

$$
\lVert\phi\rVert_{a,m}:=\left(\int_{\mathbf{R}_{>0}}|(t\partial_t)^m\phi(t)|^2\max\{t,t^{-1}\}^{2a}\,\frac{\mathrm{d}t}{t}\right)^{1/2}
\tag{D.3.2.3}
$$

*and*

$$
\lVert\phi\rVert_{a,b,m}:=\left(\int_{\mathbf{R}_{>0}}|(t\partial_t)^m\phi(t)|^2\max\{t,t^{-1}\}^{2a}|\log(t)|^{2b}\,\frac{\mathrm{d}t}{t}\right)^{1/2}
\tag{D.3.2.4}
$$

*(note that $\lVert\cdot\rVert_{a,0,m}=\lVert\cdot\rVert_{a,m}$). Then*

(1) *$\lVert\cdot\rVert_{a,m}$ and $\lVert\cdot\rVert_{a,b,m}$ are finite on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$ (hence seminorms) and continuous.*

(2) *The collection $\{\lVert\cdot\rVert_{a,m}\}$ as $a$ varies over a countable subset $\{a_k\}_{k\ge 0}$ of positive real numbers such that $\limsup_{k\ge 0}a_k=+\infty$ and $m\ge 0$ varies over all the nonnegative integers generates on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$ its Hausdorff locally convex topology.*

(3) *The collection $\{\lVert\cdot\rVert_{a,b,m}\}$ as $a$ varies over a countable subset $\{a_k\}_{k\ge 0}$ of positive real numbers such that $\limsup_{k\ge 0}a_k=+\infty$, $b\ge 0$ varies over the nonnegative integers, and $m\ge 0$ varies over the nonnegative integers generates on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$ its Hausdorff locally convex topology.*

PROOF. (1) : We have the inequalities:

$$
\lVert\phi\rVert_{a,m}\le\left(\int_{[1,+\infty)}|(t\partial_t)^m\phi(t)|^2t^{2a}\,\frac{\mathrm{d}t}{t}\right)^{1/2}+\left(\int_{(0,1)}|(t\partial_t)^m\phi(t)|^2t^{-2a}\,\frac{\mathrm{d}t}{t}\right)^{1/2}
\tag{D.3.2.5}
$$

$$
\le\left(\int_{\mathbf{R}_{>0}}|(t\partial_t)^m\phi(t)|^2t^{2a}\,\frac{\mathrm{d}t}{t}\right)^{1/2}+\left(\int_{\mathbf{R}_{>0}}|(t\partial_t)^m\phi(t)|^2t^{-2a}\,\frac{\mathrm{d}t}{t}\right)^{1/2}
$$

and

$$
\lVert\phi\rVert_{a,b,m}\le\left(\int_{[1,+\infty)}|(t\partial_t)^m\phi(t)|^2t^{2a}|\log(t)|^{2b}\,\frac{\mathrm{d}t}{t}\right)^{1/2}+\left(\int_{(0,1)}|(t\partial_t)^m\phi(t)|^2t^{-2a}|\log(t)|^{2b}\,\frac{\mathrm{d}t}{t}\right)^{1/2}
\tag{D.3.2.6}
$$

$$
\le\left(\int_{\mathbf{R}_{>0}}|(t\partial_t)^m\phi(t)|^2t^{2a}|\log(t)|^{2b}\,\frac{\mathrm{d}t}{t}\right)^{1/2}+\left(\int_{\mathbf{R}_{>0}}|(t\partial_t)^m\phi(t)|^2t^{-2a}|\log(t)|^{2b}\,\frac{\mathrm{d}t}{t}\right)^{1/2}.
$$

This proves that the integrals defining $\lVert\cdot\rVert_{a,m}$ and $\lVert\cdot\rVert_{a,b,m}$ converge on any $\phi\in\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$, and that the resulting seminorms are continuous. In particular, the topology defined in (2) is coarser than the topology on $\mathcal{S}_\mathrm{E})\mathbf{R}_{>0})$. This completes the proof of (1).

## PDF page 804

**804** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

Since $\lVert\cdot\rVert_{a,0,m}=\lVert\cdot\rVert_{a,m}$ and clearly (2) implies (3), it remains to prove (2). For each real number $c$ and each integer $m\ge 0$ we have

$$
\left(\int_{\mathbf{R}_{>0}}|(t\partial_t)^m\phi(t)|^2t^{2c}\,\frac{\mathrm{d}t}{t}\right)^{1/2}\le\left(\int_{\mathbf{R}_{>0}}|(t\partial_t)^m\phi(t)|^2\max\{t,t^{-1}\}^{2|c|}\,\frac{\mathrm{d}t}{t}\right)^{1/2}.
\tag{D.3.2.7}
$$

By Lemma D.3.1.2 (with $p=2$), Remark D.3.1.4 and Proposition D.3.2.5, the topology generated by the $\lVert\cdot\rVert_{a,m}$'s as $a\in\mathbf{R}$ varies over a sequence of nonnegative real numbers $\{a_k\}_{k\ge 0}$ such that $\limsup_{k\ge 0}a_k=+\infty$ and $m$ varies over the nonnegative integers is finer than the topology on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$. $\square$

**D.3.3. Schwartz-Bruhat functions with $I$-exponential decay on $\mathbf{R}_{>0}$-modulated groups.** We let $(G,|\cdot|_G)$ be a modulated group and throughout this subsection we assume the module $|\cdot|_G:G\to\mathbf{R}_{>0}$ is surjective. We refer to such $(G,|\cdot|_G)$ as an *$\mathbf{R}_{>0}$-modulated group*. All examples of modulated groups arising throughout this work fulfill this assumption.

Note that upon choosing a continuous homomorphic section $\tau$ to the module $|\cdot|_G$ of $G$ we get an isomorphism of topological groups $\alpha_\tau:G\simeq\mathbf{R}_{>0}\times G^1$. In particular, $G$ is compactly generated (even if $G$ isn't assumed to be second-countable) since $G^1$ is compact Hausdorff. Any compact subgroup $k\subset G$ is contained inside $G^1$ since $\mathbf{R}_{>0}$ has no non-trivial compact subgroup, and the orthogonal of $k$ in $\widehat{G}$ is in turn identified with the direct product of $\widehat{\mathbf{R}_{>0}}\simeq\mathbf{R}$ and the orthogonal of $k$ in the discrete $\widehat{G^1}$ since the formation of dual groups respects direct products and $G=\mathbf{R}_{>0}\times G^1$ via $\tau$.

Thus, the condition that the subgroup $k^\perp\subset\widehat{G}$ is compactly generated is the same as the condition that the orthogonal of $k$ in $\widehat{G^1}$ is compactly generated. Since $G^1$ is compact, so $\widehat{G^1}$ is discrete, the orthogonal of $k$ in $\widehat{G^1}$ is discrete. It follows that the subgroup $k^\perp\subset\widehat{G}$ is compactly generated if and only if the orthogonal of $k$ in $\widehat{G^1}$ is finitely generated.

DEFINITION D.3.3.1 (Schwartz-Bruhat functions with $I$-exponential decay on $\mathbf{R}_{>0}$-modulated groups). Let $(G,|\cdot|_G)$ be an $\mathbf{R}_{>0}$-modulated group. Let $I\subset\mathbf{R}$ be a non-empty interval. We define $\mathcal{S}_I(G)$ to be the $\mathbf{C}$-vector space of those continuous functions $\phi$ on $G$ satisfying $|\cdot|_G^a\phi\in\mathcal{S}(G)$ for all $a\in I$. We refer to $\mathcal{S}_I(G)$ as the $\mathbf{C}$-vector space of *Schwartz-Bruhat functions on $G$ with $I$-exponential decay*. Similarly to Example D.3.2.2, $\mathcal{S}_I(G)$ has a left $G$-action via $(g.\phi)(x)=\phi(g^{-1}x)$.

(1) For $I=[0,+\infty)$, we write $\mathcal{S}_{\mathrm{SE}}(G):=\mathcal{S}_I(G)$ and refer to its elements as Schwartz-Bruhat functions on $G$ with *forward semi-exponential decay*.

(2) For $I=(-\infty,0]$, we write $\check{\mathcal{S}}_{\mathrm{SE}}(G):=\mathcal{S}_I(G)$ and refer to its elements as Schwartz-Bruhat functions on $G$ with *backward semi-exponential decay*.

(3) For $I=\mathbf{R}$, we write $\mathcal{S}_\mathrm{E}(G):=\mathcal{S}_I(G)$ and refer to its elements as Schwartz-Bruhat functions on $G$ with *exponential decay*.

For $G=\mathbf{R}_{>0}$ this definition of $\mathcal{S}_I(G)$ coincides with Definition D.3.2.1. In that special case, we saw in the proof of the Fréchet property for $\mathcal{S}_I(\mathbf{R}_{>0})$ in Lemma D.3.2.3(1) that membership in $\mathcal{S}_{[a,b]}(\mathbf{R}_{>0})$ amounts to membership in $\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})$ and $\mathcal{S}_{\{b\}}(\mathbf{R}_{>0})$. The same holds in general:

LEMMA D.3.3.2. *For an $\mathbf{R}_{>0}$-modulated group $G$ and real numbers $a<c<b$, if $\phi:G\to\mathbf{C}$ satisfies $|\cdot|_G^a\phi,|\cdot|_G^b\phi\in\mathcal{S}(G)$ then $|\cdot|_G^c\phi\in\mathcal{S}(G)$.*

PROOF. By renaming $|\cdot|_G^a\phi$ as $\phi$ and replacing the modulus with $|\cdot|_G^{b-a}$, we have to show that if $\phi,|\cdot|_G\phi\in\mathcal{S}(G)$ then $|\cdot|_G^c\phi\in\mathcal{S}(G)$ for all $0<c<1$. By definition of $\mathcal{S}(G)$, there exists a compact subgroup $k\subset G$ with $k^\perp$ compactly generated such that $\phi$ is $k$-invariant. Since $|\cdot|_G$ is trivial on $k$, we can pass to $G/k=\mathbf{R}_{>0}\times (G^1/k)$ so that $G^1$ is an elementary abelian Lie group.

Using $\mathbf{R}\simeq\mathbf{R}_{>0}$ via $e^x$, we can arrange that $G=\mathbf{R}^m\times\mathbf{T}^n\times\mathbf{Z}^r\times F$ for integers $m\ge 1$, $n\ge 0$, $r\ge 0$, and a finite abelian group $F$ with the modulus given by $|(x,z,a,b)|=e^{x_1}$. We are given $\phi(x,z,a,b)\in\mathcal{S}(G)$ such

## PDF page 805

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH $I$-EXPONENTIAL DECAY** · **805**

that $e^{x_1}\phi(x,z,a,b)\in\mathcal{S}(G)$ and want to show that if $0<c<1$ then $e^{cx_1}f(x,z,a,b)\in\mathcal{S}(G)$. The calculation used to treat the case $G=\mathbf{R}$ in the proof of Lemma D.3.2.3(1) carries over essentially without change to the present more general setting using the seminorms (D.1.3.8)). One difference from the case $G=\mathbf{R}$ is that when $m>1$ or $r>0$ we can “go out to infinity” while keeping $x_1$ bounded or even equal to $0$ but the required decay estimates still carry through. $\square$

We fix an $\mathbf{R}_{>0}$-modulated group $G$ and now topologize $\mathcal{S}_I(G)$ by following the same approach used to topologize the Schwartz-Bruhat space of $G$.

DEFINITION D.3.3.3 (Topology on $\mathcal{S}_I(G)$). Let $G$ be an $\mathbf{R}_{>0}$-modulated group, $k\subset G$ a compact subgroup with compactly generated orthogonal $k^\perp\subset\widehat{G}$. We define

$$
\mathcal{S}_I(k,G)\subset\mathcal{S}_I(G)
\tag{D.3.3.1}
$$

to be the linear subspace of $k$-invariant Schwartz-Bruhat functions with $I$-exponential decay. We topologize $\mathcal{S}_I(k,G)$ with the projective topology induced by the linear operators

$$
T_a:\mathcal{S}_I(k,G)\to\mathcal{S}(k,G)=\mathcal{S}(G/k)
\tag{D.3.3.2}
$$

assigned by $T_a(\phi):=|\cdot|_G^a\phi$.

We topologize $\mathcal{S}_I(G)$ as the locally convex inductive limit of the family $\{\mathcal{S}_I(k,G)\}_k$ of linear subspaces of $\mathcal{S}_I(G)$ as $k\subset G$ varies over the compact subgroups with finitely generated orthogonal, partially ordered by downward inclusion. (The inductive limit is $\mathcal{S}_I(G)$ as a vector space since whether or not a given function $f:G\to\mathbf{C}$ is $k$-invariant is the same as for $|\cdot|_G^af$ for $a\in\mathbf{R}$ because $|\cdot|_G$ is trivial on $k$.) We refer to this topology on $\mathcal{S}_I(G)$ as the *inductive topology* on $\mathcal{S}_I(G)$.

EXAMPLE D.3.3.4. When the preceding topology on $\mathcal{S}_I(G)$ is applied to the modulated group $G=\mathbf{R}_{>0}$ with $|\cdot|_G:G\to\mathbf{R}_{>0}$ the identity map, it recovers the topology in Definition D.3.2.1 since $\mathbf{R}_{>0}$ has no non-trivial compact subgroups.

EXAMPLE D.3.3.5. For any $a\in\mathbf{R}$, multiplication by $|\cdot|_G^a$ carries $\mathcal{S}_{\{a\}}(G)$ linearly and topologically isomorphically onto $\mathcal{S}(G)$ (as functions on $G$, $\mathcal{S}_{\{a\}}(G)=|\cdot|_G^{-a}\mathcal{S}(G)$). For $a,b\in\mathbf{R}$, correspondingly multiplication by $|\cdot|_G^{a-b}$ carries $\mathcal{S}_{\{a\}}(G)$ linearly and topologically isomorphically onto $\mathcal{S}_{\{b\}}(G)$.

For $I=[a,b]$, the space $\mathcal{S}_I(k,G)$ is identified via $f\mapsto (f,f)$ linearly and topologically with a closed subspace of $\mathcal{S}_{\{a\}}(k,G)\times\mathcal{S}_{\{b\}}(k,G)$. To prove this, by passing to $G/k=\mathbf{R}_{>0}\times (G^1/k)$ as in the proof of Lemma D.3.3.2 we can carry over the same considerations with $e^{cx}$ for $0\le c\le 1$ as in the proof of the closed embedding property for the case $G=\mathbf{R}_{>0}$ that arose in the proof of the Fréchet condition in Lemma D.3.2.3(1).

A general non-empty interval $I\subset\mathbf{R}$ is exhausted by countably many compact intervals, so we can similarly conclude that $\mathcal{S}_I(k,G)$ is a closed subspace of a *countable* direct product of copies of the space $\mathcal{S}(k,G)=\mathcal{S}(G/k)$ that is nuclear Fréchet, so $\mathcal{S}_I(k,G)$ is nuclear [Scha, Ch. III, 7.4] and Fréchet. It likewise follows that $\mathcal{S}_I(k,G)$ is separable (i.e., has a countable dense subset) since every subset of a separable metric space is separable and each metric space $\mathcal{S}(G/k)$ is separable by (D.1.3.20) (ultimately because the spaces $\mathcal{S}(\mathbf{Z})\simeq\mathcal{S}(\mathbf{T})$ and $\mathcal{S}(\mathbf{R})$ are separable).$^{14}$

Since the transition maps $\mathcal{S}(k,G)\to\mathcal{S}(k',G)$ for $k'\subset k$ are topological embeddings, the same holds for $\mathcal{S}_I(k,G)\to\mathcal{S}_I(k',G)$. Thus, when $G$ is second-countable we see that the topology on $\mathcal{S}_I(G)$ is a countable strict inductive limit. Continuing to assume $G$ is second-countable, since each $\mathcal{S}_I(k,G)$ is topologized as a projective limit of copies of the Hausdorff locally convex space $\mathcal{S}(k,G)=\mathcal{S}(G/k)$ that is nuclear and complete (see Lemma D.1.3.7(3) applied to the elementary abelian Lie group $G/k$) it follows that each of the spaces $\mathcal{S}_I(k,G)$

$^{14}$Need to give reference for $\mathcal{S}(\mathbf{R})$ being separable.

## PDF page 806

**806** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

and then their countable strict inductive limit $\mathcal{S}_I(G)$, is both nuclear and complete [Scha, Ch. III, Cor. to 7.4; Ch. II, 5.3, 6.6].

REMARK D.3.3.6. Let $G$ be an $\mathbf{R}_{>0}$-modulated group and $I\subset\mathbf{R}$ a non-empty interval. For every $a\in\mathbf{R}$, the linear operation $\phi\mapsto |\cdot|_G^a\cdot\phi$ carries each $\phi\in\mathcal{S}_I(G)$ to a smooth function on $G$ and so this operation takes value within $\mathcal{S}_{-a+I}(G)$. By design of the topology on $\mathcal{S}_I(G)$ and $\mathcal{S}_{-a+I}(G)$ from Definition D.3.3.1, this operator is a linear topological isomorphism $M_a:\mathcal{S}_I(G)\to\mathcal{S}_{-a+I}(G)$. In particular, $\mathcal{S}_\mathrm{E}(G)$ is stable under multiplication by continuous quasi-characters of arbitrary exponent, and multiplication by any of them is a linear topological automorphism.

D.3.3.1. *The main Structure Theorem on Schwartz-Bruhat functions with $I$-exponential decay.* The topological space of $\Omega(G)$ of continuous quasi-characters of any modulated group $(G,|\cdot|_G)$ is endowed with a natural structure of Riemann surface, namely the open subsets $\{|\cdot|_G^s\chi_0\}$ for $\chi_0\in\widehat{G^1}$ (these are the connected components) have the topology of either infinite cylinders (when the image of $|\cdot|_G$ is discrete) or $\mathbf{C}$ (in the $\mathbf{R}_{>0}$-modulated case). In the latter case, the connected components are the fibers of the continuous surjective restriction map $\Omega(G)\to\Omega(G^1)=\widehat{G^1}$.

In the $\mathbf{R}_{>0}$-modulated case, using unitary base points $\chi_0$ yields a well-defined function $\mathrm{Re}:\Omega(G)\to\mathbf{R}$ via $|\cdot|_G^s\chi_0\mapsto\mathrm{Re}(s)$ (this is the usual “real part” on copies of $\mathbf{C}$ whose base point has an ambiguity corresponding to vertical translation). For any non-empty interval $I\subset\mathbf{R}$ we then denote by $\Omega(G)_I$ the subset of points in $\Omega(G)$ whose “real part” belongs to $I$ (this is a copy of $\mathbf{C}_I\subset\mathbf{C}$ for each connected component of $\Omega(G)$). We endow the interior of $\Omega(G)_I$ inside $\Omega(G)$, if non-empty, with the structure of Riemann surface inherited from the ambient $\Omega(G)$.

THEOREM D.3.3.7 (Structure of $\mathcal{S}_I(G)$ for $\mathbf{R}_{>0}$-modulated groups). *Let $I\subset\mathbf{R}$ be a non-empty interval. Let $(G,|\cdot|_G)$ be a second-countable $\mathbf{R}_{>0}$-modulated group and $\tau$ a continuous homomorphic section to the module homomorphism $|\cdot|_G:G\to\mathbf{R}_{>0}$. Then:*

(1) *the choice of section $\tau$ induces a linear topological isomorphism:*

$$
\mathcal{S}(G^1)\,\overline{\otimes}\,\mathcal{S}_I(\mathbf{R}_{>0})\xrightarrow{\simeq}\mathcal{S}_I(G)
\tag{D.3.3.3}
$$

*compatible with the left-translation action of $G^1\times\mathbf{R}_{>0}$ on the source through the first and second projection and on the tensor factors, and of $G$ on the target,$^{15}$ and promoting the following diagram:*

(D.3.3.4)

```latex
\begin{tikzcd}
\mathcal{S}(k,G^1)\,\overline{\otimes}\,\mathcal{S}_I(\mathbf{R}_{>0}) \arrow[r] \arrow[d] & \mathcal{S}_I(k,G) \arrow[d] \\
\mathcal{S}(G^1)\,\overline{\otimes}\,\mathcal{S}_I(\mathbf{R}_{>0}) \arrow[r] & \mathcal{S}_I(G)
\end{tikzcd}
```

*to a commutative diagram of continuous linear maps whose horizontal arrows are linear topological isomorphisms.*

*Each bounded subset in $\mathcal{S}_I(G)$ is contained in some $\mathcal{S}_I(k,G)$, which in turn is the image of the space*

$$
\mathcal{S}(k,G^1)\,\overline{\otimes}\,\mathcal{S}_I(\mathbf{R}_{>0})\simeq\mathcal{S}(k,G^1)\,\widehat{\otimes}_\pi\,\mathcal{S}_I(\mathbf{R}_{>0})
\tag{D.3.3.5}
$$

*under (D.3.3.3) for $k\subset G^1$ a compact subgroup such that $k^\perp$ is compactly generated (this is a topological isomorphism by Corollary C.2.3.12).*

(2) *The Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}_I(G)$ is complete, nuclear, and Montel and a strict LF-space. In particular, it is barrelled and bornological. If $G^1$ has compactly generated dual group then $\mathcal{S}_I(G)$ is a nuclear Fréchet space.*

$^{15}$Somewhere perhaps the continuity of $G$-action on $\mathcal{S}_I(G)$ for the inductive topology should be addressed.

## PDF page 807

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH $I$-EXPONENTIAL DECAY** · **807**

(3) *The Hausdorff strong dual $\mathcal{S}_I(G)'_\beta$ is complete, nuclear and Montel.*

(4) *If $0\in I$ then $\mathcal{S}_I(G)$ is naturally a linear subspace of $\mathcal{S}(G)$ and the injective linear inclusion $\mathcal{S}_I(G)\subset\mathcal{S}(G)$ is continuous. If $I$ is compact then the inductive topology on $\mathcal{S}_I(G)$ is equal to the projective topology induced by the linear maps $T_a:\mathcal{S}_I(G)\to\mathcal{S}(G)$ assigned by $T_a(\phi):=|\cdot|_G^a\phi$, for every $a\in I$.*

REMARK D.3.3.8. The usefulness of the second-countability assumption has been seen in the preceding discussion, and it also provides a cofinal *sequence* of compact subgroups $k_m\subset G^1$ with compactly generated (equivalently finitely generated) orthogonal in $\widehat{G^1}$. This allows reductions to the case that $G$ is an elementary abelian Lie group via Corollary C.2.3.12 and Proposition C.2.3.13.

REMARK D.3.3.9 (On the role of acyclicity of Schwartz-Bruhat spacess). In §C.1.5, we discussed inductive limits of Hausdorff locally convex topological $\mathbf{C}$-vector spaces, and the concept of acyclicity, one of whose applications is to provide a criterion to detect limit subspaces of LF-spaces (i.e. closed subspaces whose subspace topology is itself the LF-topology induced from the ambient): see Corollary C.1.5.13.

In Proposition D.1.5.9, we proved that for any Hausdorff locally compact second countable abelian group, the Schwartz-Bruhat space $\mathcal{S}(G)$ is acyclic, because it is a countable strict inductive limit of Fréchet spaces (strictness is the key point).

Acyclicity of the Schwartz-Bruhat space of $G^1$ will be used in proving part (4) of Theorem D.3.3.7 by realizing $\mathcal{S}_I(G)$ as a limit subspace of a strict LF-space, hence itself an LF-space. This will enable us to apply the Open Mapping Theorem (see [Gro-f, Ch. 4, §5, Thm. 2(1)]) to the continuous linear bijection from (D.3.3.3) with $\mathcal{S}_I(G)$ re-topologized as in part (4).

Before we prove Theorem D.3.3.7, we discuss the following aspect on $\mathcal{S}_I(G)$. We defined on $\mathcal{S}_I(G)$ the inductive topology. There is another natural topology on $\mathcal{S}_I(G)$, whose nature is projective. One part of the following result is that (at least for second-countable $G$) both topologies have the same bounded subsets.$^{16}$

PROPOSITION D.3.3.10 (On the bounded subsets of $\mathcal{S}_I(G)$). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $\tau$ be a choice of continuous homomorphic section to the module $|\cdot|_G$. The canonical continuous linear map*

$$
\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)\to\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)
\tag{D.3.3.6}
$$

*is a bijection identifying bounded subsets in both directions.*

*For $k\subset G$ a compact subgroup with compactly generated orthogonal, the canonical continuous linear map*

$$
\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(k,G^1)\to\mathcal{S}_I(k,G)
\tag{D.3.3.7}
$$

*is a linear topological isomorphism onto the separable nuclear Fréchet space $\mathcal{S}_I(k,G)$.*

(1) *The bounded subsets of $\mathcal{S}_I(G)$ are separable and metrizable.*

(2) *The bounded subsets of $\mathcal{S}_I(G)$ are the same with respect to the inductive topology and with respect to the coarser projective topology $\mathscr{T}$ on $\mathcal{S}_I(G)$ induced by the continuous linear maps $T_a:\mathcal{S}_I(G)\to\mathcal{S}(G)$ assigned by $T_a(\phi):=|\cdot|_G^a\phi$ for every $a\in I$.*

(3) *$B\subset\mathcal{S}_I(G)$ is bounded if and only if $T_a(B)$ is bounded in $\mathcal{S}(G)$ for every $a\in I$, equivalently for every $a\in J$ with $J\subset I$ a countable subset such that the endpoints of $I$ are accumulation points for $J$.*

That each $\mathcal{S}_I(k,G)$ is separable nuclear Fréchet was addressed in Example D.3.3.5.

PROOF. (1) : Since $G$ is second-countable, there exists a cofinal sequence $\{k_m\}_{m\ge 0}$ of compact subgroups satisfying $k_{m+1}\subset k_m$ for every integer $m\ge 0$ with each $k_m^\perp$ is compactly generated. The natural map $\varinjlim_{m\ge 0}\mathcal{S}_I(k_m,G)\to\mathcal{S}_I(G)$ is then a linear topological isomorphism with each $\mathcal{S}_I(k_m,G)\to\mathcal{S}_I(G)$ a topological

$^{16}$Somewhere should continuity of $G$-action on $\mathcal{S}_I(G)$ for the projective topology be addressed?

## PDF page 808

**808** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

embedding [Scha, Ch. II, 6.4]. By [Scha, Ch. II, 6.5], a subset $B\subset\mathcal{S}_I(G)$ is bounded if and only if there exists an integer $m_0\ge 0$ and a bounded subset $B_0\subset\mathcal{S}_I(k_{m_0},G)$ such that $B$ is the image of $B_0$ under the linear topological embedding $\mathcal{S}_I(k_{m_0},G)\to\mathcal{S}_I(G)$. Since $\mathcal{S}_I(k_{m_0},G)$ is a separable Fréchet space, its topological subspace $B_0$ is then also separable and metrizable. This proves (1).

Before proving (2), we show that the canonical continuous linear map in (D.3.3.6) is a bijection. The argument we give uses the same idea as the proof of [Gro-b, Ch. I, §3, No. 1, Prop. 14.II, p. 76]. As a first step, we rewrite the source and target spaces each in a more convenient form. For the source, since $\mathcal{S}_I(\mathbf{R}_{>0})$ and each $\mathcal{S}(k,G^1)$ are nuclear Fréchet with $\{\mathcal{S}(k_m,G^1)\}$ a countable strict inductive system for $\{k_m\}$ as in the proof of (1), the end of Proposition C.2.3.13(2) gives that the natural linear map

$$
\varinjlim \mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(k,G^1)\to\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)
$$

is a topological isomorphism. By Corollary C.2.3.12, the completed inductive tensor products in the inductive limit on the left can each be replaced with the corresponding completed projective tensor product.

Now we harness properties of $\mathcal{S}_I(\mathbf{R}_{>0})$ and its strong dual to rewrite those completed tensor products, as well as the one in the target of (D.3.3.6). Recall from Lemma D.3.2.3(1,2) that $\mathcal{S}_I(\mathbf{R}_{>0})$ is Montel (hence reflexive), nuclear and complete, and its strong dual $\mathcal{S}_I(\mathbf{R}_{>0})'_\beta$ (whose own dual is $\mathcal{S}_I(\mathbf{R}_{>0})$ by reflexivity of the latter) is complete and barrelled (as it is reflexive, hence barrelled [Scha, Ch. IV, 5.6]). Thus, for any complete Hausdorff locally convex space $F$ (such as $\mathcal{S}(G^1)$ or $\mathcal{S}(k,G^1)$) it follows from [Tre, Prop. 50.5, p. 522] that the natural map

$$
\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi F\to\mathscr{L}_b(\mathcal{S}_I(\mathbf{R}_{>0})'_\beta,F)
$$

to the space of continuous linear maps $\mathcal{S}_I(\mathbf{R}_{>0})'_\beta\to F$ (topologized by uniform convergence on bounded subsets of $\mathcal{S}_I(\mathbf{R}_{>0})'_\beta$) is a topological isomorphism.

The map we want to show is a bijection is thereby linearly and topologically identified with the natural map

$$
\varinjlim \mathscr{L}_b(\mathcal{S}_I(\mathbf{R}_{>0})'_\beta,\mathcal{S}(k,G^1))\to\mathscr{L}_b(\mathcal{S}_I(\mathbf{R}_{>0})'_\beta,\mathcal{S}(k,G^1)).
$$

The injectivity is now clear, and it remains to show that every continuous linear map $\mathcal{S}_I(\mathbf{R}_{>0})'_\beta\to\mathcal{S}(G^1)$ lands inside one of the subspaces $\mathcal{S}(k,G^1)$.

Define $E:=\mathcal{S}_I(\mathbf{R}_{>0})$. Let $p$ be a continuous *norm* (not just seminorm) on $E$; e.g., pullback along $\mathcal{S}_I(\mathbf{R}_{>0})\hookrightarrow\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})\simeq\mathcal{S}(\mathbf{R}_{>0})$ of the sup-norm on the latter. For the closed unit ball $U\subset E$ with respect to $p$, we claim that the linear span $W$ of the polar $U^\circ:=\{\ell\in E':|\ell(U^\circ)|\le 1\}$ in the dual $E'$ is dense for the strong-dual topology. (Although references may differ on whether the “polar” is taken in a real or complex sense [NB, Def. 8.3.1, Rem. 8.3.2], since $U$ is circled the meanings of $U^\circ$ and $U^{\circ\circ}$ are the same for both notions.) By the Hahn-Banach Theorem, it is the same to show that a continuous linear functional on $E'_\beta$ vanishing on $W$ (equivalently on $U^\circ$) must be $0$. By semi-reflexivity of $E$, the continuous linear functionals on $E'_\beta$ are the same as on $E'_\sigma$ [Scha, Ch. IV, 5.5]. Thus, it is the same to show $W$ is dense in $E'$ for the weak topology $\sigma(E',E)$. The continuous dual of $E'_{\sigma(E',E)}$ is $E$ [Scha, Ch. IV, 1.2], so we want to show that if $x\in E$ annihilates $W$ (or equivalently $U^\circ$) then $x=0$.

For any such $x$, the line $\mathbf{R}x$ lies inside the bipolar $U^{\circ\circ}$. Since $U$ is convex and closed for the given topology of $E$, it is also closed for the weak topology $\sigma(E,E')$ [Scha, Ch. IV, 3.1]. Thus, by the Bipolar Theorem (see [Scha, Ch. IV, 1.5] for the real case, and [NB, Thm. 8.3.8] for the complex case) we have $U^{\circ\circ}=U$. The condition $\mathbf{R}x\subset U$ then forces $x=0$ since $U$ is the closed unit ball for a norm on $E$. This completes the proof that $U^\circ$ has dense span in $E'_\beta$. Each topologically embedded subspace $\mathcal{S}(k,G^1)\subset\mathcal{S}(G^1)$ is complete and hence closed, so to show that a continuous $T:E'_\beta\to\mathcal{S}(G^1)$ has image contained in some $\mathcal{S}(k,G^1)$ it suffices by our density conclusion to show $T(U^\circ)$ is contained in some $\mathcal{S}(k,G^1)$.

Since $T$ is continuous, it carries bounded sets onto bounded sets. Every bounded subset of $\mathcal{S}(G^1)$ is contained in some $\mathcal{S}(k,G^1)$ by [Scha, Ch. ,II, 6.5], so it suffices to show that the polar $U^\circ$ of the closed unit

## PDF page 809

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH $I$-EXPONENTIAL DECAY** · **809**

ball $U$ for the continuous norm $p$ on $E$ is bounded in the topology of $E'_\beta$. This strong dual has topological dual $E$ since $E$ is reflexive, and by [Scha, Ch. IV, 3.3] boundedness in a Hausdorff locally convex space is equivalent to weak-boundedness, which is to say boundedness under all continuous linear functionals. This says that for all $x\in E$, as $\ell$ varies in $U^\circ$ then the values $\ell(x)$ in $\mathbf{C}$ are bounded. We can scale $x$ to lie in $U$ since it is a $0$-neighborhood for the topology of $E$, so then by definition of $U^\circ$ we have $|\ell(x)|\le 1$ for all such $\ell$. This completes the proof that (D.3.3.6) is bijective.

Next we show that under the bijection (D.3.3.6), bounded sets match on both sides. The preceding discussion found two topologies on the linear space underlying $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$: the strict-LF topology induced by the continuous linear bijection (D.3.3.6), and the projective tensor topology. That strict LF-topology is finer than the projective tensor product topology since (D.3.3.6) is continuous. Since the strict-LF topology on $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ is ultrabornological,$^{17}$ it is finer than the topology topology $\mathscr{T}^{\mathrm{ubor}}_\pi$ that is coarsest among the ultrabornological topologies on $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ that are finer than the projective tensor topology; the topology $\mathscr{T}^{\mathrm{ubor}}_\pi$ is constructed at the start of [Jar, §13.3] as a locally convex inductive limit of Banach spaces, so it is an LF-space topology.$^{18}$

By the Open Mapping Theorem for LF-spaces (see [Gro-f, Ch. 4, §5, Thm. 2(1), p. 148]), the continuous linear bijection

$$
\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)\to (\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1),\mathscr{T}^{\mathrm{ubor}}_\pi)
$$

between LF-spaces is a linear topological isomorphism. By [Jar, §13.3, Prop. 1(b)], $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ with its given topology and with the topology $\mathscr{T}^{\mathrm{ubor}}_\pi$ have the same Banach disks,$^{19}$ so it follows that $\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)$ and $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ have the same Banach disks via the continuous bijection between them.

Let $B\subset\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ be a bounded subset. We want to show its preimage under the bijection (D.3.3.6) is also bounded. It is harmless to replace $B$ with a larger bounded subset, so we may replace $B$ with its convex circled hull to arrange that $B$ is also convex and circled (a “disk” in the terminology of [NB, Def. 4.2.7]). Its closure is also bounded [Scha, Ch. I, 5.1(ii)], so we may further assume $B$ is closed. But then $B$ is complete since $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ is complete, so $B$ is sequentially complete. As such it is a Banach disk in $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ by [NB, Thm. 13.1.2(b)], so the corresponding pre-image in $\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)$ is also a Banach disk by the foregoing. Since by definition Banach disks in a locally convex space are bounded, we have shown that $\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)$ and $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ have the same bounded subsets. In particular, the coarsest bornological topology $\mathscr{T}^{\mathrm{bor}}$ that is finer than the projective tensor topology on $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ (this is constructed in [Jar, §13.3, Prop. 1(a)]) is already ultrabornological.$^{20}$

(2) : Since the identity map on $\mathcal{S}_I(G)$ is continuous when going from the inductive topology to the projective topology, bounded sets for the former are bounded for the latter. The main issue is therefore to show that a bounded set $B$ for the projective topology arises from a bounded set in the inductive topology, and more specifically that any such $B$ arises from $\mathcal{S}_I(k,G)$ for some compact subgroup $k\subset G$ with compactly generated orthogonal. By design, the bounded sets for the projective topology are the preimages of bounded sets under the linear injection

$$
\mathcal{S}_I(G)\hookrightarrow\prod_{a\in I}\mathcal{S}(G).
$$

Bounded subsets of arbitrary products of topological vector spaces are precisely subsets of products of bounded subsets of the factors [Scha, Ch. I, 5.5], so we are led to study boundedness inside $\mathcal{S}(G)$ more closely.

$^{17}$Is this the same as what Grothendieck calls “strictly bornological”? Does it require a countability condition? Reference for various definitions?

$^{18}$Why are the members of the direct limit construction actually complete? And why is the colimit process “countable” as required in the definition of an LF-space?

$^{19}$Is the reader going to be told what “Banach disks” means?

$^{20}$Why? And why is this last sentence being mentioned? Omit if not actually used: if the reader hasn’t been told what “ultrabornological” means and some relation with being bornological then this cannot be understood.

## PDF page 810

**810** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

The same argument as given above upon replacing for the study of (D.3.3.6), upon replacing $\mathcal{S}_I$ with $\mathcal{S}$, proves that the continuous linear map $\mathcal{S}(G)\simeq\mathcal{S}(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)\to\mathcal{S}(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ is bijective and that the two sides have the same bounded subsets. It follows that so do $\prod_{a\in I}\mathcal{S}(G)$ and $\prod_{a\in I}(\mathcal{S}(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1))$.

By [Jar, §15.4, Thm. 1], completed projective tensor products pass through arbitrary topological products of Hausdorff locally convex spaces, so the natural continuous linear map

$$
(\prod_{a\in I}\mathcal{S}(\mathbf{R}_{>0}))\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)\to\prod_{a\in I}(\mathcal{S}(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1))
$$

is a topological isomorphism. The bounded subsets in the latter thereby give rise to the bounded subsets in the projective topology on $\mathcal{S}_I(G)$. Since $\mathcal{S}(G^1)$ is nuclear, the functor $(\cdot)\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ carries closed embeddings to closed embeddings by [Tre, Prop. 43.7, Thm. 50.1]. Hence, $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)\to (\prod_{a\in I}\mathcal{S}(\mathbf{R}_{>0}))\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ induced by the linear topological embedding $\prod_{a\in I}T_a:\mathcal{S}_I(\mathbf{R}_{>0})\to\prod_{a\in I}\mathcal{S}(\mathbf{R}_{>0})$ is a linear topological embedding. This shows that the inductive topology and the topology $\mathscr{T}$ on $\mathcal{S}_I(G)$ have the same bounded subsets.$^{21}$

(3) : The topology $\mathscr{T}$ on $\mathcal{S}_I(G)$ is equal to the projective topology induced by the linear operators $T_a$ for $a$ varying over $J$ only, as opposed to all of $I$. Thus, we may conclude by using that a subset of a product $\prod E_i$ of topological vector spaces is bounded exactly when its projection into each $E_i$ is bounded [Scha, Ch. I, 5.5] $\square$

PROOF OF THEOREM D.3.3.7. (1) : Since $G$ is $\mathbf{R}_{>0}$-modulated, it is compactly generated and hence $\mathcal{S}(G)$ is the locally convex inductive limit of the $\mathcal{S}(k,G)$ as $k$ varies over the collection of compact subgroups of $G^1$ with compatctly generated $k^\perp$. The analogue holds for $\mathcal{S}_I(G)$ in relation to the $\mathcal{S}_I(k,G)$'s, with each $\mathcal{S}_I(k,G)$ linearly and topologically isomorphic to $\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(k,G^1)$ by (D.3.3.7), and that in turn is identified with $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(k,G^1)$ by Corollary C.2.3.12 since $\mathcal{S}_I(\mathbf{R}_{>0})$ and $\mathcal{S}(k,G^1)$ are Fréchet spaces. Passing to the inductive limit over a countable cofinal system of such $k$'s (as exists since $G$ is second-countable) then yields (D.3.3.3) and the rest of (1), since a bounded subset of a countable strict inductive limit is the same as a bounded subset of one of the layers of the inductive limit [Scha, Ch. II, 6.5].

(2) : In Example D.3.3.5 we saw that each $\mathcal{S}_I(k,G)$ is nuclear Fréchet, so each of these is also barrelled and bornological [Scha, Ch. II, Cor. to 7.1, 8.1] as well as Montel [Tre, Cor. 3 to Prop. 50.2]. The countable strict inductive limit $\mathcal{S}_I(G)$ of such $\mathcal{S}_I(k,G)$'s (so a strict LF-space) is then also complete, nuclear, Montel, barrelled, and bornological, as all of these properties are inherited under countable strict inductive limits (see [Scha, Ch. II, 6.6] for completeness).

Assume now that $G^1$ has compactly generated dual group. Since the dual $\widehat{G^1}$ is discrete, compact generation amounts to being finitely generated, so the dual $G^1$ of $\widehat{G^1}$ has the form $\mathbf{T}^n\times F$ for some $n\ge 0$ and a finite abelian group $F$. In this case $G=\mathbf{R}_{>0}\times G^1$ is an elementary abelian Lie group, so we can take $k=0$; i.e., $\mathcal{S}_I(G)=\mathcal{S}_I(0,G)$ is metrizable.

(3) : Since $\mathcal{S}_I(G)$ is bornological, its strong dual is complete by [Scha, Ch. IV, 6.1], and since $\mathcal{S}_I(G)$ is Montel its strong dual is also Montel [Scha, Ch. IV, 5.9]. To deduce nuclearity of $\mathcal{S}_I(G)'_\beta$, we can argue exactly as in the proof that $\mathcal{S}(G)'_\beta$ is nuclear (Theorem D.1.5.7) to reduce it to the case $G$ is an elementary abelian Lie group. In such cases we have seen $\mathcal{S}_I(G$ is nuclear Fréchet, so its strong dual is nuclear by [Tre, Prop. 50.6].

(4) : Since $0\in I$, we have a continuous linear injective map $\mathcal{S}_I(G)\to\mathcal{S}_{\{0\}}(G)$, and also the linear topological identification $\mathcal{S}_{\{0\}}(G)=\mathcal{S}(G)$ by design of $\mathcal{S}_{\{0\}}(G)$.

Finally, assuming $I=[a,b]$ with $a<b$, we want to show the continuous diagonal inclusion

$$
\mathcal{S}_I(G)\hookrightarrow\mathcal{S}_{\{a\}}(G)\times\mathcal{S}_{\{b\}}(G)\simeq\mathcal{S}(G)\times\mathcal{S}(G)
$$

$^{21}$No, this does not prove it since we have made *no contact* with $\mathcal{S}_I(k,G)$'s. Moreover, there has not been clear contact made between $\mathcal{S}_I(G)$ and $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$, which seems to be invoked here yet is what comes up in the *next* proof, risking an appearance of circularity. The “$\,\overline{\otimes}\,$” version (D.3.3.7) has not been proved either. Too many loose ends.

## PDF page 811

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH $I$-EXPONENTIAL DECAY** · **811**

is a topological embedding. (The analogue for $a=b$ using just one factor on the right side is immediate from the definitions.) The content here is that the source has its topology defined by an inductive limit process, and such colimits do not generally interact well with closed embeddings.

By (D.3.3.3) and its analogous for usual Schwartz-Bruhat spaces in (D.1.8.1), the diagonal inclusion is identified with $(\cdot)\,\overline{\otimes}\,\mathcal{S}(G^1)$ applied to the analogous map

$$
\mathcal{S}_I(\mathbf{R}_{>0})\hookrightarrow\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})\times\mathcal{S}_{\{b\}}(\mathbf{R}_{>0})\simeq\mathcal{S}(\mathbf{R}_{>0})\times\mathcal{S}(\mathbf{R}_{>0})
$$

that was seen to be a closed embedding in the proof of Lemma D.3.2.3(1).

We call $E_1:=\mathcal{S}_I(\mathbf{R}_{>0})$, $E_2:=\mathcal{S}_{\{a\}}(\mathbf{R}_{>0})\times\mathcal{S}_{\{b\}}(\mathbf{R}_{>0})$, and $F:=\mathcal{S}(G^1)$. Then $E_1,E_2$ are both nuclear Fréchet spaces and $F$ is a strict locally convex inductive limit of a sequence of nuclear Fréchet spaces since $G^1$ is second-countable (as $G$ second-countable). By Proposition C.2.3.14, the continuous injective linear map $E_1\,\overline{\otimes}\,F\to E_2\,\overline{\otimes}\,F$ is a linear topological embedding. Thus, we are done. $\square$

REMARK D.3.3.11 (Bornologicity of $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$). Assume $G$ is second-countable. In (D.3.3.6) it was seen that the canonical continuous linear map

$$
\mathcal{S}_I(G)=\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)\to\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)
\tag{D.3.3.8}
$$

is bijective and that the bounded subsets are the same on both sides. Since the bounded sets on both sides of (D.3.3.8) coincide and the source is bornological (as it is the countable strict inductive limit of the spaces $\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(k,G^1)\simeq\mathcal{S}_I(k,G)$ that are Fréchet), the bornological topology associated to $\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ (in the sense of [Scha, p. 63]) is the topology of $\mathcal{S}_I(\mathbf{R}_{>0})\,\overline{\otimes}\,\mathcal{S}(G^1)$.

When $G^1$ has finitely generated dual group, so $G^1\simeq\mathbf{T}^n\times F$ for a finite abelian $F$ and hence $G^1$ is an elementary abelian Lie group, the canonical continuous linear map $\mathcal{S}_I(G)\to\mathcal{S}_I(\mathbf{R}_{>0})\,\widehat{\otimes}_\pi\,\mathcal{S}(G^1)$ is a topological isomorphism by Corollary C.2.3.12.

But if the second-countable $G^1$ does *not* have finitely generated (equivalently not compactly generated) dual group then we claim this continuous linear bijection is *not* an isomorphism. In particular, this provides a class of examples for which formation of projective tensor products does not commute with locally convex inductive limits, even when they are strict and all member spaces of the colimit are nuclear Fréchet and the other tensor factor is nuclear Fréchet (but not finite-dimensional).

Indeed, we can pick a strictly decreasing cofinal sequence $\{k_m\}_{m\ge 1}$ of compact subgroups of $G$ with compactly generated orthogonal in $\widehat{G}$, so then $\mathcal{S}(G^1)$ is a strictly increasing sequence of closed subspaces $\mathcal{S}(k_m,G^1)$ that are compatibly topologically complemented via integration averaging over compact subgroups. Writing $E_{m+1}$) for the resulting topological complement of $\mathcal{S}(k_m,G^1)$ inside $\mathcal{S}(k_{m+1},G^1)$, the locally convex inductive limit $\mathcal{S}(G^1)$ of the $\mathcal{S}(k_m,G^1)$'s is thereby also a locally convex direct sum of $E_1:=\mathcal{S}(k_1,G^1)$ and the $E_{m+1}$)'s. The space $\mathcal{S}_I(\mathbf{R}_{>0})$ is nuclear and infinite-dimensional, so not normable [Tre, Cor. 2 to Prop. 50.2]. Since $E_{m+1}\ne 0$ because $k_m/k_{m+1}\ne 0$, [Gro-b, Ch. I, §1, No. 3, Rem. 1, p. 47] applies to the locally convex space $\oplus E_m=\mathcal{S}(G^1)$ to yield that the linear bijection (D.3.3.8) is not a topological isomorphism.

This is likewise a source of examples for which the subspace topology induced by the injective linear map $\mathcal{S}(G_1)\otimes\mathcal{S}(G_2)\to\mathcal{S}(G_1\times G_2)$ is strictly finer than the projective tensor product topology (compare with Lemma D.1.8.1(1)).

PROPOSITION D.3.3.12 ($G^1$-isotypes of $\mathcal{S}_I(G)$). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $I\subset\mathbf{R}$ be a non-empty interval. The operation $(g.f)(x)=f(g^{-1}x)$ on the space of functions $f:G\to\mathbf{C}$ preserves $\mathcal{S}_I(G)$ and as such defines a continuous action of $G$ on $\mathcal{S}_I(G)$.*

*For any continuous character $\omega\in\widehat{G^1}$, there exists a unique linear map*

$$
\Phi^I_{G,\omega}:\mathcal{S}_I(G)\to\mathrm{H}^0(\omega,\mathcal{S}_I(G))
\tag{D.3.3.9}
$$

## PDF page 812

**812** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

*to the space of $\omega$-isotypic vectors in $\mathcal{S}_I(G)$ making the following diagram of continuous linear maps commute*

(D.3.3.10)

```latex
\begin{tikzcd}
\mathcal{S}_I(G) \arrow[r, "\prod_{a\in I}T_a"]\arrow[d, "\Phi^I_{G,\omega}"'] & \prod_{a\in I}\mathcal{S}(G)\arrow[d, "\prod_{a\in I}\Phi_{G,\omega}"] \\
\mathrm{H}^0(\omega,\mathcal{S}_I(G)) \arrow[r, "\prod_{a\in I}T_a"'] & \prod_{a\in I}\mathrm{H}^0(\omega,\mathcal{S}(G))
\end{tikzcd}
```

*where $\Phi_{G,\omega} : \mathcal{S}(G)\to\mathrm{H}^0(\omega,\mathcal{S}(G))$ is the projector from (D.2.1.1). Moreover $\Phi^I_{G,\omega}$ is a continuous projector (so surjective) and open.*

Terminology D.3.3.1 (Passage to $G^1$-isotypes). We will refer to the linear map $\Phi^I_{G,\omega} : \mathcal{S}_I(G)\to \mathrm{H}^0(\omega,\mathcal{S}_I(G))$ as the passage to the $\omega$-isotype operator.

Proof of Proposition D.3.3.12. Let $\rho_G$ denoted the continuous left-translation action of $G$ on $\mathcal{S}(G)$: $(\rho_G(g))(f) : x\mapsto f(g^{-1}x)$ for $x\in G$. Upon denoting by $\mathcal{S}_a$ the Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}(G)$ equipped with the continuous action $|\cdot|^a_G\cdot\rho_G$, the induced continuous action of $G$ on the product $\prod_{a\in I}\mathcal{S}_a$ preserves the range of the linear injection $\prod_{a\in I}T_a$ that is a topological (even closed) embedding by design of the Hausdorff locally convex topology on $\mathcal{S}_I(G)$ because

$$
|g|^a_G(\rho_G(g))(|x|^a f(x))=|g|^a_G|g^{-1}x|^a_G f(g^{-1}x)=|x|^a_G f(g^{-1}x).
$$

Thus, $(g.f)(x)=f(g^{-1}x)$ preserves $\mathcal{S}_I(G)\subset\prod_{a\in I}\mathcal{S}_a$ and establishes the desired continuity for that $G$-action on $\mathcal{S}_I(G)$.

Since $|\cdot|_G$ is trivial on $G^1$, a direct calculation shows $\Phi_{G,\omega}(|\cdot|^a_G f)=|\cdot|^a_G\Phi_{G,\omega}(f)$, so if $f\in\mathcal{S}_I(G)$ then $\Phi_{G,\omega}(f) : G\to\mathbf{C}$ belongs to $\mathcal{S}_I(G)$ and is certainly $\omega$-isotypic. The injectivity of the horizontal maps in (D.3.3.10) shows that this is the unique $\Phi^I_{G,\omega}$ and that it is a continuous projector. Any continuous projector of a topological space onto a subspace is a quotient mapping (since the inclusion of the subspace is a continuous section), so in the topological group setting it is open. $\square$

D.3.3.2. *Fourier-Melllin transform on $\mathcal{S}_I(G)$.* We conclude this subsection on the structure of $\mathcal{S}_I(G)$ for second-countable $\mathbf{R}_{>0}$-modulated groups $G$ with the following result on the Fourier-Mellin transform in analogy with, and generalizing, Proposition D.3.2.5 that treats the case $G=\mathbf{R}_{>0}$.

Theorem D.3.3.13 (Fourier-Mellin transform on $\mathcal{S}_I(G)$). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $I\subset\mathbf{R}$ be a non-empty open interval, and let $\mu$ be a choice of Haar measure on $G$.*

*For $\phi\in\mathcal{S}_I(G)$, its Fourier-Mellin transform $M(\phi) : c\mapsto \int_G\phi(g)c(g)\,\mathrm{d}\mu(g)$ for $c\in\Omega(G)$ is absolutely convergent on $\Omega(G)_I$ and is holomorphic in $c$, defining a linear map*

$$
M_I : \mathcal{S}_I(G)\to\mathscr{H}(\Omega(G)_I) \tag{D.3.3.11}
$$

*that is $G$-equivariant where we use the left-translation action of $G$ on source and the $G$-action $(g.f)(c)=c(g)f(c)$ on the target.*

*Under the linear topological isomorphism from (D.3.3.3), $M_I$ matches the linear topological isomorphism*

$$
\check{\mathcal{F}}_{G^1}\overline{\otimes} M_I : \mathcal{S}(G^1)\overline{\otimes}\mathcal{S}_I(\mathbf{R}_{>0})\to\mathcal{S}(\widehat{G^1})\overline{\otimes} A\mathcal{S}(\mathbf{C}_I) \tag{D.3.3.12}
$$

*where $\mathcal{F}_{G^1}$ is the Fourier transform on $\mathcal{S}(G^1)$ and $\check{\mathcal{F}}_{G^1}$ is the composition of $\mathcal{F}_{G^1}$ with the inversion automorphism on $G^1$.*

Proof. Pick a continuous section $\tau$ to $|\cdot|_G$ and use it to define a linear topological isomorphism

$$
C^\infty(G^1)\overline{\otimes}\mathcal{S}_I(\mathbf{R}_{>0})=\mathcal{S}(G^1)\overline{\otimes}\mathcal{S}_I(\mathbf{R}_{>0})\simeq\mathcal{S}_I(G)
$$

## PDF page 813

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH I-EXPONENTIAL DECAY** · **813**

from (D.3.3.3). We shall use this to show that $M(\phi)$ is absolutely convergent pointwise on $\Omega(G)_I$ and holomorphic on this open domain inside $\Omega(G)$. Scale the Haar measure on $G=G^1\times\mathbf{R}_{>0}$ to be $\mu_1\times(\mathrm{d}t/t)$ where $\mu_1$ is the volume-$1$ Haar measure on $G^1$.

We may and do pick a compact subgroup $k\subset G^1$ such that $\phi\in\mathcal{S}_I(k,G)$, so $\phi$ arises from

$$
C^\infty(G^1/k)\overline{\otimes}\mathcal{S}_I(\mathbf{R}_{>0})=C^\infty(G^1/k)\widehat{\otimes}_\pi\mathcal{S}_I(\mathbf{R}_{>0})
$$

(topological isomorphism by (D.3.3.5)). By Grothendieck’s description of elements of completed projective tensor products as infinite series [Scha, Ch. III, 6.4], we have

$$
\phi=\sum_{n\ge 1}\lambda_n h_n\otimes f_n
$$

for an absolutely summable sequence $\{\lambda_n\}$ in $\mathbf{C}$ and sequences $\{h_n\}\subset C^\infty(G^1/k)$ and $\{f_n\}\subset\mathcal{S}_I(\mathbf{R}_{>0})$ that converge to $0$ in the respective locally convex topologies (all such infinite series converge in the completed projective tensor product). Pointwise on $G$ we have $\phi(\tau(t)g^1)=\sum_{n\ge 1}\lambda_n h_n(g^1)f_n(t)$, an absolutely convergent sum since $h_n$ and $f_n$ certainly converge to $0$ pointwise. Since $h_n\to 0$ uniformly on $G^1$ (as the sup-norm on $C^\infty(G^1/k)$ is among the seminorms defining the topology), so $|h_n|\le B$ for all $n$ and some $B>0$, for $c\in\Omega(G)_I$ with $\mathrm{Re}(c)=a\in I$ we have

$$
|\phi(\tau(t)g^1)c(\tau(t)g^1)|\le\sum_{n\ge 1}B|\lambda_n||f_n(t)|t^a.
$$

We have arranged $\mu=\mu_1\times \mathrm{d}t/t$ with $\mu_1(G^1)=1$, so for $a\in I$ we have

$$
\sum_{n\ge 1}B|\lambda_n|\int_G|f_n(t)|t^a\,\mathrm{d}\mu(g)=\sum_{n\ge 1}B|\lambda_n|\int_{\mathbf{R}_{>0}}|f_n(t)t^a|\,\mathrm{d}t/t
$$

with $f_n(t)t^a\in\mathcal{S}(\mathbf{R}_{>0})$ a sequence of functions tending to $0$ in $\mathcal{S}(\mathbf{R}_{>0})$ because $f_n\to 0$ in $\mathcal{S}_I(\mathbf{R}_{>0})$ and $a\in I$. Provided the integrals $\int_{\mathbf{R}_{>0}}|f_n(t)t^a|\,\mathrm{d}t/t$ are uniformly bounded, the convergence of $\sum_{n\ge 1}|\lambda_n|$ would then allow us to conclude by the Dominated Convergence Theorem that the integral defining $M(\phi)$ on $\Omega(G)_I$ is pointwise absolutely convergent. Thus, it suffices to show that if $\varphi_n$ is a sequence in $\mathcal{S}(\mathbf{R}_{>0})$ converging to $0$ then $\varphi_n\to 0$ in $L^1(\mathbf{R}_{>0})$. But this is immediate from the fact that the topology on $\mathcal{S}(\mathbf{R}_{>0})$ can be described using $L^1$-convergence in smooth functions and their higher derivatives (see (D.1.10.8) for $\mathbf{R}\simeq\mathbf{R}_{>0}$).

The preceding method of proof of absolute convergence pointwise on $\Omega(G)_I$ also gives the pointwise equality

$$
M(\phi)(c)=\sum_{n\ge 1}\lambda_n\int_G h_n(g^1)f_n(\tau(t))c(\tau(t)g^1)\,\mathrm{d}\mu(\tau(t)g^1) \tag{D.3.3.13}
$$

with uniform control on decay of the tail as $c$ varies in vertical strips $\Omega(G)_J$ for compact intervals $J\subset I$ since (i) the decay $t^a f_n\to 0$ in $\mathcal{S}(\mathbf{R}_{>0})$ for $a\in J$ is uniformly controlled as such $a$ varies (we only need to consider $a$ an endpoint of $J$), (ii) $\sum_{n\ge N}|\lambda_n|\to 0$ as $N\to\infty$. Thus, (D.3.3.13) converges uniformly on $\Omega(G)_J$ for compact $J\subset I$ (so uniformly on compact subsets of $\Omega(G)_I$), reducing the verification of holomorphicity to the special case $\phi=h\otimes f$ for $h\in C^\infty(G^1/k)$ and $f\in\mathcal{S}_I(\mathbf{R}_{>0})$. In such cases, with $c$ varying in the connected component of $\Omega(G)_I$ labelled by some $\omega\in\widehat{G^1}$ (i.e., $c|_{G^1}=\omega$) and using the unitary base point $\chi(\tau(t)g^1)=\omega(g^1)$ (so $c=\chi|\cdot|^s_G$) we have

$$
M(h\otimes f)(c)=\int_{G^1}h\omega\,\mathrm{d}\mu_1\cdot\int_{\mathbf{R}_{>0}}f(t)t^s\,\mathrm{d}t/t=(\mathcal{F}_{G^1}(h))(1/\omega)(M_I(f))(s) \tag{D.3.3.14}
$$

where $M_I : \mathcal{S}_I(\mathbf{R})\simeq A\mathcal{S}(\mathbf{C}_I)\subset\mathscr{H}(\mathbf{C}_I)$ is as in (D.3.2.2) (the Fourier transform $\mathcal{F}_{G^1}(h)$ is evaluated on $1/\omega=\bar\omega$ rather than $\omega$ due to the appearance of complex conjugation in Definition D.1.1.4 for the Fourier transform on locally compact abelian groups).

## PDF page 814

**814** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

With the convergence and holomorphicity aspects of $M(\phi)$ established, if $\phi$ is $k$-invariant for a compact subgroup $k\subset G^1$ (with finitely generated orthogonal in $\widehat{G^1}$) then we claim the restriction of $M(\phi)$ to the connected component $\Omega(G)_{I,\omega}$ over $\omega\in\widehat{G^1}$ vanishes except possibly when $\omega(k)=1$ (i.e., $\omega\in k^\perp$). In other words, under the product decomposition

$$
\mathscr{H}(\Omega(G)_I)=\prod_{\omega\in\widehat{G}}\mathscr{H}(\Omega(G)_{I,\omega})
$$

we claim the holomorphic $M(\phi)$ is supported in the factors labeled by $k^\perp=\widehat{G^1/k}$, which is to say it arises from the subspace $\mathscr{H}(\Omega(G/k)_I)=\prod_{\omega\in\widehat{G^1/k}}\Omega(G/k)_{I,\omega}$ embedded using $0$ along all factors not labeled by $\widehat{G^1/k}$ (note that $\Omega(G/k)_{I,\omega}=\Omega(G)_{I,\omega}$ when $\omega(k)=1$). This is a direct calculation: if $\omega|_k$ is non-trivial then for $c\in\Omega(G)_{I,\omega}$ the assumed $k$-invariance of $\phi$ implies

$$
M(\phi)(c)=\int_G\phi(g)c(g)\,\mathrm{d}\mu(g)=\int_{G/k}\phi(\overline{g})c(g)\left(\int_k c(x)\,\mathrm{d}\mu_k(x)\right)\mathrm{d}\overline{\mu}(\overline{g})
$$

(with $g$ a representative of $\overline{g}\in G/k$), and the inner integral over $k$ is $\int_k\omega\,\mathrm{d}\mu_k=0$ since $\omega|_k$ is non-trivial. Thus, $M_I$ for $G$ is obtained as the direct limit of the corresponding Fourier-Mellin transforms for $G/k$ as $k$ varies through a countable cofinal decreasing sequence $\{k_m\}$ of compact subgroups $k\subset G^1$ with finitely generated orthogonal inside $\widehat{G^1}$. Topologically $\mathcal{S}_I(G)$ is the locally convex inductive limit of the spaces $\mathcal{S}_I(k_m,G)=\mathcal{S}_I(G/k_m)$, so by the good behavior of $\overline{\otimes}$ with respect to countable strict inductive limits (Proposition C.2.3.13(2)) we may and do now focus on each $G/k_m$ in place of $G$; i.e., we consider $G$ that is an elementary abelian Lie group (equivalently, the compact $G^1$ has compactly generated dual group).

The choice of $\tau$ identifies $\Omega(G)_I$ with $\widehat{G^1}\times\mathbf{C}_I$ for $\widehat{G^1}$ discrete, so $\mathscr{H}(\Omega(G)_I)=\prod_{\omega\in\widehat{G^1}}\mathscr{H}(\mathbf{C}_I)$. Equipping the $\omega$-component with the unitary base point $\chi(\tau(t)g^1)=\omega(g^1)$, (D.3.3.14) says that the restriction of the Fourier-Mellon transform to an elementary tensor $h\otimes f\in C^\infty(G^1)\otimes\mathcal{S}_I(\mathbf{R}_{>0})\subset\mathcal{S}_I(G)$ is the tuple

$$
\prod_{\omega\in\widehat{G^1}}(\check{\mathcal{F}}_{G^1}(h))(\omega)M_I(f)\in\prod_{\omega\in\widehat{G^1}}A\mathcal{S}(\mathbf{C}_I).
$$

For any (discrete) set $\Sigma$ and $\mathbf{C}$-vector space $V$, the natural map

$$
\mathrm{Map}(\Sigma,\mathbf{C})\otimes V\to\prod_{\sigma\in\Sigma}V
$$

defined by $h\otimes v\mapsto (h(\sigma)v)$ is injective (via passage to the direct limit from the case of finite-dimensional $V$), so in particular we have

$$
\mathcal{S}(\widehat{G^1})\otimes A\mathcal{S}(\mathbf{C}_I)\hookrightarrow\prod_{\omega\in\widehat{G^1}}A\mathcal{S}(\mathbf{C}_I)
$$

and $\check{\mathcal{F}}_{G^1}(h)\in\mathcal{S}(\widehat{G^1})$.

We have shown that the restriction of $M$ to the subspace $\mathcal{S}(G^1)\otimes\mathcal{S}(\mathbf{R}_{>0})\subset\mathcal{S}_I(G)$ is the composition of the algebraic isomorphism

$$
\check{\mathcal{F}}_{G^1}\otimes M_I : \mathcal{S}(G^1)\otimes\mathcal{S}(\mathbf{R}_{>0})\simeq\mathcal{S}(\widehat{G^1})\otimes A\mathcal{S}(\mathbf{C}_I)
$$

followed by the injection of the latter into $\prod_{\omega\in\widehat{G^1}}A\mathcal{S}(\mathbf{C}_I)\subset\prod_{\omega\in\widehat{G^1}}\mathscr{H}(\mathbf{C}_I)=\mathscr{H}(\Omega(G)_I)$. Since the Fourier transform $\check{\mathcal{F}}_{G^1} : \mathcal{S}(G^1)\to\mathcal{S}(\widehat{G^1})$ is a linear topological isomorphism (Lemma D.1.6.19(2)) and likewise for $M_I : \mathcal{S}_I(\mathbf{R}_{>0})\simeq A\mathcal{S}(\mathbf{C}_I)$ by (D.3.2.2) It follows that $M$ restricts to a linear topological isomorphism

$$
\mathcal{S}(G^1)\otimes\mathcal{S}_I(\mathbf{R}_{>0})\simeq\mathcal{S}(\widehat{G^1})\otimes A\mathcal{S}(\mathbf{C}_I)
$$

## PDF page 815

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH I-EXPONENTIAL DECAY** · **815**

where the two sides are given either the inductive or projective tensor product topologies, both of which coincide due to Corollary C.2.3.12 since the tensor factors are Fréchet (recall $G^1$ is now an elementary abelian Lie group).

We have shown via Grothendieck’s infinite series description of $\mathcal{S}(G^1)\widehat{\otimes}_\pi\mathcal{S}_I(\mathbf{R}_{>0})\simeq\mathcal{S}_I(G)$ that $M$ carries $\sum\lambda_n h_n\otimes f_n$ (for absolutely summable $\{\lambda_n\}$ and null sequences $h_n,f_n$) to the holomorphic function whose restriction to $\Omega(G)_{I,\omega}=\mathbf{C}_I$ is

$$
\sum_{n\ge 1}\lambda_n(\check{\mathcal{F}}_{G^1}(h))(\omega)M_I(f_n).
$$

Thus, it remains to show that for the complete Hausdorff locally convex topological vector space $V=A\mathcal{S}(\mathbf{C}_I)$ and the discrete finitely generated abelian group $\Gamma=\widehat{G^1}$, the unique continuous map

$$
\theta : \mathcal{S}(\Gamma)\widehat{\otimes}_\pi V\to\prod_{\gamma\in\Gamma}V
$$

arising via completeness of the target [Scha, Ch. II, 5.3] and continuity of the evaluation maps $\mathcal{S}(\Gamma)\otimes_\pi V\to V$ at every $\gamma\in\Gamma$ satisfies $\theta(\sum\lambda_n(h_n\otimes v_n))=(\sum\lambda_n h_n(\gamma)v_n)_{\gamma\in\Gamma}$ (the infinite series in $V$ is convergent by completeness and local convexity of the topology) and is injective.

The explicit description of $\theta$ on Grothendieck’s infinite series is immediate from continuity considerations, so the composite map

$$
\mathcal{S}_I(G)\simeq\mathcal{S}(G^1)\widehat{\otimes}_\pi\mathcal{S}_I(\mathbf{R}_{>0})\overset{\check{\mathcal{F}}_{G^1}\widehat{\otimes}M_I}{\simeq}\mathcal{S}(\widehat{G^1})\widehat{\otimes}_\pi A\mathcal{S}(\mathbf{C}_I)\xrightarrow{\theta}\prod_{\omega\in\widehat{G^1}}\mathscr{H}(\mathbf{C}_I)=\mathscr{H}(\Omega(G)_I)
$$

coincides with the Fourier-Mellin transform $M$. Hence, injectivity of $\theta$ is reduced to injectivity of $M$, and that in turn follows from combining injectivity of restriction of holomorphic functions to vertical lines in $\Omega(G)_I$ and injectivity of the Fourier transform on Schwartz functions. $\square$

D.3.4. Uniform Riemann-Lebesgue Lemma on $\mathbf{R}_{>0}$-modulated groups. We include here an analog for second-countable $\mathbf{R}_{>0}$-modulated groups of the Uniform Riemann-Lebesgue Lemma from Proposition B.2.2.3. We refer the reader to §D.1.6 for differential operators on Hausdorff locally compact abelian groups and their interaction with the Fourier transform on Schwartz-Bruhat functions (see Lemma D.1.6.19).

We recall for ease of access that for $G$ an $\mathbf{R}_{>0}$-modulated Hausdorff locally compact abelian group, $\Omega(G)$ denotes the Riemann surface of continuous quasi-characters on $G$, and for any non-empty interval $I\subset\mathbf{R}$ we write $\Omega(G)_I$ for the domain

$$
\Omega(G)_I:=\{c\in\Omega(G) : \sigma(c)\in I\}
$$

where $\sigma : \Omega(G)\to\mathbf{R}$ is the exponent function, associating to a continuous quasi-character $c\in\Omega(G)$ the unique real number $\sigma(c)$ such that $c=\chi|\cdot|^{\sigma(c)+it}_G$ for a, equivalently any, choice $\chi\in\widehat{G}$ of continuous (unitary) character such that $\chi|_{G^1}=c|_{G^1}$, and $t\in\mathbf{R}$ the real number uniquely determined by $\chi$ such that $c=\chi|\cdot|^{\sigma(c)+it}_G$.

Upon changing the choice of $\chi$, the real number $t\in\mathbf{R}$ changes accordingly, but $\sigma(c)$ does not change, and it is therefore uniquely associated to $c$. The function $\sigma : \Omega(G)\to\mathbf{R}$ is continuous and surjective. The next result is a generalization of Proposition B.2.2.3(2), but first we need to record a useful observation:

Remark D.3.4.1. Let $I$ be a non-empty interval. We claim any invariant differential operator $D$ on $C^\infty(G)$ preserves the subspace $\mathcal{S}_I(G)\subset C^\infty(G)$. It suffices to treat the case $D=\partial_b$ for a $1$-parameter subgroup $b : \mathbf{R}\to G$. For $a\in I$ and $\phi\in\mathcal{S}_I(G)$ we want to show that $|\cdot|^a_G D(\phi)\in\mathcal{S}(G)$. By hypothesis $|\cdot|^a_G\phi\in\mathcal{S}(G)$, so $D(|\cdot|^a_G\phi)\in\mathcal{S}(G)$. The product rule for $D=\partial_b$ gives

$$
D(|\cdot|^a_G\phi)=r|\,|^a_G\phi+|\cdot|^a_G D(\phi)
$$

where $|b(t)|_G=e^{rt}$ for some $r\in\mathbf{R}$. Since $r|\cdot|^a_G\phi\in\mathcal{S}(G)$ by the definition of $\mathcal{S}_I(G)$, and we have noted that $D(|\cdot|^a_G\phi)\in\mathcal{S}(G)$, it follows that $|\cdot|^a_G D(\phi)\in\mathcal{S}(G)$ as desired.

## PDF page 816

**816** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

Theorem D.3.4.2 (Uniform Riemann-Lebesgue - II). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated Hausdorff locally compact abelian group, and $I\subset\mathbf{R}$ a non-empty bounded open interval. Let $D$ be an invariant differential operator on $C^\infty(G)$, and define $p_D : \Omega(G)\to\mathbf{C}$ be*

$$
p_D(c):=(Dc)(e) \tag{D.3.4.1}
$$

*for $e\in G$ the neutral element (on $\widehat{G}\subset\Omega(G)$ this recovers the symbol $p(D)$ from Definition D.1.6.10). Fix a Haar measure $\mu$ on $G$ to define the Fourier-Mellin transform $M : \mathcal{S}_{\overline{I}}G)\to\mathcal{S}_I(G)\xrightarrow{M_I}\mathscr{H}(\Omega(G)_I)$ by $M(\phi) : c\mapsto\int_G\phi(g)c(g)\,\mathrm{d}\mu(g)$.*

*For every bounded subset $\mathcal{B}\subset\mathcal{S}_{\overline{I}}(G)$ and a fixed choice of $\omega\in\widehat{G^1}$ there exist constants $C_{\mathcal{B},D,I}>0$ and $M_{\omega,\mathcal{B},D,I}>0$ such that*

$$
|M(\phi)(c)|\le\frac{C_{\mathcal{B},D,I}}{|p_D(c)|} \tag{D.3.4.2}
$$

*for all $\phi\in \mathcal{B}$ and all $c\in\Omega(G)_{I,\omega}$ such that $|p_D(c)|\ge M_{\omega,\mathcal{B},D,I}$.*

Proof. We let $a_1,\dots,a_n : \mathbf{R}\to G$ be $1$-parameter subgroups that give a basis for $\mathcal{L}(G)$ ($n\ge 1$ since $G$ is $\mathbf{R}_{>0}$-modulated), so $D=\sum b_J\partial^J_a$ as a sum over finitely many multi-indices $J=(j_1,\dots,j_n)$ with $b_J\in\mathbf{C}$ and $j_i\in\mathbf{N}$, where $\partial^J_a:=\partial^{j_1}_{a_1}\cdots\partial^{j_n}_{a_n}$. Suppose there are $N$ terms occurring in $D$, so for any $c\in\Omega(G)$ we have

$$
|p_D(c)|\le\sum|b_J||p_{\partial^J_a}(c)|\le N\max_J|b_J||p_{\partial^J_a}(c)|.
$$

Note that $N$ is independent of $c$, but the multi-index $J_c$ for which $|b_J||p_{\partial^J_a}(c)|$ is maximized may depend on $c$. If we can settle the case of the operators $\partial^J_a$, and let $C'_{\mathcal{B},D,I}$ be the maximum of the constants $|b_J|C_{\mathcal{B},\partial^J_a,I}$ and $M_{\omega,\mathcal{B},D,I}$ be the maximum of the constants $N|b_J|M_{\omega,\mathcal{B},\partial^J_a,I}$ then for any $\phi\in \mathcal{B}$ and $c\in\Omega(G)_{I,\omega}$ with $|p_D(c)|\ge M_{\omega,\mathcal{B},D,I}$ we have

$$
|M(\phi)(c)|\le\frac{C'_{\mathcal{B},D,I}}{\max|b_J||p_{\partial^J_a}(c)|}\le\frac{NC'_{\mathcal{B},D,I}}{|p_D(c)|}.
$$

Thus, $C_{\mathcal{B},D,I}:=NC'_{\mathcal{B},D,I}$ and $M_{\omega,\mathcal{B},D,I}$ do the job for $D$.

Now we may and do assume $D=\partial^{r_1}_{a_1}\cdots\partial^{r_n}_{a_n}$ for some exponents $r_i\in\mathbf{N}$. Next we reduce to the case that $G$ is an elementary abelian Lie group. By second-countability, there is a cofinal decreasing sequence $\{k_m\}$ of compact subgroups of $G$ with compactly generated orthogonal such that $\mathcal{S}_{\overline{I}}(G)=\varinjlim\mathcal{S}_{\overline{I}}(k_m,G)$ as a countable strict inductive limit, so $\mathcal{B}\subset\mathcal{S}_{\overline{I}}(k_{m_0},G)$ for some $m_0$ by [Scha, Ch. II, 6.5]. Increasing $m_0$ if necessary allows us to also arrange that $\omega(k_{m_0})=1$. In particular, for $k=k_{m_0}$ we see that every $\phi\in \mathcal{B}$ is $k$-invariant and $\omega\in\widehat{(G/k)}^1$. Clearly also $D(\phi)$ is $k$-invariant since $D$ is an invariant differential operator, and $D(\phi)\in\mathcal{S}_{\overline{I}}(G)$ by Remark D.3.4.1, so $D(\phi)\in\mathcal{S}_{\overline{I}}(k,G)\simeq\mathcal{S}_{\overline{I}}(G/k)$. The quotient $G/k$ is an elementary abelian Lie group and it is $\mathbf{R}_{>0}$-modulated because $k\subset G^1$.

For any $1$-parameter subgroup $b : \mathbf{R}\to G$ with composite $1$-parameter subgroup $\bar b : \mathbf{R}\to G/k$, we have

$$
(\partial_b\phi)(x)=\lim_{t\to 0}\frac{\phi(b(t)x)-\phi(x)}{t}=(\partial_{\bar b}\bar\phi)(x\bmod k)
$$

for $\bar\phi : G/k\to\mathbf{C}$ the corresponding element of $\mathcal{S}_{\overline{I}}(G/k)$ (see Lemma D.1.5.4). Thus, $D(\phi)\in\mathcal{S}_{\overline{I}}(k,G)$ corresponding to $\bar D(\bar\phi)\in\mathcal{S}_{\overline{I}}(G/k)$ where $\bar D:=\partial^{r_1}_{\bar a_1}\cdots\partial^{r_n}_{\bar a_n}$ as an invariant differential operator on $C^\infty(G/k)$. (The $\bar a_i$’s may merely span $\mathcal{L}(G/k)$ rather than be a basis for it, but that doesn’t matter because once we reduce to studying $\overline{D}$ and $\mathcal{B}\subset\mathcal{S}_{\overline{I}}(G/k)$ we can go again through the reduction to a product among the first-order operators associated to a basis of $\mathcal{L}(G/k)$.)

By using Weil’s coset integration formula from Theorem D.1.2.1 exactly as in the passage to elementary abelian Lie groups in the proof of Theorem D.3.3.13, we see from the $k$-invariance of $\phi$ that $M(\phi)(c)=0$

## PDF page 817

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH I-EXPONENTIAL DECAY** · **817**

except possibly when $c\in k^\perp=\widehat{G/k}$, and that if $c\in k^\perp$ then

$$
M(\phi)(c)=M(\bar\phi)(\bar c)
$$

where $\bar c\in\Omega(G/k)$ corresponds to $c$ and the Fourier-Mellin transform on $G/k$ is defined using the Haar measure associated to the initial choice of $\mu$ on $G$ (used to define $M$ for $G$) and the volume-$1$ Haar measure on $k$. Since it is also clear from the definitions that $p_D(c)=p_{\bar D}(\bar c)$, we may rename $G/k$ as $G$ to reduce to the case that $G$ is an elementary abelian Lie group.

Since $G$ is $\mathbf{R}_{>0}$-modulated, any choice $\tau$ of continuous homomorphic section to the module $|\cdot|_G$ induces an isomorphism of Hausdorff locally compact abelian groups $G\simeq\mathbf{R}_{>0}\times G^1$, and hence the compact Hausdorff abelian group $G^1=\ker(|\cdot|_G)$ is an elementary abelian Lie group: $G^1\simeq\mathbf{T}^m\times F$ for an integer $m=n-1\ge 0$ and a finite abelian group $F$ (with $\mathbf{T}=\mathbf{R}/\mathbf{Z}$). We have $F=\pi_0(G)$ and the $1$-parameter subgroups of $G$ are all contained in the identity component, so by treating the restrictions of $\phi$ to each of the finitely many connected components of $G$ separately we may and do assume $G$ is connected: $G=\mathbf{R}_{>0}\times\mathbf{T}^m$.

Now $\mathcal{S}_{\overline{I}}(G)\simeq\mathcal{S}_{\overline{I}}(\mathbf{R}_{>0})\overline{\otimes}\mathcal{S}(\mathbf{T}^m)\simeq\mathcal{S}_{\overline{I}}(\mathbf{R}_{>0})\widehat{\otimes}_\pi\mathcal{S}(\mathbf{T}^m)$ where both tensor factors are Fréchet spaces. Since $\mathcal{S}_{\overline{I}}(G)$ is Montel (Theorem D.3.3.7), the closure of $\mathcal{B}$ (which is also bounded [Scha, Ch. I, 5.1]) is compact. Thus, by [Tre, Cor. 2 to Thm. 45.2] there are compact subsets $K_1\subset\mathcal{S}_{\overline{I}}(\mathbf{R}_{>0})$ and $K_2\subset\mathcal{S}(\mathbf{T}^m)$ such that $\mathcal{B}$ is contained in the closure $\overline{\mathrm{cch}}(K_1\otimes K_2)$ of the convex circled hull of the set of elementary tensors $f_1\otimes f_2$ for $f\in K_1$ and $f_2\in K_2$. If a constant $C_{\mathcal{B},D,I}$ can be found that works for all such elementary tensors then it also works for their circled hull as well as for all convex combinations from the circled hull, and then for the closure thereof. In other words, it suffices to treat the case $\phi=f_1\otimes f_2$. Writing $c=c_1\otimes\omega$ for $c_1\in\Omega(\mathbf{R}_{>0})_I$, we have $M(\phi)(c)=M(f_1)(c_1)M(f_2)(\omega)$ (for a choice of Haar measures on $\mathbf{R}_{>0}$ and $G^1$ whose product measure is the chosen one on $G$).

Writing $D=D_1\overline{\otimes}D_2$ on $\mathcal{S}_{\overline{I}}(G)=\mathcal{S}_{\overline{I}}(\mathbf{R}_{>0})\overline{\otimes}\mathcal{S}(G^1)$ (where $D_1=(t\partial_t)^{r_1}$ for some integer $r_1\ge 0$ and $D_2$ is a product of $r_2\ge 0$ operators — with repetition allowed — among the $\partial_{z_j}$’s for $(z_1,\dots,z_m)$ the standard coordinates on $G^1=\mathbf{T}^m$), clearly

$$
p_D(c)=p_{D_1}(c_1)p_{D_2}(\omega).
$$

Since $p_{D_2}(\omega)$ is a fixed value (as $D$ and $\omega$ are fixed), keeping $|p_D(c)|$ above a positive constant $M$ ensures $|p_{D_1}(c_1)|\ge M/|p_{D_2}(\omega)|$ as we vary such $c=c_1\otimes\omega$. In this way we see it suffices to separately treat the case $G=\mathbf{R}_{>0}$ and an analogous result for the compact $G^1=\mathbf{T}^m$: for any compact subset $K\subset\mathcal{S}(G^1)$ and the differential operator $D=\partial^{r_1}_{z_1}\cdots\partial^{r_m}_{z_m}$ on $G^1=\mathbf{T}^m$, if $p_D(\omega)\ne 0$ then there is a constant $C_K>0$ such that $|M(\phi)(\omega)|\le C_K$ for all $\phi\in K$. Since $\mathcal{S}(\mathbf{T}^m)\simeq\mathcal{S}(\mathbf{T}^{m-1})\widehat{\otimes}_\pi\mathcal{S}(\mathbf{T})$, if $m>1$ then we can go through an analogous argument to pass to the separate cases of $\mathbf{T}^{m-1}$ and $\mathbf{T}$. In other words, it suffices to treat the case $G=\mathbf{R}_{>0}$ and the analogous result as stated above for $G=\mathbf{T}=\mathbf{R}/\mathbf{Z}$. For $G=\mathbf{R}_{>0}$ we may assume $D=(t\partial_t)^r$ for some $r\ge 1$ and for $G=\mathbf{T}$ we may assume $D=\partial^r_z$ for some $r\ge 1$.

For $G=\mathbf{R}_{>0}$ we have $c(t)=t^s$ for $s\in\mathbf{C}_I$, so then $p_{(t\partial_t)^r}(c)=s^r$. Since $|s^r|/|\mathrm{Im}(s)|^r$ is uniformly bounded above on the region when $|\mathrm{Im}(s)|$ stays above a chosen $\delta>0$, requiring $|p_D(c)|\ge(\delta+\max(|a|,|b|))^r$ where $I=(a,b)$ ensures $|\mathrm{Im}(s)|\ge\delta$, Thus, we can use Proposition B.2.2.3(2) provided the constant there (which depends on $\phi$, as seen at the end of its proof) is bounded independently of $\phi$ varying in a compact subset $K\subset\mathcal{S}_{\overline{I}}(\mathbf{R})$. By construction the constant there can be taken to be

$$
\|t^a(t\partial_t)^r(\phi)\|_{L^1(\mathbf{R}_{>0},\mathrm{d}t/t)}+\|t^b(t\partial_t)^r(\phi)\|_{L^1(\mathbf{R}_{>0},\mathrm{dt}/t)}
$$

where $I=(a,b)$. This constant is bounded for $\phi$ varying through a compact subset of $\mathcal{S}_{\overline{I}}(\mathbf{R}_{>0})$ because $\mathcal{S}_{[a,b]}(\mathbf{R}_{>0})\to\mathcal{S}(\mathbf{R}_{>0})\times\mathcal{S}(\mathbf{R}_{>0})$ via $\phi\mapsto(t^a\phi,t^b\phi)$ is a topological embedding and the seminorm $f\mapsto\|(t\partial_t)^r(f)\|_{L^1(\mathbf{R}_{>0},\mathrm{d}t/t)}$ on $\mathcal{S}(\mathbf{R}_{>0})$ is among a collection of seminorms defining the topology on $\mathcal{S}(\mathbf{R}_{>0})$ (see (D.1.10.7) applied to $\mathbf{R}\simeq\mathbf{R}_{>0}$).

## PDF page 818

**818** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

Now consider $G=\mathbf{T}=\mathbf{R}/\mathbf{Z}$ equipped with the volume-$1$ Haar measure. We have $\omega(z)=e^{2\pi imz}$ for some $m\in\mathbf{Z}$, so for $D=\partial^r_z$ we have $p_D(\omega)=(2\pi im)^r$. Thus, we may assume $m\ne 0$ and then integrating by parts $r$ times gives

$$
M(\phi)(z^m)=\int_0^1\phi(x)e^{2\pi imx}\,\mathrm{d}x=-\frac{1}{2\pi im}\int_0^1(\partial_x\phi)(x)e^{2\pi imx}\,\mathrm{d}x=\cdots=\left(\frac{-1}{2\pi im}\right)^r\int_0^1(\partial^r_x\phi)(x)e^{2\pi imx}\,\mathrm{d}x
$$

since $\phi$ is $1$-periodic. We are then done using the constant $C_K=(2\pi|m|)^{-r}\sup_{\phi\in K}\|D\phi\|_{L^1(\mathbf{T})}$ provided this is finite (as $\phi$ varies through a compact subset $K\subset\mathcal{S}(\mathbf{T})$). The seminorm $\phi\mapsto\|D(\phi)\|_{L^1(\mathbf{T})}$ on $\mathcal{S}(\mathbf{T})$ is among a collection of seminorms defining the topology on $\mathcal{S}(\mathbf{T})$ as in (D.1.10.10) (with $p=1$ there), so it is bounded on compact subsets of $L^1(\mathbf{T})$. $\square$

D.3.5. Poisson Summation Formula on $\mathbf{R}_{>0}$-modulated groups: isolated singularities. Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a choice of Haar measure on $G$. The Poisson Summation Formula (see (D.1.2.8)) holds everywhere on $G$ — rather than only $\mu_G$-almost everywhere — in the presence of continuity hypotheses as in Theorem D.1.2.7(3). We now give a class of functions with finitely many isolated singularities and smooth everywhere else for which the Formula holds everywhere over $G$ upon redefining the function at singular points as the arithmetic mean of suitable “one-sided” limit values.

Now let $(G,|\cdot|_G)$ be an $\mathbf{R}_{>0}$-modulated group equipped with the canonical Haar measure $\mu_G$ that is the unique one such that, upon denoting by $\mu_1$ the volume-$1$ Haar measure on $G^1$, the unique Haar measure obtained on $G/G^1\simeq\mathbf{R}_{>0}$ (the isomorphism being the module $|\cdot|_G$) as per Theorem D.1.2.1 is $\mathrm{d}t/t$ on $\mathbf{R}_{>0}$.

Proposition D.3.5.1 (Poisson Summation Formula - jump singularities on $\mathbf{R}_{>0}$-modulated groups). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group with module $|\cdot|_G$. Let $\mu_G$ be the canonical Haar measure on $G$. Let $\gamma\in G$ be an element satisfying $|\gamma|_G>1$. Let $\chi_0\in\widehat{G}$ be a continuous (unitary) character, and let $\tau : \mathbf{R}_{>0}\to G$ be a choice of continuous homomorphic section to the module $|\cdot|_G$.*

Let $\phi : G\to\mathbf{C}$ be a function. Assume:

(1) *$\phi$ is bounded, and for every integer $N\ge 1$, there exist real numbers $T>0$ and $C_N>0$, such that*

$$
|\phi(g)|\le C_N e^{-N|\log|g|_G|} \tag{D.3.5.1}
$$

for all $g\in G$ with $|\log|g|_G|>T$,

(2) *for every $g\in G^1$, the continuous function $\phi(\tau(t)g)$ of $t\in\mathbf{R}_{>0}$ is smooth away from finitely many points $\{t_1,\dots,t_m\}\subset\mathbf{R}_{>0}$ and admits one-sided limits at each of them for each $g\in G^1$, and the derivatives $(t\partial_t)^k\phi(\tau(t)g)$ are continuous functions of*

$$
(t,g)\in(\mathbf{R}_{>0}-\{t_1,\dots,t_m\})\times G^1
$$

for each integer $k\ge 0$,

(3) *$\phi$ is $\chi_0|_{G^1}$-homogeneous with respect to the left-translation action by $G^1$.*

*Then upon redefining $\phi$ on the finitely many fibres of $|\cdot|_G$ over $\{t_1,\dots,t_m\}$ to be*

$$
\phi(\tau(t_k)g):=\frac{\lim_{t\to t_k^+}\phi(\tau(t)g)+\lim_{t\to t_k^-}\phi(\tau(t)g)}{2} \tag{D.3.5.2}
$$

*for $1\le k\le m$ and for all $g\in G^1$, the following identity holds for all $x\in G$:*

$$
\sum_{n\in\mathbf{Z}}\chi_0(\gamma^n x)\phi(\gamma^n x)=\frac{1}{\log|\gamma|_G}\sum_{m\in\mathbf{Z}}\widehat{\phi}\left(\overline{\chi}_0|\cdot|^{-\frac{2\pi im}{\log|\gamma|_G}+it_0}_G\right)|x|^{\frac{2\pi im}{\log|\gamma|_G}}_G \tag{D.3.5.3}
$$

where $t_0\in[0,2\pi/\log|\gamma|_G)$ satisfies $\chi_0(\gamma)=|\gamma|^{it_0}_G$.

Remark D.3.5.2. We recall that for $G$ an $\mathbf{R}_{>0}$-modulated group and $\gamma\in G$ such that $|\gamma|_G>1$, upon choosing a holomorphic parametrization $\{\chi|\cdot|^s_G\}$ for the Riemann surface $\Omega(G)$ of continuous quasi-characters,

## PDF page 819

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH I-EXPONENTIAL DECAY** · **819**

with $s\in\mathbf{C}$ and $\chi$ varying over a choice $\widetilde{G^1}$ of continuous (unitary) characters each lifting each point of the discrete set $\widehat{G^1}$, the continuous characters of $G$ that are trivial on the discrete closed subgroup $\gamma^{\mathbf{Z}}$ are all parametrized as

$$
\chi|\cdot|^{\frac{2\pi im}{\log|\gamma|_G}-it(\chi)}_G
$$

as $\chi$ varies over $\widetilde{G^1}$ and $m\in\mathbf{Z}$, with $t(\chi)$ the unique real number contained in $[0,2\pi/\log|\gamma|_G)$ satisfying:

$$
e^{it(\chi)\log|\gamma|_G}=\chi(\gamma). \tag{D.3.5.4}
$$

In particular, $\chi':=\chi|\cdot|^{-it(\chi)}_G$ satisfies $\chi'(\gamma)=1$, and hence $\chi'$ is trivial on $\gamma^{\mathbf{Z}}$.

Proof of Proposition D.3.5.1. We observe that for each $x\in G$, writing $x=\tau(t)g$ for unique $(t,g)\in\mathbf{R}_{>0}\times G^1$, both sides of (D.3.5.3) are independent of $g\in G^1$ (this uses hypothesis (3) for independence of $g$ on the left side of (D.3.5.3)).

We define $\psi(x):=\chi_0(x)\phi(x)$, for $x\in G$; this is invariant under left-translation by $G^1$, so for $x\in G$ the value $\psi(x)$ only depends on $|x|_G$. Note that $\psi$ also satisfies (D.3.5.1) since $\chi_0$ is unitary. We have

$$
\widehat{\psi}(\chi)=\int_G\psi(y)\overline{\chi}(y)\,\mathrm{d}\mu_G(y)=\int_{\mathbf{R}_{>0}}\psi(\tau(t))\overline{\chi}(\tau(t))\,\frac{\mathrm{d}t}{t}=\int_{G^1}\overline{\chi}(g)\,\mathrm{d}\mu_1(g) \tag{D.3.5.5}
$$

and the rightmost side of (D.3.5.5) is nonzero only if $\overline{\chi}|_{G^1}=1$. The identity in (D.3.5.3) therefore follows from Proposition B.4.1.2 applied to $\psi\circ\tau$ and (in the notation of the Proposition) $\chi=1$, $\theta=|\gamma|_G$ upon rewriting the hypotheses on $\phi$ in terms of $\psi$. $\square$

D.3.6. Approximation by smooth compactly supported functions. The following approximation result will be useful for us:

Lemma D.3.6.1 (Approximation by smooth compactly supported functions). *Let $(G,|\cdot|_G)$ be a second-countable locally compact Hausdorff $\mathbf{R}_{>0}$-modulated abelian group. Let $I\subset\mathbf{R}$ be a non-empty interval. Then $\mathcal{D}(G):=C^\infty_c(G)$ is a dense subspace of $\mathcal{S}_I(G)$ with continuous inclusion.*

We equip $\mathcal{D}(G)$ with the usual countable strict inductive limit topology (via any choice of countable exhaustion of $G$ by compact subsets).

Proof. Each $\phi\in\mathcal{D}(G)$ certainly satisfies $|\cdot|^a_G\phi\in\mathcal{S}(G)$ for every $a\in\mathbf{R}$, so $\mathcal{D}(G)\subset\mathcal{S}_I(G)$.

For every $a\in\mathbf{R}$, multiplication by the smooth function $|\cdot|^a_G$ is continuous and continuously invertible on $\mathcal{D}(G)$. Thus, the composition of $T_a : \mathcal{S}_I(G)\to\mathcal{S}(G)$ with the injective linear inclusion $\mathcal{D}(G)\subset\mathcal{S}_I(G)$ is continuous for every $a\in\mathbf{R}$. By design of the projective topology on $\mathcal{S}_I(G)$, the inclusion

$$
j_G : \mathcal{D}(G)\to\mathcal{S}_I(G)
$$

is therefore continuous.

Upon choosing a continuous homomorphic section $\tau$ to $|\cdot|_G$, by Theorem D.3.3.7(1) (which uses second-countability of $G$) we have a linear topological isomorphism $\mathcal{S}_I(G)\simeq\mathcal{S}(G^1)\overline{\otimes}\mathcal{S}_I(\mathbf{R}_{>0})=\mathcal{D}(G^1)\overline{\otimes}\mathcal{S}_I(\mathbf{R}_{>0})$ (the final equality using that $G^1$ is compact). We similarly have a linear topological isomorphism $\mathcal{D}(G)\simeq\mathcal{D}(G^1)\overline{\otimes}\mathcal{D}(\mathbf{R}_{>0})$ by [Bru, §5, Thm.3(a), p. 55]. The continuous inclusion $\mathcal{D}(G)\to\mathcal{S}_I(G)$ is thereby identified with the natural continuous map

$$
\mathrm{id}_{\mathcal{D}(G^1)}\overline{\otimes} j_{\mathbf{R}_{>0}} : \mathcal{D}(G^1)\overline{\otimes}\mathcal{D}(\mathbf{R}_{>0})\to\mathcal{D}(G^1)\overline{\otimes}\mathcal{S}_I(\mathbf{R}_{>0}) \tag{D.3.6.1}
$$

since by continuity is suffices to check on the dense subspace $\mathcal{D}(G^1)\otimes\mathcal{D}(\mathbf{R}_{>0})$ (and so by linearity it suffices to check on elementary tensors).

To prove (D.3.6.1) has dense image, we claim it suffices to treat the case $G=\mathbf{R}_{>0}$. In other words, if the map between second tensor factors in (D.3.6.1) has dense image then we claim the map (D.3.6.1) has dense image. By the Hahn-Banach Theorem, it suffices to show that the induced map between continuous linear

## PDF page 820

**820** · **CHAPTER D. SCHWARTZ-BRUHAT FUNCTIONS**

duals is injective. The continuous dual is insensitive to passage to completion, so it is the same as showing that the natural map

$$
\mathrm{id}_{\mathcal{D}(G^1)}\otimes j_{\mathbf{R}_{>0}} : \mathcal{D}(G^1)\otimes_\iota\mathcal{D}(\mathbf{R}_{>0})\to\mathcal{D}(G^1)\otimes_\iota\mathcal{S}_I(\mathbf{R}_{>0})
$$

induces an injection between continuous linear duals.

The continuous linear dual of an inductive tensor product $E\otimes_\iota F$ (for Hausdorff locally convex $E$ and $F$) is the space of “separately continuous” bilinear forms $B : E\times F\to\mathbf{C}$ (i.e., $B(x,\cdot) : F\to\mathbf{C}$ and $B(\cdot,y) : E\to\mathbf{C}$ are continuous for all $x\in E$ and $y\in F$). In other words, if $B : \mathcal{D}(G^1)\times\mathcal{S}_I(\mathbf{R}_{>0})\to\mathbf{C}$ is a separately continuous bilinear map that vanishes on $\mathcal{D}(G^1)\times\mathcal{D}(\mathbf{R}_{>0})$ then we want to show $B=0$ if $\mathcal{D}(\mathbf{R}_{>0})$ is dense in $\mathcal{S}_I(\mathbf{R}_{>0})$. But such vanishing for $B$ is immediate from such density due to continuity of $B$ in the second variable for each fixed entry in the first variable.

We are reduced to the case $G=\mathbf{R}_{>0}$: proving $\mathcal{D}(\mathbf{R}_{>0})$ is dense in $\mathcal{S}_I(\mathbf{R}_{>0})$. By the definition of the topology, density can be checked by working with each $\mathcal{S}_J(\mathbf{R}_{>0})$ for each $J$ in an increasing sequence of compact intervals exhausting $I$. Thus, we can assume $I$ is compact and hence bounded. Since multiplication by $|\cdot|^a_{\mathbf{R}}$ for any real number $a\in\mathbf{R}$ is continuous and continuously invertible on $\mathcal{D}(\mathbf{R}_{>0})$, we can use such multiplication to move the bounded $I$ arbitrarily far to the right. Thus, we may and do assume $I\subset(0,+\infty)$.

Using $\exp : \mathbf{R}\simeq\mathbf{R}_{>0}$, the Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{D}(\mathbf{R}_{>0})$ is linearly and topologically isomorphic to $\mathcal{D}(\mathbf{R})$ endowed with its locally convex inductive limit topology, and similarly $\mathcal{S}_I(\mathbf{R}_{>0})$ is linearly and topologically isomorphic to the Hausdorff locally convex topological vector space $\mathcal{S}_I(\mathbf{R})$.

A family of continuous seminorms generating the Hausdorff locally convex topology on $\mathcal{S}_I(\mathbf{R})$ is

$$
\nu_{a,k}(\phi):=\sup_{x\in\mathbf{R}}|e^{ax}\partial^k_x\phi(x)|
$$

for $(a,k)\in I\times\mathbf{N}$ with $I\subset(0,\infty)$. Pick $\psi\in\mathcal{D}(\mathbf{R})$ with support contained in $[-2,2]$, and $\psi(\mathbf{R})\subset\mathbf{R}_{\ge 0}$ with $\psi([-1,1])=\{1\}$. Choose $\varphi\in\mathcal{S}_I(\mathbf{R})$.

For every integer $m\ge 1$, we define $\psi_m(x):=\psi(x/m)$ and define $\phi_m:=\psi_m\cdot\phi$, an element of $\mathcal{D}(\mathbf{R})$. We now show that $\lim_{m\to+\infty}\phi_m=\phi$ in $\mathcal{S}_I(\mathbf{R})$, so $\mathcal{D}(\mathbf{R})$ would then be dense in the metric space $\mathcal{S}_I(\mathbf{R})$. For all $x\in\mathbf{R}$, every integer $m\ge 1$, and every pair $(a,k)\in I\times\mathbf{N}$,

$$
\partial^k\phi_m(x)=\sum_{0\le r\le k}\left(\frac{1}{m}\right)^{k-r}\binom{k}{r}\partial^r_x\phi(x)\partial^{k-r}_x\psi(x/m) \tag{D.3.6.2}
$$

$$
=\sum_{0\le r\le k,r\ne k}\left(\frac{1}{m}\right)^{k-r}\binom{k}{r}\partial^r_x\phi(x)\partial^{k-r}_x\psi(x/m)+\partial^k_x\phi(x).
$$

We deduce that for every integer $m\ge 1$ and every pair $(a,k)\in I\times\mathbf{N}$,

$$
|e^{ax}\partial^k\phi_m(x)-e^{ax}\partial^k_x\phi(x)|\le\left|e^{ax}\sum_{0\le r\le k,r\ne k}\left(\frac{1}{m}\right)^{k-r}\binom{k}{r}\partial^r_x\phi(x)\partial^{k-r}_x\psi(x/m)\right| \tag{D.3.6.3}
$$

$$
\le\sum_{0\le r\le k,r\ne k}\left(\frac{1}{m}\right)^{k-r}\binom{k}{r}|e^{ax}\partial^r_x\phi(x)\partial^{k-r}_x\psi(x/m)|.
$$

Now observe that for every integer $m\ge 1$ and every pair $(a,k)\in I\times\mathbf{N}$,

$$
\sup_{x\in\mathbf{R}}|e^{ax}\partial^k\phi_m(x)-e^{ax}\partial^k_x\phi(x)|\le\sum_{0\le r\le k,r\ne k}\binom{k}{r}\sup_{x\in\mathbf{R}}\frac{|\partial^{k-r}\psi(x/m)|}{m^{k-r}}\nu_{a,r}(\phi)\le\frac{C_k}{m}\sum_{0\le r\le k,r\ne k}\binom{k}{r}\nu_{a,r}(\phi) \tag{D.3.6.4}
$$

## PDF page 821

**D.3. SCHWARTZ-BRUHAT FUNCTIONS WITH I-EXPONENTIAL DECAY** · **821**

where $C_k:=\max_{1\le k\le r,r\ne k}\sup_{x\in\mathbf{R}}|\partial^{k-r}\psi|$ and the right side in (D.3.6.4) tends to zero as $m\to+\infty$, proving that $\phi_m\to\phi$ in $\mathcal{S}_I(\mathbf{R})$. $\square$

## PDF page 822
