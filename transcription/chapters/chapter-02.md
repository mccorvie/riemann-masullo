## PDF page 57

CHAPTER 2

**Adelic $\theta$-functions**

We fix a number field $F$, writing $\mathcal O_F$ for its ring of integers.

In [CF, Ch.XV,§4,Def.4.4.1], idelic zeta integrals, i.e. integrals over $\mathrm{GL}_1(\mathbf A_F)$ of the form

$$
\int_{\mathrm{GL}_1(\mathbf A_F)} f(g)c(g)\,\mathrm d\mu(g)
$$

for $f$ a suitable measurable function on the Hausdorff locally compact abelian topological group $\mathrm{GL}_1(\mathbf A_F)$, $\mu$ a fixed choice of Haar measure on $\mathrm{GL}_1(\mathbf A_F)$, and as $c$ varies over a suitable subset of all continuous quasi-characters of $\mathrm{GL}_1(\mathbf A_F)$ satisfying $c(F^\times)=1$, are defined and shown to be well behaved for test functions $f$ from the complex vector space $\mathfrak z$ introduced in [CF, Ch.XV,§4.4, $\mathfrak z_1$-$\mathfrak z_3$].

The set of continuous quasi-characters of $\mathrm{GL}_1(\mathbf A_F)$ satisfying $c(F^\times)=1$ is equipped with the structure of a Riemann surface $\Omega$. Such functions are designed to ensure convergence of the integrals from [CF, Ch.XV,Def.4.4.1] over $\mathrm{GL}_1(\mathbf A_F)$ over large domains within $\Omega$, and the validity of the adelic “Riemann-Roch Theorem” from [CF, Ch.XV,Thm.4.2.1].

In this Chapter we study properties of the Hausdorff locally convex topological complex vector space $\mathcal S(\mathbf A_F)$ of Schwartz-Bruhat functions on the adele ring $\mathbf A_F$.

A consequence of the results recorded here is the well known fact that Schwartz-Bruhat functions on $\mathbf A_F$ are examples of functions from $\mathfrak z$.

The topological properties of $\mathcal S(\mathbf A_F)$ and its strong dual $\mathcal S(\mathbf A_F)'_\beta$ will enable us to study the continuous representation of $\mathrm{GL}_1(\mathbf A_F)$ on $\mathcal S(\mathbf A_F)$ and its homological and co-homological invariants, leading to precise information on Hecke $L$-functions and their divisor of zeros and poles.

The main goals of this Chapter are as follows:

(1) Analyze the decay properties of functions on the idele class group $C_F$ of $F$ constructed by averaging under the continuous left-translation action by $F^\times$, Schwartz-Bruhat functions on $\mathbf A_F$ (restricted to $\mathrm{GL}_1(\mathbf A_F)$ under composition with the continuous map $\mathrm{GL}_1(\mathbf A_F)\to\mathbf A_F$).

(2) Discussing $S$-local analogs of the constructions and results from (1), for $S$ a finite set of places of $F$ containing all the Archimedean places.

(3) Revisiting [CF, Ch.XV,§4.4] of Tate’s dissertation, with the specific purpose of rewriting Tate’s idelic zeta integrals as Mellin transforms of smooth functions on $\mathbf R_{>0}$ with rapid decay at infinity, such functions being linearly associated to the Schwartz-Bruhat functions on $\mathbf A_F$, respectively $\mathbf A_{F,S}$.

(4) Studying continuity properties of the formation of the functions constructed in (2), together with the interaction with directional derivation along continuous $1$-parameter subgroups of $\mathrm{GL}_1(\mathbf A_F)$, respectively $\mathrm{GL}_1(\mathbf A_{F,S})$.

57

## PDF page 58

58  CHAPTER 2. ADELIC $\theta$-FUNCTIONS

| | |
|---|---:|
| 2.1. Schwartz-Bruhat functions | 59 |
| 2.1.1. Schwartz-Bruhat functions | 59 |
| 2.1.1.1. Schwartz functions on the real line. | 59 |
| 2.1.1.2. Schwartz functions on Euclidean spaces. | 60 |
| 2.1.1.3. Schwartz-Bruhat functions on Hausdorff locally compact abelian groups. | 62 |
| 2.1.2. Local Schwartz-Bruhat functions | 63 |
| 2.1.2.1. Smooth functions on non-Archimedean fields. | 63 |
| 2.1.2.2. The locally convex topological complex vector spaces $\mathcal S(F_v)$ for $v\in\Sigma_{F,f}$. | 63 |
| 2.1.2.3. Uniform sequential continuity of the continuous left $F_v^\times$-module $\mathcal S(F_v)$ | 65 |
| 2.1.3. Adelic Schwartz-Bruhat functions | 67 |
| 2.1.3.1. Kernel Theorem for the Adelic Schwartz-Bruhat spacee | 67 |
| 2.1.4. Inductive structure of $\mathcal S(\mathbf A_F)$. | 70 |
| 2.2. Global adelic $\theta$-functions | 74 |
| 2.2.1. Averaging over a full lattice | 75 |
| 2.2.2. Averaging over $\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$ under $(F^\times\times F)$-translation. | 77 |
| 2.2.2.1. The main convergence Lemma. | 77 |
| 2.2.3. The $\theta$-function operator $\Phi_F:\mathcal S(\mathbf A_F)\to C(C_F)$ | 81 |
| 2.2.3.1. Estimates over the idele class group. | 82 |
| 2.2.4. Compatibility with directional derivatives: global adelic $\theta$-functions | 86 |
| 2.2.4.1. Directional derivatives and the global polar hyperplanes | 91 |
| 2.2.5. The homogeneous $\theta$-function operators $\Phi_{F,\omega}:\mathcal S(\mathbf A_F)\to C(C_F/C_F^1)$ | 95 |
| 2.2.5.1. Properties of the homogeneous $\theta$-function operator | 95 |
| 2.2.5.2. Decay estimates over $C_F/C_F^1$. | 97 |
| 2.3. $S$-local adelic $\theta$-functions | 98 |
| 2.3.1. $S$-local $\theta$-function operators | 99 |
| 2.3.1.1. Estimates over $J_{F,S}$ | 100 |
| 2.3.1.2. Homogeneous $S$-adelic $\theta$-functions | 104 |
| 2.3.1.3. Estimates over $J_{F,S}/J_{F,S}^1$ | 105 |
| 2.3.2. Compatibility with directional derivatives | 105 |
| 2.4. Asymptotic behavior as $\lvert g\rvert_{F,S}\to 0^+$ by lattice point-counting | 106 |
| 2.4.1. Warm-up: the case of the rational number field | 106 |
| 2.4.2. The general case | 110 |
| 2.4.3. Order of growth as $\lvert g\rvert_{F,S}\to 0^+$ | 112 |

## PDF page 59

2.1. SCHWARTZ-BRUHAT FUNCTIONS    59

**2.1. Schwartz-Bruhat functions**

Distribution theory rests upon the construction of Hausdorff locally convex topological vector spaces of test functions, usually satisfying favorable topological properties, such as completeness, nuclearity, barrelledness and the Heine-Borel property (these latter two properties defining the class of Montel Hausdorff locally convex topological vector spaces; see [Jar, Part II,Ch.11,§11.5]).

Distributions are ordinarily defined as the strong dual of a Hausdorff locally convex topological complex vector space of suitable test functions. Such spaces of distributions often receive a linear topological embedding from the space of test functions itself, enabling us to think of distributions as generalized functions.

For the concept of *strong dual* we refer the reader to Definition C.2.1.5(3): for a Hausdorff locally convex topological $\mathbf C$-vector space $E$, its strong dual is the continuous dual endowed with the topology of uniform convergence on bounded subsets, and denoted as $E'_\beta$.

In this section we recall the notion of tempered distribution on the real line, briefly reviewing its generalization to tempered distributions on Hausdorff locally compact abelian groups, specializing to the case of the Hausdorff locally compact abelian group $\mathbf A_F$ of the adeles of a number field.

The general theory of Schwartz-Bruhat functions on Hausdorff locally compact abelian groups $G$ is reworked in Appendix D, with the aim at providing proofs of the main structural results on $\mathcal S(G)$, relying on Appendix C, where we discuss complements and background material from functional analysis.

For the purposes of this Chapter, we will be recalling basic facts on Schwartz-Bruhat functions as the need arises, and in the specific cases of interest only.

**2.1.1. Schwartz-Bruhat functions.** We begin by reviewing the example of the space of Schwartz functions on the real line.

2.1.1.1. *Schwartz functions on the real line.* Let $f_1,f_2$ be smooth complex valued functions on the real line. Deciding how “near” $f_1$ and $f_2$ are is a task to be addressed depending on the behavior of $f_1(x),f_2(x)$ as $|x|\to+\infty$, since $\mathbf R$ is not compact.

The uniform norm provides one notion of nearness among smooth complex valued functions on $\mathbf R$, so long as the functions are bounded over $\mathbf R$. The resulting topology on the $\mathbf C$-vector space of bounded smooth complex valued functions is too coarse to allow a rich strong dual. Even on smooth functions with compact support, the resulting linear topology is uninteresting.

**EXAMPLE 2.1.1.1.** The space of distributions on the real line is built as the strong dual (see [Sch-a, Ch.III,§3,p.71]) of the Hausdorff locally convex topological complex vector space of smooth compactly supported functions $C^\infty_c(\mathbf R)$, endowed with the locally convex (strict) inductive limit topology (see [Scha, Ch.II,§6,p.57] and [Jar, Part I,Ch.4,§4.6], [Sch-a, Ch.III,§1,Thm.II]) promoting the linear inclusions $C^\infty_K(\mathbf R)\subset C^\infty_c(\mathbf R)$ to continuous linear operators (in fact, linear topological embeddings).

Here $C^\infty_K(\mathbf R)$ denotes the complex vector space of smooth functions on $\mathbf R$ with support contained within the compact subset $K\subset\mathbf R$ (see [Sch-a, p.24]), endowed with the topology of uniform convergence of functions and their derivatives of any order. We refer the reader to [Sch-a, Ch.III,§1].

Before continuing, we caution the reader on the difference between inductive limit topologies and locally convex inductive limit topologies.

**REMARK 2.1.1.2** (Cautionary remark on the difference of inductive limit and locally convex inductive limit topology). The locally convex inductive limit topology on $C^\infty_c(\mathbf R)$ differs from the inductive limit topology, which is generally not locally convex. A counterexample can be constructed from [Shi, Lemme 4] and its proof.

## PDF page 60

60  CHAPTER 2. ADELIC $\theta$-FUNCTIONS

The inductive limit topology of a sequence of topological spaces equipped with continuous transition maps (satisfying good properties, such as being topological embeddings with closed image) may be unwieldy. It is difficult to write down examples of open neighborhoods.

For locally convex inductive limits of filtered families of Hausdorff locally convex topological $\mathbf C$-vector spaces, instead, we can write down a $0$-neighborhood base as follows. Let $I$ be a filtered set (i.e. equipped with a partial ordering) and $\{E_i\}_{i\in I}$ an $I$-indexed collection of Hausdorff locally convex topological $\mathbf C$-vector spaces.

Assume given injective transition maps $u_{ij}:E_i\to E_j$ for every $j\ge i$ in $I$, and let $E$ be the filtered colimit linear space. We call $u_i:E_i\to E$ the induced linear inclusion. A $0$-neighborhood base for the locally convex inductive limit topology on $E$ is given by the convex hulls

$$
\operatorname{ch}(\bigcup_{i\in I}u_i(V_i))
$$

for $V_i$ varying through a given fundamental system of $0$-neighborhoods in $E_i$. We refer the reader to [Gro-f, Ch.4,§1,Prop.1(2),p.136].

Locally convex inductive limits have a tendency to be large and do not satisfy the second-countability condition (in particular, they are usually non-metrizable).

For example the $\mathbf N$-indexed direct sum $\bigoplus_{\mathbf N}\mathbf C$ is non-metrizable because it does not have a countable $0$-neighborhood base.

The space of *tempered distributions* on the real line is, instead, built as the strong dual of the Hausdorff locally convex topological complex vector space of Schwartz functions on $\mathbf R$.

**EXAMPLE 2.1.1.3.** The complex vector space $\mathcal S(\mathbf R)$ of Schwartz functions on $\mathbf R$ is comprised of the smooth functions $f\in C^\infty(\mathbf R)$ such that

$$
\|f\|_{m,N}:=\sup_{x\in\mathbf R}(1+|x|^N)|\partial^m_x f(x)|<+\infty
$$

where $\partial^m_x f$ is the order-$m$ derivative of $f$, for all integers $N,m\ge 0$, topologized with the locally convex topology generated by the family $\{\|\cdot\|_{m,N}\}_{m,N\ge 0}$ of seminorms.

The space of *tempered distributions* on $\mathbf R$ is defined to be the Hausdorff locally convex topological vector space $\mathcal S(\mathbf R)'_\beta$: the strong dual of $\mathcal S(\mathbf R)$. This is the continuous dual of $\mathcal S(\mathbf R)$ endowed with the topology of uniform convergence (for continuous linear functionals) on the bounded subsets of $\mathcal S(\mathbf R)$.

2.1.1.2. *Schwartz functions on Euclidean spaces.* Schwartz functions can be similarly defined for Euclidean spaces, which we now briefly recall. We fix an integer $m\ge 0$ and consider the real Euclidean space $\mathbf R^m$. We parametrize $\mathbf R^m$ with its standard coordinates $x=(x_i)_{1\le i\le m}$.

We define, for every $\alpha\in\mathbf N^m$, the $\mathbf C$-linear operator

(2.1.1.1)

$$
D^\alpha_x:=\frac{\partial^{|\alpha|}}{\partial x_1^{\alpha_1}\cdots\partial x_m^{\alpha_m}}:C^\infty(\mathbf R^m)\to C^\infty(\mathbf R^m)
$$

with $|\alpha|:=\sum_{i=1}^m\alpha_i$. We write, for any $x\in\mathbf R^m$ and $\alpha\in\mathbf N^m$

(2.1.1.2)

$$
x^\alpha:=\prod_{i=1}^m x_i^{\alpha_i}.
$$

**DEFINITION 2.1.1.4.** Let $f:\mathbf R^m\to\mathbf C$ be a smooth function. We say $f$ is of *rapid decay at infinity* if and only if for every $\alpha,\beta\in\mathbf N^m$, the function

(2.1.1.3)

$$
\|\cdot\|_{\alpha,\beta}:C^\infty(\mathbf R^m)\to[0,+\infty]
$$

## PDF page 61

2.1. SCHWARTZ-BRUHAT FUNCTIONS    61

defined as

(2.1.1.4)

$$
\|f\|_{\alpha,\beta}:\sup_{x\in\mathbf R^m}(1+|x^\alpha|)|D^\beta_x f(x)|
$$

is finite on $f$.

We denote by $\mathcal S(\mathbf R^m)$ the $\mathbf C$-vector space of all smooth functions on $\mathbf R^m$ of rapid decay at infinity. We topologize $\mathcal S(\mathbf R^m)$ with the locally convex topology generated by the family $\{\|\cdot\|_{\alpha,\beta\in\mathbf N^m}\}$ of seminorms. We refer to the locally convex topological $\mathbf C$-vector space $\mathcal S(\mathbf R^m)$ as the *Schwartz space* of $\mathbf R^m$.

**REMARK 2.1.1.5.** There are several families of explicit seminorms on $\mathcal S(\mathbf R^m)$ generating the same locally convex topology. For instance, $p_{\alpha,\beta}:\mathcal S(\mathbf R^m)\to\mathbf R_{\ge 0}$, for each $\alpha,\beta\in\mathbf N^m$, given by $p_{\alpha,\beta}(f):=\sup_{x\in\mathbf R^m}|x^\alpha D^\beta_x f(x)|$. Another important such family is

$$
p_{\alpha,\beta,r}:=\|x^\alpha D^\beta_x f(x)\|_{L^r(\mathbf R^m,\mathrm{d}x)}
$$

for $r\ge 1$ a fixed choice of real number. Other such families generating an equivalent topology on $\mathcal S(\mathbf R^m)$ are given by the same assignments, upon replacing $x^\alpha$ with $u(x)$ as $u$ varies over all polynomial functions on $\mathbf R^m$ with complex coefficients. We refer the reader to [KG, Part I,Ch.III,(3)].

We shall next record a result on properties of the linear topology on $\mathcal S(\mathbf R^m)$, but first we must clarify the role of boundedness in the definition of strong duals. The $\beta$-topology, or *strong* topology, on the continuous dual $E'$ of a Hausdorff locally convex topological complex vector space $E$ is defined in [Jar, Part II,Ch.8,§8.4,Example 3.A,p.153] as the topology of uniform convergence on all subsets of $E$ that are $\sigma(E,E')$-bounded, i.e. bounded for the weakened topology on $E$. However, the subsets of $E$ that are bounded with respect to the weakened topology are exactly the subsets of $E$ that are bounded for the intrinsic topology on $E$ by [Jar, Part II,Ch.8,§8.3,Thm.4,p.151] (see also [NB, Thm.8.8.7]). Definition C.2.1.5 is therefore equivalent to the definition in [Jar, Part II,Ch.8,§8.4,Example 3.A,p.153], and it is [Scha, Ch.III,§3,Example 4(d),p.81].

**PROPOSITION 2.1.1.6.** *Let $m\ge 0$ be an integer. The locally convex topological $\mathbf C$-vector space $\mathcal S(\mathbf R^m)$ is nuclear, Fréchet and reflexive. The strong dual $\mathcal S(\mathbf R^m)'_\beta$ is complete, nuclear and Montel.*

**REMARK 2.1.1.7.** We recall that a Hausdorff locally convex topological complex vector space $E$ is *semi-Montel* if and only if it satisfies the Heine-Borel property: if $B\subset E$ is a bounded subset, then $B$ is relatively compact in $E$; see [Jar, Part II,§11]. By [Jar, Part II,§11,Prop.1], if $E$ is semi-Montel, then it is barrelled (see [Jar, Part II,§11.1]) if and only if it is reflexive, and semi-Montel spaces satisfying any of these additional properties are, by definition, Montel spaces.

**PROOF OF PROPOSITION 2.1.1.6.** Nuclearity of $\mathcal S(\mathbf R^m)$ is [Tre, Part III,Ch.51,Corollary,p.530]. The family of seminorms $\|\cdot\|_{\alpha,\beta}$ from (2.1.1.4) is separating. The locally convex topology on $\mathcal S(\mathbf R^m)$ is therefore Hausdorff.

The seminorms from (2.1.1.4) are countably many, and hence $\mathcal S(\mathbf R^m)$ is, by [Kothe-I, Ch.4,§18,(2),p.205], metrizable. It is Fréchet so long as it is complete. Since it is metrizable (because (2.1.1.3) is a countable fundamental family of seminorms), it is enough to show convergence of any Cauchy *sequence* $\{f_k\}_{k\ge 0}$ in $\mathcal S(\mathbf R^m)$ with respect to the topology generated by the given seminorms.

We first observe that $\{f_k\}_{k\ge 0}$ converges with respect to the uniform norm topology, since $C_0(\mathbf R^m)$ is Banach (see [Fol, Prop.4.35]). We call its limit $f$.

The functions $g_{\alpha,k}:=D^\alpha_x f_k(x)$ also define a Cauchy sequence $\{g_{\alpha,k}\}_{k\ge 0}$ for each $\alpha\in\mathbf N^m$ with respect to the uniform norm topology on $C_0(\mathbf R^m)$, converging to some $f_\alpha$, which is seen to be $D^\alpha_x f$ since the convergence is, in particular, uniform on compact subsets for $\{D^\alpha_x f_k\}_{k\ge 0}$ for each $\alpha\in\mathbf N^m$, and $f_\alpha$ is therefore of the desired form on every compact subset of $\mathbf R^m$.

## PDF page 62

62  CHAPTER 2. ADELIC $\theta$-FUNCTIONS

The function $f$ is therefore smooth and rapidly decaying at infinity. We need to show that the convergence of $\{f_k\}_{k\ge 0}$ to $f$ is in the sense of the Hausdorff locally convex topology on $\mathcal S(\mathbf R^m)$.

For each $\beta\in\mathbf N^m$, $\{x^\beta g_{\alpha,k}\}_{k\ge 0}$ is a Cauchy sequence for the uniform topology on $C_0(\mathbf R^m)$, and its limit $f_{\alpha,\beta}$ is, by uniqueness, $x^\beta D^\alpha_x f$, since this can be checked locally. It follows that $x^\beta D^\alpha_x f_k\to x^\beta D^\alpha_x f$ with respect to the uniform topology on $C_0(\mathbf R^m)$, and since this holds for every $\alpha,\beta\in\mathbf N^m$, we deduce that $f_k\to f$ in $\mathcal S(\mathbf R^m)$.

Since $\mathcal S(\mathbf R^m)$ is nuclear, then every bounded subset in $\mathcal S(\mathbf R^m)$ is relatively compact by [Tre, Part III,Ch.50,Prop.50.2(5.12)]. By completeness, $\mathcal S(\mathbf R^m)$ has the Heine-Borel property, i.e. it is semi-Montel as per [Jar, Part II,Ch.11,§11.5,p.230].

By [NB, Thm.13.2.13], its strong dual $\mathcal S(\mathbf R^m)'_\beta$, the space of tempered distributions on $\mathbf R^m$, is complete, and it is nuclear by [Tre, Part III,Ch.50,Prop.50.6]. Both $\mathcal S(\mathbf R^m)$ and $\mathcal S(\mathbf R^m)'_\beta$ are reflexive (the latter by [Tre, Part II,Prop.36.10]). We further refer the reader to [Sch-a, Ch.VII,§3].

By reflexivity and [Jar, Part II,Ch.11,§11.5,Prop.1], $\mathcal S(\mathbf R^m)$ is Montel, and hence so is $\mathcal S(\mathbf R^m)'_\beta$ by [Jar, Part II,Ch.11,§11.5,Prop.4(f)]. $\square$

2.1.1.3. *Schwartz-Bruhat functions on Hausdorff locally compact abelian groups.* Definition 2.1.1.4 bootstraps to the case of elementary abelian Lie groups, i.e. Hausdorff locally compact abelian groups isomorphic to $\mathbf R^m\times(\mathbf R/\mathbf Z)^n\times\mathbf Z^k\times F$ for integers $m,n,k\ge 0$, and a finite abelian group $F$, and, from this case, to the case of arbitrary Hausdorff locally compact abelian groups through their classification theory. This is done in Bruhat’s paper [Bru], and specifically in [Bru, §9]. Such functions are termed *Schwartz-Bruhat* throughout this work.

By Lemma D.1.3.7(2), the Hausdorff locally convex topological $\mathbf C$-vector space of Schwartz-Bruhat functions on *elementary* Lie groups (i.e. Hausdorff locally compact abelian groups of the form $\mathbf R^m\times(\mathbf R/\mathbf Z)^n\times\mathbf Z^k\times F$) is linearly and topologically isomorphic to $\mathcal S(\mathbf R^m)\widehat{\otimes}_\pi C^\infty((\mathbf R/\mathbf Z)^n)\widehat{\otimes}_\pi{\mathbf s}_k\otimes_\pi\mathbf C^F$, where $\mathcal S(\mathbf R^m)$ was studied in Proposition 2.1.1.6, $C^\infty((\mathbf R/\mathbf Z)^n)$ is endowed with the topology of uniform convergence on functions and their derivatives of arbitrary order, and ${\mathbf s}=\mathcal S(\mathbf Z)$ is the space of rapidly decaying $\mathbf Z$-indexed sequences ($\{a_k\}_{k\in\mathbf Z}$ such that $a_k=O(|k|^{-N})$ for every integer $N\ge 0$ as $|k|\to+\infty$), with ${\mathbf s}_k$ the $k$-th projective tensor power of ${\mathbf s}$.

Recall that an arbitrary Hausdorff locally compact abelian group $G$ is the direct limit, as a topological abelian group, of its open compactly generated subgroups (i.e. generated as a group by a compact neighborhood of $1$).

Any compact subgroup $k\subset G$ is called *good* (following [Bru, §1]) if and only if its open annihilator $k^\perp$ is ompactly generated as a subgroup of the dual group $\widehat G$. Any open compactly generated subgroup $\Gamma\subset G$ containing $k$ is such that $\Gamma/k$ is an elementary Lie group (seen upon combining, for instance, [DE, Cor.4.2.5] and [DE, Cor.4.2.6] with [DE, Prop.3.6.1(c)]).

We now briefly recall how to define and topologize $\mathcal S(G)$ (we refer the reader to [Bru, §9]). To construct $\mathcal S(G)$, we will work with pairs $(k,\Gamma)$ where $k\subset G$ is a good subgroup and $\Gamma\subset G$ is an open compactly generated subgroup containing $k$. Since $\Gamma/k$ is an abelian Lie group, we have already discussed the space $\mathcal S(\Gamma/k)$ of Schwartz-Bruhat functions. These can be viewed as special $k$-invariant functions on $\Gamma$, and we topologize this space as discussed above. The collection of all such pairs $(k,\Gamma)$ is filtered and $\mathcal S(G)$ is defined to be the filtered colimit of the $\mathcal S(\Gamma/k)$’s as a $\mathbf C$-linear space, linearly topologized with the locally convex inductive limit topology.

The topological vector space $\mathcal S(G)$ is Hausdorff for general $G$ (see Theorem D.1.5.7, resting, as far as the Hausdorff property is concerned, on Lemma D.1.5.6). If $G$ is separable, $\mathcal S(G)$ is complete, nuclear and Montel, and so is its strong dual $\mathcal S(G)'_\beta$. We refer the reader to Theorem D.1.5.7 for a proof.

## PDF page 63

**2.1. SCHWARTZ-BRUHAT FUNCTIONS** · **63**

As a special case, for $G=\mathbf R$ the classical Schwartz space $\mathcal S(\mathbf R)$ is recovered, and it is complete, nuclear and Montel, with strong dual $\mathcal S(\mathbf R)'_\beta$ sharing the same properties. Throughout this work, we will be referring to $\mathcal S(G)$ as the *Schwartz-Bruhat space* of $G$, and to its topology as the *Schwartz-Bruhat topology*.

**2.1.2. Local Schwartz-Bruhat functions.** The main cases of Hausdorff locally compact abelian groups $G$ of interest to this work are $G=\mathbf A_F$ for a number field $F$, $G=\mathbf A_{F,S}$ for $S$ a finite set of places of $F$ containing the Archimedean places, $G=C_F=\mathrm{GL}_1(\mathbf A_F)/F^\times$, the idele class group of $F$, and its $S$-local subgroup $C_{F,S}=(\mathrm{GL}_1(\mathbf A_{F,S})\times\prod_{v\notin S}\mathcal O_{F_v}^\times)/\mathcal O_{F,S}^\times$, and $G=J_{F,S}=\mathrm{GL}_1(\mathbf A_{F,S})/\mathcal O_{F,S}^\times$, the quotient of $C_{F,S}$ by $1\times\prod_{v\notin S}\mathcal O_{F_v}^\times$.

We will require, later in Chapter 3, the Hausdorff locally convex topological $\mathbf C$-vector spaces of Schwartz-Bruhat functions on the idele class group $C_F$, and the $S$-idele class group $C_{F,S}$, along with its quotient $J_{F,S}$. These will be introduced, and their properties reworked, when the need arises.

In this subsection, we treat the case $G=F_v^\times$, for $v$ a non-Archimedean place of $F$.

2.1.2.1. *Smooth functions on non-Archimedean fields.* We recall that for $G$ a Hausdorff locally compact abelian group, a function $f:G\to\mathbf C$ is called *smooth* if and only if it is $k$-invariant for some compact subgroup $k\subset G$ whose open annihilator $k^\perp$ is compactly generated as a subgroup of the dual group $\widehat G$ and for every open compactly generated subgroup $\Gamma\subset G$ containing $k$ the induced function on the quotient $\Gamma/k$ (an elementary Lie group!) is smooth in the sense of differential geometry.

We denote by $C^\infty(G)$ the $\mathbf C$-algebra of smooth complex-valued functions on $G$, and denote by $C_c^\infty(G)$ the subspace of those elements of $C^\infty(G)$ that are also compactly supported. When $G$ is locally profinite, $C_c^\infty(G)$ coincides with the $\mathbf C$-linear space of complex-valued locally constant functions with compact support.

Let $F$ be a number field, $v$ a finite place of $F$. We have, as $\mathbf C$-linear spaces,

$$
C_c^\infty(F_v)=\mathcal S(F_v).
$$

REMARK 2.1.2.1. We caution the reader that the containment $C_c^\infty(F_v^\times)\subset\mathcal S(F_v^\times)$ is strict. Indeed, via $\mathcal O_{F_v}^\times$-invariance, $\mathcal S(\pi_v^{\mathbf Z})\simeq\mathcal S(\mathbf Z)$ (for $\pi_v$ a uniformizer at $v$) is a subspace of $\mathcal S(F_v^\times)$, and $\mathcal S(\mathbf Z)$ is the space of rapidly decaying $\mathbf Z$-indexed sequences.

2.1.2.2. *The locally convex topological complex vector spaces $\mathcal S(F_v)$ for $v\in\Sigma_{F,f}$.* In this subsection we recall how to explicitly describe the elements of the Schwartz-Bruhat space of the local fields $F_v$ for $v$ non-Archimedean.

As a Hausdorff locally compact abelian group, we recall that $F_v$ is the filtered union of compact open subgroups $K_v\subset F_v$, and for two compact open subgroups $K_{v,1}\subset K_{v,2}$, by openness of $K_{v,1}$ in $K_{v,2}$ and compactness of $K_{v,2}$ the quotient $K_{v,2}/K_{v,1}$ is a finite abelian group.

As per the very construction of $\mathcal S(G)$ for $G$ a Hausdorff locally compact abelian group, the basic Hausdorff locally convex topological vector spaces $\mathcal S(k,\Gamma)$ (see [Bru, §1]) arising in the construction are all of the form $\mathcal S(K_{v,2}/K_{v,1})$, which is a finite dimensional complex vector space. As such, it carries a unique Hausdorff locally convex topology (i.e. the Euclidean topology) compatible with the Euclidean topology on the complex numbers, and $\mathcal S(F_v)$ is a locally convex inductive limit of finite dimensional complex vector spaces, each endowed with its natural Euclidean topology.

REMARK 2.1.2.2. We inform the reader concerned about the possibility of uncountably-indexed locally convex inductive limits arising, that the locally convex inductive systems of interest throughout this work will always be equivalent to countable ones. They will often arise from topological vector spaces related through formation of quotients of spaces of Schwartz-Bruhat functions on second-countable Hausdorff locally compact

## PDF page 64

**64** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

abelian groups. For example, $\mathcal S(F_v)$ is countably generated, since $F_v$ has a countable $0$-neighborhood base of compact open subgroups.

REMARK 2.1.2.3 (On the necessity of topologizing $\mathcal S(F_v)$). Let $F$ be a number field. The aim of the next few Chapters of this work is to collect certain averages over $F^\times$-orbits on $\mathrm{GL}_1(\mathbf A_F)$ of Schwartz-Bruhat functions on $\mathbf A_F$, into topological vector spaces, for then studying them through the lens of the Mellin transform. Several subquotients of such topological vector spaces will be essential in performing the trace calculation that is the main subject of study of this work.

Their topology will be of great importance, because it will be one of the purposes of the first half of this work to identify Schauder bases on such subquotients, and Schauder bases are sensitive to the topology of their linear environment. The defining conditions of a Schauder basis is that every element of the ambient Hausdorff locally convex topological vector space, should be expressible as a convergent countably infinite linear combination of basis elements in a unique way, with continuous coefficient functionals.

To build such topological vector spaces, we will be starting off from the Schwartz-Bruhat topology on $\mathcal S(\mathbf A_F)$ and $\mathcal S(\mathbf A_{F,S})$. It renders itself necessary to topologize $\mathcal S(F_v)$ for every non-Archimedean place as well, as simple as such topology is: it is the finest locally convex topology, equivalently the topology rendering any linear form continuous.

We deduce the following two structural results on $\mathcal S(F_v)$ and the spaces $\mathcal S(G)$ for $G=\prod_{v\in S}F_v$ with $S$ a finite set of finite places of the number field $F$, and $G=\widehat{\prod}_{v\notin S}(F_v,\mathcal O_{F_v})$ for $S$ a finite set of places of $F$ containing all the Archimedean places:

PROPOSITION 2.1.2.4. *Let $F$ be a number field, $v$ a finite place.*

(1) *$\mathcal S(F_v)$ is countably $\mathbf C$-linearly generated, and it carries the finest locally convex topology. In particular, it is a strict LF-space.*

(2) *$\mathcal S(F_v)$ is Hausdorff locally convex, complete, nuclear, Montel, and its strong dual is a nuclear Fréchet space.*

(3) *Every $\mathbf C$-linear subspace of $\mathcal S(F_v)$ is linearly and topologically complemented.*

Recall that a subspace $V$ of a Hausdorff locally convex topological $\mathbf C$-vector space $E$ is called *linearly and topologically complemented* if and only if there exists a subspace $W\subset E$ such that $V\oplus W\to E$ is a homeomorphism. In particular, $V$ and $W$ are closed, since $E$ is Hausdorff.

PROOF. A cofinal sequence of compact open subgroups of $F_v$ is given by $\{\pi_v^m\mathcal O_{F_v}\}_{m\in\mathbf Z}$, for $\pi_v$ any choice of generator of the maximal ideal of the complete discrete valuation ring of $\mathcal O_{F_v}$.

As a $\mathbf C$-linear space, $\mathcal S(F_v)$ is therefore the countable inductive limit of the countably many finite dimensional vector spaces $\mathcal S(\pi_v^N\mathcal O_{F_v}/\pi_v^m\mathcal O_{F_v})$ for $N\le m$, where the finite group $\pi_v^N\mathcal O_{F_v}/\pi_v^m\mathcal O_{F_v}$ is endowed with the discrete topology since $\pi_v^m\mathcal O_{F_v}$ is open in $\pi_v^N\mathcal O_{F_v}$. As such, it is countably linearly generated. By Proposition C.2.5.1(6), the rest of the assertions hold. □

EXAMPLE 2.1.2.5. Every Schwartz-Bruhat function on $\mathbf Q_p$, for $p$ an arbitrary prime number, is smooth and compactly supported, hence locally constant with compact support, i.e. we have $\mathcal S(\mathbf Q_p)=C_c^\infty(\mathbf Q_p)$. Since every open subset in $\mathbf Q_p$ is a finite disjoint union of open $p$-adic balls, i.e. subsets of the form $a+p^N\mathbf Z_p$, for some $N\in\mathbf Z^+$ and $a\in\mathbf Q_p$, then, upon writing $1_{a+p^N\mathbf Z_p}$ for the indicator function of $a+p^N\mathbf Z_p$, each $f\in\mathcal S(\mathbf Q_p)$ is of the form:

$$
f=\sum_{i=1}^n c_i1_{a_i+p^{N_i}\mathbf Z_p}
$$

for nonzero integers $N_i$ and $a_i\in\mathbf Q_p$, and for $c_i\in\mathbf C$.

## PDF page 65

**2.1. SCHWARTZ-BRUHAT FUNCTIONS** · **65**

EXAMPLE 2.1.2.6. Similarly to Example 2.1.2.5, every Schwartz-Bruhat function on $F_v$, $v$ a non-Archimedean place of the number field $F$, is smooth and compactly supported, hence locally constant with compact support. Every open subset in $F_v$ is a finite disjoint union of subsets of the form $a+\pi_v^N\mathcal O_{F_v}$, for $\pi_v$ a uniformizer at $v$, for some $N\in\mathbf Z^+$ and $a\in F_v$, then, upon writing $1_{a+\pi_v^N\mathcal O_v}$ for the indicator function of $a+\pi_v^N\mathcal O_{F_v}$, each $f\in\mathcal S(F_v)$ is of the form:

$$
f=\sum_{i=1}^n c_i1_{a_i+\pi_v^{N_i}\mathcal O_{F_v}} \tag{2.1.2.1}
$$

for nonzero integers $N_i$ and $a_i\in F_v$, and for $c_i\in\mathbf C$.

REMARK 2.1.2.7. For any finite place $v$ of $F$, $\mathcal S(F_v)$ is topologized with the locally convex inductive limit induced by the unique topology of the finite dimensional $\mathbf C$-vector spaces comprising the inductive limit presentation of the $\mathbf C$-linear space $\mathcal S(F_v)$.

PROPOSITION 2.1.2.8. *Let $F$ be a number field, $S_1$ a finite set of non-Archimedean places of $F$, $S_2$ a finite set of places of $F$ containing all Archimedean places. Let $G_1:=\prod_{v\in S_1}F_v$ and $G_2:=\widehat{\prod}_{v\notin S_2}(F_v,\mathcal O_{F_v})$.*

(1) *The Hausdorff locally convex topological $\mathbf C$-vector spaces $\mathcal S(G_1)$ and $\mathcal S(G_2)$ are countably $\mathbf C$-linearly generated, and carry the finest locally convex topology. In particular, they are strict LF-spaces, and hence bornological.*

(2) *$\mathcal S(G_1)$ and $\mathcal S(G_2)$ are Hausdorff locally convex, complete, nuclear, Montel, and their strong duals are nuclear Fréchet spaces.*

(3) *Every $\mathbf C$-linear subspace of $\mathcal S(G_1)$, respectively $\mathcal S(G_2)$ is linearly and topologically complemented.*

REMARK 2.1.2.9. We note that Proposition 2.1.2.8 applies, in particular, to $G=\mathbf A_F^f$. More generally, if the Hausdorff locally compact abelian group $G$ is locally profinite, $\mathcal S(G)$ carries the finest locally convex topology, and Proposition C.2.5.1 describes the properties of the finest locally convex topology.

If $G$ is, in addition, separable, then $\mathcal S(G)$ is countably $\mathbf C$-linearly generated, and Proposition C.2.5.1(6) applies. In particular, for $G$ locally profinite and separable, $\mathcal S(G)$ is complete, nuclear, Montel, and its strong dual $\mathcal S(G)'_\beta$ is nuclear Fréchet.

PROOF. We call $\widehat{\mathcal O}_{F,S}$ the compact open subgroup $\prod_{v\in S_1}\mathcal O_{F_v}\subset G_1$, and $\widehat{\mathcal O}_{F,\Sigma_F-S_2}$ the compact open subgroup $\prod_{v\notin S_2}\mathcal O_{F_v}\subset G_2$.

A cofinal sequence of compact open subgroups of $G_1$, respectively $G_2$, is given by $\{N\widehat{\mathcal O}_{F,S_1}\}_{N\in\mathbf Z^+}$, respectively $\{N\widehat{\mathcal O}_{F,\Sigma_F-S_2}\}_{N\in\mathbf Z^+}$.

As a $\mathbf C$-linear space, $\mathcal S(G_1)$ is therefore the countable inductive limit of the countably many finite dimensional vector spaces $\mathcal S(N'\widehat{\mathcal O}_{F,S_1}/N\widehat{\mathcal O}_{F,S_1})$ for $0<N'\le N$. Similarly, as a $\mathbf C$-linear space, $\mathcal S(G_2)$ is the countable inductive limit of the countably many finite dimensional vector spaces $\mathcal S(N'\widehat{\mathcal O}_{F,\Sigma_F-S_2}/N\widehat{\mathcal O}_{F,\Sigma_F-S_2})$. As such, $\mathcal S(G_1)$ and $\mathcal S(G_2)$ are both countably linearly generated. By Proposition C.2.5.1(6), the rest of the assertions hold. □

2.1.2.3. *Uniform sequential continuity of the continuous left $F_v^\times$-module $\mathcal S(F_v)$.* The Hausdorff locally compact abelian group $F_v^\times$ acts on $F_v$ by left-translation. Its compact open subgroup $\mathcal O_{F_v}^\times$ acts on $F_v$ accordingly.

We denote by:

$$
\rho_v:F_v^\times\times\mathcal S(F_v)\to\mathcal S(F_v) \tag{2.1.2.2}
$$

such action, assigned by $\rho_v(g,f)(x):=f(g^{-1}x)$ as functions of $x\in F_v$.

Let $S_1$ be a finite set of non-Archimedean places of $F$, and $S_2$ a finite set of places of $F$ containing all the Archimedean places.

## PDF page 66

**66** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

The Hausdorff locally compact abelian groups $\mathrm{GL}_1(\prod_{v\in S_1}F_v)$ and $\mathrm{GL}_1(\widehat{\prod}_{v\notin S_2}(F_v,\mathcal O_{F_v}))$ act continuously on $\prod_{v\in S_1}F_v$, respectively $\widehat{\prod}_{v\notin S_2}(F_v,\mathcal O_{F_v})$, by left-translation. We denote by

$$
\rho_{F,S_1},\ \rho_{F,\Sigma_F-S_2}
$$

such actions.

We denote by $\widehat{\mathcal O}_{F,S_1}$ the compact open subgroup of $\prod_{v\in S_1}F_v$ defined as $\prod_{v\in S_1}\mathcal O_{F_v}$, and by $\widehat{\mathcal O}_{F,\Sigma_F-S_2}$ the compact open subgroup of $\widehat{\prod}_{v\notin S_2}(F_v,\mathcal O_{F_v})$.

The continuous left-translation action of $\mathcal O_{F_v}^\times$, respectively of $\widehat{\mathcal O}_{F,S_1}^\times$, $\widehat{\mathcal O}_{F,\Sigma_F-S_2}^\times$, is “uniformly continuous” in the following sense:

LEMMA 2.1.2.10. *Let $F$ be a number field.*

(1) *Let $v$ a finite place of $F$. Let $\{f_m\}_{m\ge 0}$ be a convergent Cauchy sequence in $\mathcal S(F_v)$, with limit $f$. Let $p$ be any continuous seminorm on $\mathcal S(F_v)$. Then we have:*

$$
\lim_{m\ge 0}\sup_{g\in\mathcal O_{F_v}^\times}p(\rho_v(g,f_m-f))=0. \tag{2.1.2.3}
$$

(2) *Let $S_1$ be a finite set of non-Archimedean places of $F$. Let $\{f_m\}_{m\ge 0}$ be a convergent Cauchy sequence in $\mathcal S(\prod_{v\in S_1}F_v)$. Let $p$ be a continuous seminorm on $\mathcal S(\prod_{v\in S_1}F_v)$. Then we have:*

$$
\lim_{m\ge 0}\sup_{g\in\widehat{\mathcal O}_{F,S_1}^\times}p(\rho_{F,S_1}(g,f_m-f))=0. \tag{2.1.2.4}
$$

(3) *Let $S_2$ be a finite set of places of $F$ containing all the Archimedean places. Let $\{f_m\}_{m\ge 0}$ be a convergent Cauchy sequence in $\mathcal S(\widehat{\prod}_{v\notin S_2}(F_v,\mathcal O_{F_v}))$, with limit $f$. Then we have:*

$$
\lim_{m\ge 0}\sup_{g\in\widehat{\mathcal O}_{F,\Sigma_F-S_2}}p(\rho_{F,\Sigma_F-S_2}(g,f_m-f))=0. \tag{2.1.2.5}
$$

PROOF. (1) : By Proposition 2.1.2.4(1), $\mathcal S(F_v)$ carries the finest locally convex topology, and it is countably linearly generated.

Every convergent Cauchy sequence $\{f_m\}_{m\ge 0}$ in $\mathcal S(F_v)$ is bounded (see Remark C.4.3.4).

By Proposition C.2.5.1(4), there exist integers $N\le m$ and a bounded subset $B\subset\mathcal S(\pi_v^N\mathcal O_{F_v}/\pi_v^m\mathcal O_{F_v})$ whose image in $\mathcal S(F_v)$ contains $\{f_m\}_{m\ge 0}$ and its limit $f$. Since the compact open subgroups $\pi_v^N\mathcal O_{F_v}$, $\pi_v^m\mathcal O_{F_v}\subset F_v$ are $\mathcal O_{F_v}^\times$-stable, the continuous left-translation action by $\mathcal O_{F_v}^\times$ preserves the finite dimensional subspace $V$ obtained as the image in $\mathcal S(F_v)$ of $\mathcal S(\pi_v^N\mathcal O_{F_v}/\pi_v^m\mathcal O_{F_v})$. Since $\mathcal O_{F_v}^\times$ is profinite, its action factors through a finite quotient. The supremum in (2.1.2.3) is therefore realized as a maximum over a finite set of representatives in $\mathcal O_{F_v}^\times$ for such finite quotient coset space, and (2.1.2.3) therefore holds by continuity of the action of $\mathcal O_{F_v}^\times$ on $\mathcal S(F_v)$.

(2) and (3) follow from a similar argument, using the cofinal sequences of compact open subgroups $N\widehat{\mathcal O}_{F,S_1}\subset\prod_{v\in S_1}F_v$, respectively $N\widehat{\mathcal O}_{F,\Sigma_F-S_2}\subset\widehat{\prod}_{v\notin S_2}(F_v,\mathcal O_{F_v})$, as $N$ varies over the positive integers, and the fact that both $\widehat{\mathcal O}_{F,S_1}^\times$ and $\widehat{\mathcal O}_{F,\Sigma_F-S_2}^\times$ are profinite. □

REMARK 2.1.2.11. The conclusions of Lemma 2.1.2.10 hold for most of the actions of the compact groups $G$ arising throughout this work. We will say the continuous action $\rho_G$ of $G$ on the Hausdorff locally convex topological $\mathbf C$-vector space $E$ is *uniformly continuous*, for any convergent net $u_i\to u$, we have $\sup_{g\in G}p(\rho_G(g,u_i-u))\to 0$ for any continuous seminorm $p$ on $E$.

This equivalently means that for any convergent Cauchy net $f_i\to f$ in $E$, $i\in I$ for $I$ a directed set, the vector valued functions $u_i:G\to E$ defined as $\rho_G(g,f_i)$ converge to $\rho_G(g,f)$ in $C(G,E)$ equipped with the topology of uniform convergence (i.e. generated by the family of seminorms $\sup_{g\in G}p(\cdot)$ as $p$ varies over a fundamental set of continuous seminorms on $E$).

## PDF page 67

**2.1. SCHWARTZ-BRUHAT FUNCTIONS** · **67**

We term this condition *sequential uniform continuity*, if it holds for convergent sequences as opposed to general nets; see Proposition D.1.9.2.

**Remark 2.1.2.12.** Let $F$ be a number field, $v$ a finite place of $F$. Let $S$ be a finite set of places containing all the Archimedean places.

We denote by $\widehat{\mathcal O}^\times_{F,\Sigma_F-S}$ the profinite group $\prod_{v\notin S}\mathcal O^\times_{F_v}$, and by $\widehat{\prod}_{v\notin S}(F_v,\mathcal O_{F_v})$ the restricted product of the additive groups of the non-Archimedean local fields $F_v$ constrained by the compact open subgroups $\mathcal O_{F_v}$, for each non-Archimedean place $v\notin S$.

We know from Proposition 2.1.2.4 and Proposition 2.1.2.8, that $\mathcal S(F_v)$ and $\mathcal S(\widehat{\prod}_{v\notin S}(F_v,\mathcal O_{F_v}))$ are bornological and complete, since they both carry the finest locally convex topology.

We know from Lemma 2.1.2.10 that the continuous left-translation action by $\mathcal O_{F_v}^\times$, respectively $\widehat{\mathcal O}^\times_{F,\Sigma_F-S}$, on each, is sequentially uniformly continuous. The assumptions of Lemma 4.3.3.1 in Chapter 4 are therefore satisfied, and the Lemma applies upon choosing $E$ to be $\mathcal S(F_v)$, respectively $\mathcal S(\widehat{\prod}_{v\notin S}(F_v,\mathcal O_{F_v}))$, or a quotient by a (necessarily closed) subspace, and upon choosing $G=\mathcal O_{F_v}^\times$, respectively $\widehat{\mathcal O}^\times_{F,\Sigma_F-S}$. We will be recording this observation here for later reference.

**2.1.3. Adelic Schwartz-Bruhat functions.** We refer the reader to §2.1 for more on Schwartz-Bruhat functions on a general Hausdorff locally compact abelian group $G$, following Bruhat's work [Bru] and resting on the structure theory of Hausdorff locally compact abelian groups. We often refer, throughout this work, to the Hausdorff locally convex topological $\mathbf C$-vector space $\mathcal S(G)$ of Schwartz-Bruhat functions on $G$, as the *Schwartz-Bruhat space* of $G$.

2.1.3.1. *Kernel Theorem for the Adelic Schwartz-Bruhat spacee.* In this subsection, we focus on the case $G=\mathbf A_F,\mathbf A_{F,S}$ for $F$ a number field and $S$ a finite set of places of $F$ containing all the Archimedean places.

We begin with the special case $F=\mathbf Q$.

**Example 2.1.3.1.** We recall that we have an isomorphism $\mathbf A_{\mathbf Q}=\mathbf R\times\mathbf A^f_{\mathbf Q}$ of Hausdorff locally compact abelian groups, where $\mathbf A^f_{\mathbf Q}$ is the topological ring of the finite adeles of $\mathbf Q$. See Definition A.1.1.3(2). As an additive topological group, $\mathbf A^f_{\mathbf Q}$ is itself a Hausdorff locally compact abelian group, totally disconnected and such that a neighborhood base at $0$ is given by the subsets of the form $N\widehat{\mathbf Z}$ for $N\in\mathbf Z^+$.

Any compact open subgroup of $\mathbf A^f$ contains one of the form:

$$
K=\prod_p K_p
$$

with finite index, where $K_p=\mathbf Z_p$ for all but finitely many primes, and $K_p\subset\mathbf Q_p$ is a compact open subgroup of $\mathbf Q_p$ for all $p$. As such, $K_p\subset p^{-N_p}\mathbf Z_p$ for some integer $N_p\in\mathbf Z$.

As for the case of the $p$-adic rationals, and, in fact, as a consequence of the description of $\mathcal S(\mathbf Q_p)$ from Example 2.1.2.5, the $\mathbf C$-vector space $\mathcal S(\mathbf A^f_{\mathbf Q})$ agrees with the $\mathbf C$-vector space of all smooth compactly supported functions on $\mathbf A^f_{\mathbf Q}$. The $\mathbf C$-linear space $\mathcal S(\mathbf A^f_{\mathbf Q})$ is topologized in a manner similar to $\mathcal S(\mathbf Q_p)$ (see Proposition 2.1.2.8(1) applied to $G_2=\mathbf A^f_{\mathbf Q}$).

There is a canonical linear isomorphism

(2.1.3.1)

$$
\mathcal S(\mathbf R)\otimes\mathcal S(\mathbf A^f_{\mathbf Q})\to\mathcal S(\mathbf A_{\mathbf Q})
$$

leading to a description of the generic element of $\mathcal S(\mathbf A_{\mathbf Q})$: it is a finite linear combination of functions of the form:

$$
f=f_\infty\otimes\bigotimes_p f_p
$$

## PDF page 68

**CHAPTER 2. ADELIC $\theta$-FUNCTIONS** · **68**

where $f_\infty\in\mathcal S(\mathbf R)$ and, for each prime number $p$, $f_p$ is the indicator function of a subset of the form $a+p^N\mathbf Z_p$ for $N\in\mathbf Z$ and $a\in\mathbf Q_p$, and $f_p=\mathrm{1}_{\mathbf Z_p}$ for all but finitely many primes.

In fact, the linear isomorphism from (2.1.3.1) can be promoted to a topological one, by topologizing the algebraic tensor product as the *inductive* topological tensor product: it is the finest locally convex topology promoting the canonical bi-linear map $\mathcal S(\mathbf R)\times\mathcal S(\mathbf A^f_{\mathbf Q})\to\mathcal S(\mathbf R)\otimes_\iota\mathcal S(\mathbf A^f_{\mathbf Q})$ to a separately continuous bi-linear map. We will be proving this in Proposition 2.1.3.2 below. In particular, $\mathcal S(\mathbf R)\otimes_\iota\mathcal S(\mathbf A^f_{\mathbf Q})$ is thereby complete, this completeness ultimately stems from expressing that topological tensor product as a strict countable inductive limit of Fréchet spaces (such as a product of finitely many copies of $\mathcal S(\mathbf R)$), which is complete by [Scha, Ch.II,6.6,p.59].

We refer the reader to the discussion following (C.2.3.22) from §C.2.3, and to the references contained therein, for more on inductive tensor products. Proposition C.2.3.13 provides further basic properties, as well as more on other tensor topologies (projective and injective) which will be of relevance throughout this work.

Suffices here to say that inductive tensor products behave well with respect to inductive constructions (such as locally convex inductive limits) and they lend themselves to kernel theorems (see Lemma D.1.8.1) for spaces of test functions. We further refer the reader to Remark 2.1.3.3 below.

**Lemma 2.1.3.2.** *Let $F$ be a number field. The locally convex topological complex vector spaces $\mathcal S(\mathbf A^f_F)$ and $\mathcal S(\mathbf A_F)$ satisfy the following conditions:*

(1) *They are strict locally convex inductive limits of nuclear Fréchet spaces, and hence strict LF-spaces. They are Hausdorff, complete, nuclear and Montel, and their strong duals satisfy the same properties. Moreover, $\mathcal S(\mathbf A^f_F)'_\beta$ is a nuclear Fréchet space.*

(2) *The canonical linear map*

(2.1.3.2)

$$
\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota\mathcal S(\mathbf A^f_F)\to\mathcal S(\mathbf A_F)
$$

*is a linear topological isomorphism. In particular, the inductive tensor product on the left side of (2.1.3.2) is complete.*

(3) *For any $f\in\mathcal S(\mathbf A_F)$, there exist:*

*(1) an integer $r\ge 1$.*

*(2) Functions $\{f_i\}_{1\le i\le r}\subset\mathcal S(\mathbf A_F)$ such that for each $1\le i\le r$, $f_i$ has the form $f_i=f_{\infty,i}\otimes f_{0,i}$ where $f_{\infty,i}\in\mathcal S(\mathbf A_{F,S_\infty})$ and $f_{0,i}=\prod_{v\in\Sigma_{F,f}}1_{K_{v,i}}$, where $K_{v,i}\subset F_v$ is a compact subgroup with $K_{v,i}=\mathcal O_{F_v}$ for all but finitely many $v\in\Sigma_{F,f}$.*

*(3) Complex numbers $\{c_i\}_{1\le i\le r}\subset\mathbf C$.*

*such that $f=\sum_{1\le i\le r}c_if_i$.*

**Remark 2.1.3.3** (Cautionary remark on inductive and projective tensor topologies). We refer to [Scha, Ch.II,§5] for a discussion of projective topologies. For $E,F$ two locally convex complex vector spaces, there exists on the algebraic tensor product $E\otimes F$ a unique locally convex topology such that for any locally convex complex vector space $G$, continuous linear maps $E\otimes F\to G$ correspond bijectively to *continuous* (i.e. not merely separately continuous) bi-linear maps $E\times F\to G$ under the canonical correspondence given by composing a continuous linear map $E\otimes F\to G$ with the canonical continuous linear map $E\times F\to E\otimes F$. This topology is referred to as the projective tensor product topology on $E\otimes F$, due to its projective nature, and also termed $\pi$-topology. A fundamental system of neighborhoods of $0$ for this topology on $E\otimes F$ is given by the convex circled hulls of the sets of the form

$$
U_i\otimes V_j:=\{u\otimes v:u\in U_i,v\in V_j\}
$$

where $U_i$ and $V_j$ are fundamental systems of neighborhoods of $0$ in $E$, respectively $F$.

In this work, the projective topology is often used in combination with the inductive tensor topology. The completed inductive tensor product is denoted by $E\,\overline{\otimes}\,F$, and it is most suitable to inductive constructions

## PDF page 69

**2.1. SCHWARTZ-BRUHAT FUNCTIONS** · **69**

and “kernel theorems” (results expressing a class of functions on a product space as a suitable completed tensor product of function spaces on the factors). Lemma D.1.8.1 gives examples of kernel theorems with Schwartz spaces and their strong duals in the setting of locally compact abelian groups.

We refer the reader to §C.2.3 of Appendix C, to [Gro-c, Thm.1] (and the discussion preceding the Theorem), [Scha, Ch.II,§5] and [Jar, Part III,§15.1] for a discussion of the projective (or $\pi$-)topology on an algebraic tensor product of two Hausdorff locally convex topological vector spaces, and to (C.2.3.23) and particularly to Proposition C.2.3.13 for a discussion and basic properties of inductive tensor products.

We observe here that the canonical continuous linear map:

$$
\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota\mathcal S(\mathbf A^f_F)\to\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\mathcal S(\mathbf A^f_F)
$$

is a continuous linear bijection. It is not, however, a linear topological isomorphism, because $\mathcal S(\mathbf A^f_F)$ is a strict locally convex inductive limit of finite dimensional Euclidean spaces (in particular, a strict locally convex inductive limit of Fréchet spaces) and the transition maps are *strict inclusions*. Moreover, $\mathcal S(\mathbf A_{F,S_\infty})$ is a non-normable Fréchet space. Under such circumstances, the continuous linear bijection from the inductive to the projective tensor product is not a linear topological embedding, hence not a linear topological isomorphism. This is a consequence of [Gro-b, Ch.I,§1,No.3,Rem.1,p.47].

We further refer the reader to Remark 4.5.1.3 where a similar situation is discussed.

We further refer the reader to Remark 2.1.3.4 below, where the three main tensor topologies occurring throughout this work, are compared on $\mathcal S(\mathbf A_{F,S_\infty})\otimes\mathcal S(\mathbf A^f_F)$.

**Proof of Proposition 2.1.3.2.** Both $\mathbf A_F$ and $\mathbf A^f_F$ are Hausdorff locally compact abelian groups, and both are separable, being second-countable (see Lemma ??). As such, [Bru, §9,Prop.11] applies and gives that $\mathcal S(\mathbf A_F)$ and $\mathcal S(\mathbf A^f_F)$ are Hausdorff, complete, nuclear and Montel with their strong duals satisfying the same properties.

We now provide a direct argument.

The locally convex complex topological vector space $\mathcal S(\mathbf A^f_F)$ is a strict inductive limit of finite dimensional $\mathbf C$-vector spaces (each endowed with its unique linear topology compatible with the Euclidean topology on the complex numbers).

Indeed, since $\mathbf A^f_F$ is the filtered union compact open subgroups of the form $K_v=\prod_{v\in\Sigma_{F,f}}H_v$, with $H_v\subset F_v$ compact open and $H_v=\mathcal O_{F_v}$ for all but finitely may places $v\in\Sigma_{F,f}$, $\mathcal S(\mathbf A^f_F)$ is the locally convex inductive limit of the finite dimensional complex vector spaces $\mathcal S(K'_v/K_v)$, as $(K_v,K'_v)$ varies across pairs of compact open subgroups in $\mathbf A^f_F$ with $K_v\subset K'_v$. The set of such pairs contains a cofinal filtered subset that is countable, since $\mathbf A^f_F$ is second-countable.

It follows that $\mathcal S(\mathbf A^f_F)$ carries the finest locally convex topology, and Proposition C.2.5.1(6) describes its properties. Alternatively, see Proposition 2.1.2.8 applied to $G_2=\mathbf A^f_F$.

By Proposition 2.1.2.8(6), $\mathcal S(\mathbf A^f_F)'_\beta$ is a nuclear Fréchet space, hence Montel: by [Tre, Part III,Ch.50,Prop.50.2(5.12)], it is semi-Montel, as per [Jar, Part II,Ch.11,§11.5,p.230], and since it is barrelled, it is Montel (see [Tre, Part III,Ch.50,Cor.3,p.520]). This finishes the proof of (1) for $\mathcal S(\mathbf A^f_F)$.

We call $\{V_m\}_{m\ge 0}$ a choice of sequence of finite dimensional $\mathbf C$-linear spaces, with $\alpha_m:V_m\to V_{m+1}$ the injective $\mathbf C$-linear transition operators, such that $\varinjlim_{m\ge 0}(V_m,\alpha_m)=\mathcal S(\mathbf A^f_F)$.

The induced $\mathbf C$-linear operators between inductive tensor products

(2.1.3.3)

$$
\alpha_{\mathcal{S},m}:\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m\to\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_{m+1}
$$

are injective, since $\mathcal S(\mathbf A_{F,S_\infty})$ is a $\mathbf C$-linear space and the $\mathbf C$-linear spaces underlying the tensor products are algebraic tensor products, and continuous by [Jar, Part III,Ch.15,§15.2,Prop.1].

Each $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m$ is Hausdorff and complete since $\mathcal S(\mathbf A_{F,S_\infty})$ is by Proposition 2.1.1.6, and $V_m$ is finite dimensional. Moreover, each $\alpha_{\mathcal{S},m}$ is a topological embedding by [Bou-GT, Ch.I,§3.5,Prop.9], since it admits

## PDF page 70

**CHAPTER 2. ADELIC $\theta$-FUNCTIONS** · **70**

a continuous section $s_m:\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_{m+1}\to\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m$ induced by any choice of $\mathbf C$-linear section to the injective $\mathbf C$-linear map $\alpha_m$. Alternatively, since $\alpha_m(V_m)$ is complemented in $V_{m+1}$, $\alpha_{\mathcal{S},m}$ splits linearly and topologically by [Jar, Part III,Ch.15,§15.2,Prop.3(b)].

As such, the sequence $\{\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m,\alpha_{\mathcal{S},m}\}_{m\ge 0}$ is strict in the sense of [Jar, Part I,Ch.4,§4.6], and the locally convex inductive limit topology on $\varinjlim_{m\ge 0}(\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi V_m)$ is Hausdorff by [Jar, Ch.4,§4.6,Thm.1] and complete by [Jar, Ch.4,§4.6,Thm.4].

The injective continuous linear operators $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m\to\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota\mathcal S(\mathbf A^f_F)$ are topological embeddings, since the continuous linear map $V_m\to\mathcal S(\mathbf A^f_F)$ splits linearly by Proposition C.2.5.1(3), and hence so does $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m\to\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota\mathcal S(\mathbf A^f_F)$ by [Jar, Part III,Ch.15,§15.2,Prop.3(b)].

It follows that the topology induced on $\varinjlim_{m\ge 0}(\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m)$ by the canonical linear operator $\varinjlim_{m\ge 0}(\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m)\to\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota\mathcal S(\mathbf A^f_F)$ is the locally convex inductive limit topology, by Proposition C.2.3.13(2), i.e. the canonical injective linear operator $\varinjlim_{m\ge 0}(\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m)\to\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota\mathcal S(\mathbf A^f_F)$ is a linear topological embedding.

It is surjective since the linear spaces underlying the topological tensor products are the respective algebraic tensor products, and hence it is a linear topological isomorphism.

We deduce that the canonical linear operator from (2.1.3.2) is a surjective linear topological embedding, and hence $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota\mathcal S(\mathbf A^f_F)$ and $\mathcal S(\mathbf A_F)$ are Hausdorff, complete, nuclear and Montel, since $\mathcal S(\mathbf A_{F,S_\infty})$ is by Proposition 2.1.1.6, each $V_m$ is, being finite dimensional, $\mathcal S(\mathbf A_{F,S_\infty})$ is, as these properties are preserved by finite linear topological direct sums, and since they are preserved by strict inductive limits.

This proves (1) and (2): indeed, since $\mathcal S(\mathbf A_{F,S_\infty})$ is a nuclear Fréchet space, so is each $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m\simeq\mathcal S(\mathbf A_{F,S_\infty})^{\oplus N_m}$ by [Scha, Ch.III,§7,Thm.7.4], and so $\mathcal S(\mathbf A_F)$ is a strict LF-space and a strict locally convex inductive limit of nuclear Fréchet spaces. Moreover, since each $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\iota V_m$ is a reflexive Hausdorff locally convex topological $\mathbf C$-vector space, and the transition maps split linearly and topologically, Lemma C.1.6.1 applies, to give that $\mathcal S(\mathbf A_F)'_\beta$ is a countable projective limit of Hausdorff complete nuclear locally convex topological $\mathbf C$-vector spaces, and hence Hausdorff, complete (see [Scha, Ch.II,§5,5.3,p.52]), nuclear (see [Scha, Ch.III,§7,Corollary,p.103]) and hence Montel (by [Scha, Ch.III,§7,Cor.2,p.101]).

We deduce that $\mathcal S(\mathbf A^f_F)$ is isomorphic, as a complex vector space, to the $\mathbf C$-linear subspace of those continuous functions that are finite linear combinations of functions of the form $\prod_{v\in\Sigma_{F,f}}1_{K_v}$, where $K_v\subset F_v$ is a compact subset, with $K_v=\mathcal O_{F_v}$ for all but finitely many $v\in\Sigma_{F,f}$, and (3) follows from (2). $\square$

**Remark 2.1.3.4** (Comparison of the main tensor topologies). Upon endowing the algebraic tensor product $\mathcal S(\mathbf A_{F,S_\infty})\otimes\mathcal S(\mathbf A^f_F)$ with the injective tensor product topology (see [Tre, Ch.43], [Gro-b, Ch.I], [Scha, Ch.III,§5] and [Scha, Ch.II,§6], and particularly [Gro-b, Ch.I,§3,n.3,p.89,Def.5]), the linear map

$$
\mathcal S(\mathbf A_{F,S_\infty})\otimes_\varepsilon\mathcal S(\mathbf A^f_F)\to\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\mathcal S(\mathbf A^f_F)
$$

induced by [Jar, Part III,§16.1,Prop.3] is a linear topological isomorphism since, by nuclearity of $\mathcal S(\mathbf A^f_F)$, the injective and projective tensor product topologies on $\mathcal S(\mathbf A_{F,S_\infty})\otimes\mathcal S(\mathbf A^f_F)$ coincide (see [Gro-b, Ch.I,§5,Prop.35]).

In light of Remark 2.1.3.3, the inductive tensor topology on $\mathcal S(\mathbf A_{F,S_\infty})\otimes\mathcal S(\mathbf A^f_F)$ is strictly finer than the injective and projective topologies, while the latter two are the same.

**Remark 2.1.3.5.** We note that Schwartz-Bruhat functions of the form $f=\bigotimes_v f_v$, with $f_v\in\mathcal S(F_v)$ for *every* place $v$ of $F$, and $f_v=\mathrm{1}_{\mathcal O_{F_v}}$ for all but finitely many finite places of $F$, linearly generate a dense (and even sequentially dense) linear subspace of $\mathcal S(\mathbf A_F)$ (for instance, from [Tre, Thm.51.6,(51.3)]).

They are linear generators of $\mathcal S(\mathbf A_F)$ only for $F$ having a single Archimedean place: $\mathbf Q$ and imaginary quadratic fields.

**2.1.4. Inductive structure of $\mathcal S(\mathbf A_F)$.** We present here a structural result on $\mathcal S(\mathbf A_F)$, exhibiting $\mathcal S(\mathbf A_F)$ as a locally convex inductive limit of the $S$-adelic Schwartz-Bruhat spaces $\mathcal S(\mathbf A_{F,S})$.

## PDF page 71

**2.1. SCHWARTZ-BRUHAT FUNCTIONS** · **71**

PROPOSITION 2.1.4.1. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all of the Archimedean places. We denote by $S_f$ the subset of $S$ of all the finite places of $F$ contained in $S$. Then:*

(1) *The canonical linear map:*

$$
\mathcal{S}(\mathbf{A}_{F,S_\infty}) \otimes_\iota \bigotimes_{v\in S_f} \mathcal{S}(F_v) \to \mathcal{S}(\mathbf{A}_{F,S}) \tag{2.1.4.1}
$$

*the topological tensor product being inductive, is a linear topological isomorphism, whose formation is compatible, in the sense of (2.1.4.2) below, with extensions $S\subset S'$ of the finite set of places $S$ of $F$.*

(2) *$\mathcal{S}(\mathbf{A}_{F,S})$ is a strict locally convex inductive limit of nuclear Fréchet spaces, and hence a strict LF-space. It is Hausdorff, complete, nuclear and Montel, and its strong dual satisfies the same properties.*

(3) *If $S'$ is another finite set of places of $F$, with $S\subset S'$, then the canonical linear map:*

$$
\pi_{S,S'} : \mathcal{S}(\mathbf{A}_{F,S}) \to \mathcal{S}(\mathbf{A}_{F,S'}) \tag{2.1.4.2}
$$

*defined by the assignment:*

$$
\pi_{S,S'}(f) := f\otimes (\prod_{v\in S'_f-S_f} 1_{\mathcal{O}_{F_v}}) \tag{2.1.4.3}
$$

*is continuous, injective, and induces on $\mathcal{S}(\mathbf{A}_{F,S})$ its intrinsic Hausdorff locally convex topology as the pre-image of the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{A}_{F,S'})$.*

(4) *The maps $\pi_{S,S'}$ from (2.1.4.2) are topological embeddings.*

(5) *The canonical linear map:*

$$
\pi : \operatorname*{\mathrm{colim}}_{S\subset\Sigma_F} \mathcal{S}(\mathbf{A}_{F,S}) \to \mathcal{S}(\mathbf{A}_F) \tag{2.1.4.4}
$$

*induced by the maps:*

$$
\pi_S : \mathcal{S}(\mathbf{A}_{F,S}) \to \mathcal{S}(\mathbf{A}_F) \tag{2.1.4.5}
$$

*each defined by $\pi_S(f) := f\otimes 1_K$ where $K\subset \widehat{\prod}_{v\notin S}(F_v,\mathcal{O}_{F_v})$ is the compact subset $\prod_{v\notin S}\mathcal{O}_{F_v}$, is a linear topological isomorphism, upon endowing the inductive limit with its locally convex inductive limit topology.*

PROOF. (1) and (2) : Since each $\mathcal{S}(F_v)$, for $v$ any finite place of $F$, is the locally convex inductive limit of finite dimensional $\mathbf{C}$-vector spaces with injective $\mathbf{C}$-linear transition maps, so is the tensor product $\bigotimes_{v\in S_f}\mathcal{S}(F_v)$, since the tensor product of finitely many injective $\mathbf{C}$-linear maps between finite dimensional $\mathbf{C}$-vector spaces is an injective $\mathbf{C}$-linear map between finite dimensional $\mathbf{C}$-vector spaces, and a $\mathbf{C}$-linear subspace of a finite dimensional $\mathbf{C}$-vector space, endowed with the Euclidean topology, always inherits the subspace topology, and as such it is closed.

By Proposition 2.1.2.4 and Lemma C.2.5.2, $\bigotimes_{v\in S_f}\mathcal{S}(F_v)$ is indeed the locally convex inductive limit of a sequence of finite dimensional $\mathbf{C}$-vector spaces with injective $\mathbf{C}$-linear transition maps. It is nuclear by [Jar, Part III,Ch.21,§21.2,Cor.3] and the leftmost side in (2.1.4.1) is itself the locally convex inductive limit of a sequence of Hausdorff locally convex topological complex vector spaces of the form $\mathcal{S}(\mathbf{A}_{F,S_\infty})^{\oplus N}$ for varying integers $N\ge 1$, with injective transition maps, each a topological embedding by [Jar, Part II,Ch.16,§15.2,Cor.2(b),p.348] (using nuclearity of $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ to identify injective and projective tensor topologies, together with Corollary C.2.3.12, using that $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ is a Fréchet space, as is any finite dimensional $\mathbf{C}$-vector space).

By [Scha, Ch.II,§6,6.6], $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota\bigotimes_{v\in S_f}\mathcal{S}(F_v)$ (and by Proposition C.2.3.13(2)) is Hausdorff and complete, and by [Jar, Part III,Ch.21,§21.2,Cor.3], it is nuclear (being a countable locally convex inductive limit of nuclear Fréchet spaces). By [Jar, Part II,Ch.11,§11.5,Prop.4(e)], it is Montel.

The linear map in (2.1.4.1) is a continuous bijection.

## PDF page 72

**72** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

We consider the closed subspace

$$
\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota V \subset \mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota \bigotimes_{v\in S_f}\mathcal{S}(F_v) \tag{2.1.4.6}
$$

for $V\subset\bigotimes_{v\in S_f}\mathcal{S}(F_v)$ a finite dimensional $\mathbf{C}$-vector subspace.

The inductive tensor product $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota V$ is a Fréchet space, and the composition of the linear topological embedding in (2.1.4.6) followed by the continuous linear operator from (2.1.4.1), is continuous, injective, and its image is a $\mathbf{C}$-linear subspace $W$ of $\mathcal{S}(\mathbf{A}_{F,S})$ spanned by the Schwartz-Bruhat functions of the form $f_\infty\otimes\bigotimes_{v\in S_f}1_{K_{v,i_v}}$ for $f_\infty\in\mathcal{S}(\mathbf{A}_{F,S_\infty})$ and $K_{v,i_v}\subset F_v$ are finitely many compact subsets. $W$ is therefore closed and metrizable, since $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ is a Fréchet space by Proposition 2.1.1.6.

By [NB, Thm.14.4.5], the restriction of the continuous linear operator from (2.1.4.1) to $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota V$ is therefore a linear topological embedding. Since the topologies on $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota\bigotimes_{v\in S_f}\mathcal{S}(F_v)$ and $\mathcal{S}(\mathbf{A}_{F,S})$ are locally convex strict inductive limits of the topologies on subspaces of the form $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes V$ and $W$, compatibly with the continuous linear operator from (2.1.4.1) (see Proposition C.2.3.13(2)), then such operator is a linear topological embedding, hence a linear topological isomorphism.

We deduce that $\mathcal{S}(\mathbf{A}_{F,S})$ is Hausdorff, complete, nuclear and Montel, since $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota\bigotimes_{v\in S_f}\mathcal{S}(F_v)$ is.

Since $\mathcal{S}(\mathbf{A}_{F,S})$ is Montel, then the strong dual $\mathcal{S}(\mathbf{A}_{F,S})'_\beta$ is Hausdorff and Montel by [Scha, Ch.IV,§5,5.9] (see also [MV, Part IV,Ch.24,Thm.24.25,p.286]). It is complete by [Scha, Ch.IV,§6,6.1]. Since $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ is a strict inductive limit of nuclear Fréchet spaces (of the form $\mathcal{S}(\mathbf{A}_{F,S_\infty})^{\oplus N}$ for integers $N\ge 1$) with topologically split transition maps, its strong dual is a projective limit (see Lemma C.1.6.1) of nuclear spaces, hence nuclear by [Gro-b, Ch.II,Thm.9].

Compatibility of the linear topological isomorphism in (2.1.4.1) with enlargement of the finite set of places $S$ is a consequence of the construction.

This proves (1) and (2), noting that $\mathcal{S}(\mathbf{A}_{F,S})$ is a strict locally convex inductive limit of subspaces of the form $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota V \simeq \mathcal{S}(\mathbf{A}_{F,S_\infty})^{\oplus N_V}$ for a finite dimensional $\mathbf{C}$-vector space $V$ ($N_V$ being the dimension of $V$), and each is therefore nuclear and Fréchet by [Scha, Ch.III,§7,Thm.7.4].

(3) follows from (1).

(4) : By (3), the inductive system $\{\mathcal{S}(\mathbf{A}_{F,S})\}$ is strict.

(5) : The linear operator in (2.1.4.4) is a continuous bijection as a consequence of the definition of Schwartz-Bruhat functions on $\mathbf{A}_F$. Since each $\pi_S$ is a linear topological embedding, then $\pi$ is a linear topological isomorphism since by (4) the inductive system $\{\mathcal{S}(\mathbf{A}_{F,S})\}_{S\subset\Sigma_F}$ is strict. □

COROLLARY 2.1.4.2. *Let $F$ be a number field, $S,S'$ finite sets of places of $F$ containing all Archimedean places, with $S\subset S'$. The canonical linear maps:*

$$
\mathcal{S}(\mathbf{A}_{F,S})\otimes_\iota \mathcal{S}(G) \to \mathcal{S}(\mathbf{A}_F),\ \mathcal{S}(\mathbf{A}_{F,S})\otimes_\iota \mathcal{S}(\prod_{v\in S'-S}F_v) \to \mathcal{S}(\mathbf{A}_{F,S'}) \tag{2.1.4.7}
$$

*with $G := \widehat{\prod}_{v\notin S}(F_v,\mathcal{O}_{F_v})$, are linear topological isomorphisms. In particular, both inductive tensor products are complete.*

PROOF. In light of Proposition 2.1.4.1(1) and Proposition 2.1.3.2(2), it is enough to show that the canonical linear map:

$$
\bigotimes_{v\in S_f}\mathcal{S}(F_v)\otimes_\iota \mathcal{S}(G) \to \mathcal{S}(\mathbf{A}_F^f) \tag{2.1.4.8}
$$

the topological tensor product on the left side of (2.1.4.8) being inductive, is a linear topological isomorphism. Since it is a bijection, then Proposition C.2.5.1 implies it is a linear topological isomorphism. Alternatively, this holds as a consequence of Lemma D.1.8.1.

Similarly, the second operator in (2.1.4.7) is also a linear topological isomorphism. □

## PDF page 73

**2.1. SCHWARTZ-BRUHAT FUNCTIONS** · **73**

LEMMA 2.1.4.3. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Then:*

(1) *There exists a continuous linear map*

$$
\Pi_S : \mathcal{S}(\mathbf{A}_F) \to \mathcal{S}(\mathbf{A}_F) \tag{2.1.4.9}
$$

*whose image is $\pi_S(\mathcal{S}(\mathbf{A}_{F,S}))$ and is the identity on $\pi_S(\mathcal{S}(\mathbf{A}_{F,S}))$, for $\pi_S$ as in (2.1.4.5), and satisfies $\Pi_S^2 = \Pi_S$. In particular, the operator $\pi$ from (2.1.4.4) has topologically complemented image.*

(2) *For any finite set $S'$ of places of $F$ containing $S$, the continuous linear map*

$$
\Pi'_{S,S'} : \mathcal{S}(\mathbf{A}_{F,S'}) \to \mathcal{S}(\mathbf{A}_F) \tag{2.1.4.10}
$$

*defined as*

$$
\Pi'_{S,S'} := \Pi_S\circ \pi_{S'} \tag{2.1.4.11}
$$

*whose image is $\pi_S(\mathcal{S}(\mathbf{A}_{F,S}))$, factors through a continuous linear map*

$$
\Pi_{S,S'} : \mathcal{S}(\mathbf{A}_{F,S'}) \to \mathcal{S}(\mathbf{A}_{F,S'}) \tag{2.1.4.12}
$$

*whose image is $\pi_{S,S'}(\mathcal{S}(\mathbf{A}_{F,S}))$, satisfying $\Pi_{S,S'}^2 = \Pi_{S,S'}$.*

*In particular, the map $\pi_{S,S'}$ from (2.1.4.3) has linearly and topologically complemented image.*

(3) *For two finite sets $S',S''$ of places of $F$ such that $S\subset S'\subset S''$, we have:*

$$
\Pi_{S,S'} = \Pi_{S,S''}\circ \pi_{S',S''} \tag{2.1.4.13}
$$

*where $\pi_{S,S'}$ is as in (2.1.4.2).*

PROOF. (1) : We have

$$
\pi_S(\mathcal{S}(\mathbf{A}_{F,S})) = \mathcal{S}(\mathbf{A}_{F,S})\otimes 1_K
$$

where $K\subset \widehat{\prod}_{v\notin S}(F_v,\mathcal{O}_{F_v})$ is the compact open subset $\prod_{v\notin S}\mathcal{O}_{F_v}$ and $1_K$ is its indicator function.

For $G := \widehat{\prod}_{v\notin S}(F_v,\mathcal{O}_{F_v})$, its Schwartz-Bruhat space $\mathcal{S}(G)$ is Hausdorff locally convex as a topological $\mathbf{C}$-vector space, and the line spanned by $1_K$ is complemented by the Hahn-Banach Theorem. Indeed, for the functional $\mathbf{C}\cdot 1_K\to\mathbf{C}$ defined as $\varphi : c1_K\mapsto c$, there exists a continuous extension $\widetilde{\varphi} : \mathcal{S}(G)\to\mathbf{C}$ by [NB, Cor.7.3.3], satisfying $\widetilde{\varphi}|_{\mathbf{C}\cdot 1_K} = \varphi$. We define

$$
\Pi(f) := \widetilde{\varphi}(f)1_K
$$

to obtain a continuous operator $\Pi : \mathcal{S}(G)\to\mathcal{S}(G)$ such that $\Pi^2 = \Pi$ and the image of $\Pi$ is $\mathbf{C}\cdot 1_K$.

We now define:

$$
\Pi'_S := \mathrm{id}_{\mathcal{S}(\mathbf{A}_{F,S})}\otimes\Pi : \mathcal{S}(\mathbf{A}_{F,S})\otimes_\iota \mathcal{S}(G) \to \mathcal{S}(\mathbf{A}_{F,S})\otimes_\iota \mathcal{S}(G).
$$

However, since we have $\mathbf{A}_F\simeq \mathbf{A}_{F,S}\times G$, we also have, by Corollary 2.1.4.2, a linear topological isomorphism $\mathcal{S}(\mathbf{A}_F)\simeq \mathcal{S}(\mathbf{A}_{F,S})\otimes_\iota \mathcal{S}(G)$, where the target is already complete since it is the strict inductive limit of a sequence of complete Hausdorff locally convex spaces, as $\mathcal{S}(G)$ is the strict inductive limit of a sequence of finite dimensional $\mathbf{C}$-vector spaces.

The continuous linear operator $\Pi'_S$ therefore induces a unique continuous linear operator $\Pi_S : \mathcal{S}(\mathbf{A}_F)\to \mathcal{S}(\mathbf{A}_F)$ satisfying $\Pi_S^2 = \Pi_S$. Its image is the image under the linear topological isomorphism $\mathcal{S}(\mathbf{A}_{F,S})\otimes_{\pi}\mathcal{S}(G)$, of the subspace $\mathcal{S}(\mathbf{A}_{F,S})\otimes\mathbf{C}\cdot 1_K$, which is $\pi_S(\mathcal{S}(\mathbf{A}_{F,S}))$. Moreover, by design of $\Pi'_S$, we have, for every $f\in\pi_S(\mathcal{S}(\mathbf{A}_{F,S}))$, i.e. $f = f_0\otimes 1_K$ for unique $f_0\in\mathcal{S}(\mathbf{A}_{F,S})$:

$$
(\Pi_S\circ\pi_S)(f) = \Pi_S(f_0\otimes 1_K) = (\mathrm{id}_{\mathcal{S}(\mathbf{A}_{F,S})}(f_0)\otimes\Pi(1_K)) = f_0\otimes 1_K = f.
$$

(2) and (3) follow from (1) and the identity $\pi_{S''}\circ\pi_{S',S''} = \pi_{S'}$ as continuous linear operators $\mathcal{S}(\mathbf{A}_{F,S'})\to \mathcal{S}(\mathbf{A}_F)$. □

## PDF page 74

**74** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

For $E$ a Hausdorff locally convex $\mathbf{C}$-vector space, we denote by $\mathscr{L}(E) := \mathscr{L}(E,E)$ the $\mathbf{C}$-linear space of continuous linear endomorphisms of $E$, and write $\mathscr{L}_\beta(E)$ for $\mathscr{L}(E,E)$ endowed with the topology of uniform convergence on all bounded subsets of $E$ (see Definition C.2.1.5).

The following Corollary will not be used throughout this work. It is however indicative of how the $S$-local Schwartz-Bruhat spaces $\mathcal{S}(\mathbf{A}_{F,S})$ encompass large pieces of the global Schwartz-Bruhat space $\mathcal{S}(\mathbf{A}_F)$, up to a closed subspace (“smaller and smaller” as $S$ grows large) that splits off linearly and topologically. This will be a general pattern to follow throughout the later Chapters of this work, where we will be analyzing large subquotients of $\mathcal{S}(\mathbf{A}_F)$ by studying their $S$-local analogs for all large enough $S$: the fact that such analysis is possible rests on properties of Hecke $L$-functions, to be harnessed through the systematic use of the Mellin transform (idelic, in the spirit of Tate’s dissertation from [CF, Ch.XV], and $S$-idelic).

COROLLARY 2.1.4.4. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places of $F$. Let:*

$$
\Pi_S : \mathcal{S}(\mathbf{A}_F) \to \pi_S(\mathcal{S}(\mathbf{A}_{F,S})) \tag{2.1.4.14}
$$

*be any continuous projection onto the linear image of $\pi_S$ from (2.1.4.5) satisfying $\Pi_S\circ\pi_S = \pi_S$. Then the net*

$$
\{\Pi_S\}_{S\subset\Sigma_F}\subset \mathscr{L}_\beta(\mathcal{S}(\mathbf{A}_F))
$$

*indexed by the finite subsets of $\Sigma_F$ containing $S_\infty$, converges to the identity on $\mathcal{S}(\mathbf{A}_F)$ with respect to the topology of uniform convergence on bounded susbsets.*

PROOF. To see this, we let $B\subset\mathcal{S}(\mathbf{A}_F)$ be a bounded subset. By Proposition 2.1.4.1(4), and by [Scha, Ch.II,§6,6.5], there exits $B_0\subset\mathcal{S}(\mathbf{A}_{F,S_0})$ bounded, for $S_0$ large enough, such that $B = \pi_{S_0}(B_0)$.

For any $S\subset\Sigma_F$ finite and containing $S_\infty$, such that $S_0\subset S$, we therefore have $\Pi_S = \mathrm{id}$ over $B$. We call $I(S_0)$ their set, and we call $I$ the set of all finite subsets $S\subset\Sigma_F$ containing $S_\infty$. $I$ is filtered by inclusion and contains $I(S_0)$ as a filtered subset.

$I(S_0)$ is cofinal in $I$, since for every $S\in I$, the set $S_0\cup S$ is in $I(S_0)$ and contains $S$. In particular, the net $I\to\mathscr{L}_\beta(\mathcal{S}(\mathbf{A}_F))$ defined as $T_i := \Pi_S$ where $S = i$ in $I$, converges to $\mathrm{id}$ uniformly over the bounded subset $B$ of $\mathcal{S}(\mathbf{A}_F)$. Indeed, this requires the existence, for every $\varepsilon > 0$, of an element $i_0\in I$ such that for every $i\ge i_0$:

$$
\sup_{b\in B} p(T_i(b)-b) < \varepsilon
$$

with $p$ varying over any fundamental family of continuous seminorms on $\mathcal{S}(\mathbf{A}_F)$. We may choose $i_0 := S_0$, and this indeed holds (for any $\varepsilon > 0$).

Note that the seminorms $p_B : \mathscr{L}(\mathcal{S}(\mathbf{A}_F))\to\mathbf{R}_{\ge 0}$, as $B$ varies over all the bounded subsets of $\mathcal{S}(\mathbf{A}_F)$, defined as $p_B(T) := \sup_{b\in B} p(T(b))$ generate the topology $\beta$ on $\mathscr{L}(\mathcal{S}(\mathbf{A}_F))$ of uniform convergence on bounded subsets (see [Scha, Ch.III,§3,p.81], as $p$ varies over any fundamental family of continuous seminorms on $\mathcal{S}(\mathbf{A}_F)$, $\mathfrak{S}$ the set of all bounded subsets of $\mathcal{S}(\mathbf{A}_{F,S})$; see also (C.2.1.4)). We have just shown that for each bounded subset $B\subset\mathcal{S}(\mathbf{A}_F)$, we have $\lim_{S\in I} p_B(\Pi_S - \mathrm{id}) = 0$.

This means $\Pi_S\to\mathrm{id}$ uniformly on the bounded subsets of $\mathcal{S}(\mathbf{A}_F)$, i.e. $\Pi_S\to\mathrm{id}$ in $\mathscr{L}_\beta(\mathcal{S}(\mathbf{A}_F))$. □

**2.2. Global adelic $\theta$-functions**

Let $F$ be a number field. In this section we will be defining and studying the linear map associating to a Schwartz-Bruhat function $f : \mathbf{A}_F\to\mathbf{C}$ its restriction to $\mathrm{GL}_1(\mathbf{A}_F)$ averaged over the continuous translation action by the discrete subgroup $F^\times$. We will show that such averages are themselves continuous as functions on the idele class group $C_F$ of $F$, and decaying rapidly at infinity in a precise sense that can be controlled using the idelic norm.

## PDF page 75

2.2.  GLOBAL ADELIC $\theta$-FUNCTIONS    75

Such $F^\times$-averaged Schwartz-Bruhat functions are called *global adelic $\theta$-functions*. We will study them systematically throughout the rest of Chapter 2, and then collect them into a topological vector space in the next Chapter.

**2.2.1.  Averaging over a full lattice.** In this subsection we record a convergence result concerning averages of norm functions on Euclidean spaces under the translation action by a full lattice.

Let $N\ge 1$ be an integer and consider $\Gamma\subset\mathbf R^N$ a discrete subgroup. If $\Gamma$ is co-compact, then $\Gamma$ is a finite free abelian group of rank $N$, i.e. a full lattice.

We denote by $\lVert\cdot\rVert_\infty\colon\mathbf R^N\to\mathbf R_{\ge 0}$ the norm $\lVert x\rVert_\infty:=\max\{|x_i|_{\mathbf R},1\le i\le N\}$.

LEMMA 2.2.1.1. *Let $N\ge 1$. Let $\Gamma\subset\mathbf R^N$ be a full lattice. For every real number $r\ge 1$, the set*

$$
X_r:=\{x\in\mathbf R^N:\lVert\xi\rVert_\infty\in[r,r+1)\}\subset\mathbf R^N \tag{2.2.1.1}
$$

*is bounded, Lebesgue measurable, and it satisfies:*

$$
\lvert\Gamma\cap X_r\rvert=O_{\Gamma,N}(r^{N-1}) \tag{2.2.1.2}
$$

*as $r\to+\infty$, the implied constant depending $N$ and on $\Gamma$.*

REMARK 2.2.1.2. We note that the implied constant in (2.2.1.2) depends on $N$ on itself, and also on $N$ through $\Gamma$, through its successive minima: for a full lattice $\Gamma\subset\mathbf R^N$, the successive minima $r_1,\dots,r_N$ are defined as, for each integer $1\le k\le N$, the infimum over all real numbers $r\ge 0$ such that $B_0(r)\cap\Gamma$ contains $k$ vectors which are $\mathbf R$-linearly independent (the closed ball $B_0(r)$ of radius $r>0$ and center the origin $0\in\mathbf R^N$ being defined using the standard Euclidean norm); see [Schm, §2,p.347].

The method to estimate the error term for $\lvert\Gamma\cap X_r\rvert-\frac{\mathrm{vol}(X_r)}{\mathrm{vol}(\mathbf R^N/\Gamma)}$, where volumes are computed in $\mathbf R^N$ with respect to the Lebesgue measure, normalized so as to give the hypercube $[0,1)^N$ volume 1, follows [Schm, Lemma 1,p.347] and springs from the proof of [Davenport-1, §2,Thm.p.180].

PROOF. We denote, for every real number $r\ge 1$, by $X_r\subset\mathbf R^N$ the subset $X_r:=\{x\in\mathbf R^N:\lVert x\rVert_\infty\in[r,r+1)\}$. Since $\lVert\cdot\rVert_\infty\colon\mathbf R^N\to\mathbf R_{\ge 0}$ is continuous, surjective and proper, and $X_r$ is the pre-image of the bounded interval $[r,r+1)$, we deduce that $X_r$ is measurable and relatively compact, and so is its image under the orthogonal projection onto any linear subspace of $\mathbf R^N$. Indeed, such image is a convex polyhedron within such subspace.

Let $L\subset\mathbf R^N$ be a line. Then $L\cap X_r$ is either empty or the union of at most two segments. Indeed, for $x,y\in\mathbf R^N$ and such that $L=x+\mathbf R\cdot y$, we have

$$
x+ty\in X_r
$$

if and only if

$$
f(t):=\sup_{1\le k\le N}|x_k+ty_k|\in[r,r+1).
$$

Note that $y$ is necessarily nonzero.

The function $f\colon\mathbf R\to\mathbf R_{\ge 0}$ is continuous, surjective and proper. Moreover, its fibre over $r\in\mathbf R_{\ge 0}$ is the pre-image under the map $t\mapsto x+ty$, of the intersection of the closed surface $S_r:=\{\lVert x\rVert_\infty=r\}$, the boundary of the $N$-dimensional hypercube in $\mathbf R^N$ with edge-length $r$, with $L$. The fibres of $f$ are therefore finite of size at most 2, since the interior of $S_r$ is convex.

The subset $X_r$ is obtained from the interior of $S_{r+1}$ by removing the interior of $S_r$, and so the intersection of $L$ with the interior of $S_{r+1}$, which, by the foregoing, is either a point of a segment, intersects $X_r$ in the complement of the intersection of $L$ with the interior of $S_r$, again a point of a segment. This shows that $L\cap X_r$ is either empty, a segment or two segments.

It follows that [Schm, Lemma 1,p.347] (see also [Gao, p.15]) applies. Indeed, $X_r$ is of class 2, following the terminology of loc.cit., and for $\lambda_1,\dots,\lambda_N$ the successive minima of $\Gamma$ (for each $k\ge 1$, each $\lambda_k$ is the

## PDF page 76

76    CHAPTER 2.  ADELIC $\theta$-FUNCTIONS

infimum among all positive real numbers $\lambda$ such that $\Gamma$ contains $k$ linearly independent vectors in $\mathbf R^N$ of Euclidean norm at most $\lambda$) we have $\lambda_{N-1}\le r$ for all large enough $r>0$, since $\lambda_N$ does not depend on $r$.

Then we have:

$$
\left\lvert\lvert\Gamma\cap X_r\rvert-\frac{\mathrm{vol}(X_r)}{\mathrm{vol}(\mathbf R^N/\Gamma)}\right\rvert\le\left(1+\frac{2}{\sqrt{3}}3^N N\right)^N\max_{1\le k\le N-1}\frac{r^k}{\prod_{1\le i\le k}\lambda_k},
$$

where $\mathrm{vol}(X_r)=(2(r+1))^N-(2r)^N=2^N Nr^{N-1}+O_N(r^{N-2})$ as $r\to+\infty$.

We deduce that (2.2.1.2) holds, the implied constant depending on $N$ and on $\Gamma$ both through its co-volume and through its successive minima. $\square$

We need the following convergence result:

PROPOSITION 2.2.1.3. *Let $N\ge 1$ be an integer, $\Gamma\subset\mathbf R^N$ a full lattice. Let $\lVert\cdot\rVert\colon\mathbf R^N\to\mathbf R_{\ge 0}$ be a norm on $\mathbf R^N$ inducing the Euclidean topology. Let $K\subset\mathbf R^N$ be a fixed arbitrary compact subset. Let $\sigma>0$ be a real number.*

*Then the series*

$$
\sum_{\xi\in\Gamma-\Gamma\cap K}\lVert\xi+x\rVert^{-\sigma} \tag{2.2.1.3}
$$

*converges for $\sigma>N$, uniformly with respect to $x$ varying over $K$, and, for every $\varepsilon>0$, uniformly for $(\sigma,x)\in[N+\varepsilon,+\infty)\times K$.*

PROOF. There exists a real number $C>0$ such that $\lVert\cdot\rVert_\infty\le C\lVert\cdot\rVert$ as real-valued continuous functions on $\mathbf R^N$.

We therefore have the inequality

$$
\sum_{\xi\in\Gamma-\Gamma\cap K}\lVert\xi+x\rVert^{-\sigma}\le\frac{1}{C^\sigma}\sum_{\xi\in\Gamma-\Gamma\cap K}\lVert\xi+x\rVert_\infty^{-\sigma}. \tag{2.2.1.4}
$$

We now call

$$
Z_m:=\{(\xi,x)\in(\Gamma-\Gamma\cap K)\times K:\lVert\xi+x\rVert_\infty\in[m,m+1)\}\subset(\Gamma-\Gamma\cap K)\times K \tag{2.2.1.5}
$$

for $m\in\mathbf N$.

For each $x\in K$, we denote $Z_{m,x}\subset Z_m$ the fibre of $Z_m\to K$ over $\{x\}$. Since, for each $x\in\mathbf R^N$ fixed, $\{y\in\mathbf R^N:\lVert x+y\rVert_\infty\in[m,m+1)\}$ is relatively compact and $\Gamma\subset\mathbf R^N$ is discrete, the fibre $Z_{m,x}$ is finite.

We note that $Z_{m,0}$ is non-empty.

We have $|Z_{m,0}|\ll m^{N-1}$ by Lemma 2.2.1.1. For $x\in K$ fixed, upon combining $|\lVert\xi\rVert_\infty-\lVert x\rVert_\infty|\le\lVert\xi+x\rVert_\infty$ and $\lVert x+\xi\rVert_\infty\le\lVert x\rVert_\infty+\lVert\xi\rVert_\infty$, we deduced that if $(\xi,x)\in Z_{m,x}$ is fixed, then we have

$$
\lVert\xi\rVert_\infty\in[m-\lVert x\rVert_\infty,m+\lVert x\rVert_\infty+1).
$$

For $m(x)$ the least nonnegative integer such that $\lVert x\rVert_\infty\le m(x)$, we have

$$
\xi\in\bigcup_{m-m(x)\le k\le m+m(x)}Z_{k,0}
$$

and hence

$$
|Z_{m,x}|\ll_{x,N}\sum_{1,m-m(x)\le k\le m+m(x)}k^{N-1}\ll_{x,N}(m+m(x))^{N-1}.
$$

Since $K$ is compact, there exists an integer $m(K)\ge 0$ such that $m(x)\le m(K)$ for every $x\in K$.

It follows that we have

$$
|Z_{m,x}|\ll_{K,N}(m+m(K))^{N-1}\ll_{K,N}m^{N-1}
$$

the implied constant depending only on $N$ and $K$.

## PDF page 77

2.2.  GLOBAL ADELIC $\theta$-FUNCTIONS    77

We have

$$
\sum_{\xi\in\Gamma-\Gamma\cap K}\lVert\xi+x\rVert_\infty^{-\sigma}\ll_{K,N}\sum_{m\ge 1}m^{N-1-\sigma}
$$

and hence the series in (2.2.1.3) is absolutely convergent, uniformly with respect to $x\in K$, for each $\sigma>N$, and the convergence is uniform for $(\sigma,x)\in[N+\varepsilon,+\infty)\times K$ for every $\varepsilon>0$. $\square$

**2.2.2.  Averaging over $\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$ under $(F^\times\times F)$-translation.** For $F$ a number field and $f\in\mathcal S(\mathbf A_F)$ a Schwartz-Bruhat function on the adeles of $F$, we can restrict $f$ to $\mathrm{GL}_1(\mathbf A_F)$, i.e. consider the pre-composition of $f$ with the continuous identity map $\mathrm{GL}_1(\mathbf A_F)\to\mathbf A_F^\times$, with $\mathbf A_F^\times$ endowed with the adelic topology, followed by the topological embedding $\mathbf A_F^\times\subset\mathbf A_F$.

Such restriction is a continuous map $\mathrm{GL}_1(\mathbf A_F)\to\mathbf C$, and the continuous left-translation action by the discrete subgroup $F^\times\subset\mathrm{GL}_1(\mathbf A_F)$ leads to the formation of the average of $f$ along each $F^\times$-orbit in $\mathrm{GL}_1(\mathbf A_F)$, thought of as a function on $C_F$.

2.2.2.1. *The main convergence Lemma.* The following Lemma establishes basic properties of such averages and their formation. A large part of the materials covered in this subsection is discussed in a similar form also in [RV, Ch.7,§7.2,Lemma 7.6].

We denote by

$$
\tau\colon\mathbf R_{>0}\to\mathrm{GL}_1(\mathbf A_{F,S_\infty})
$$

a choice of continuous homomorphic section to the continuous group homomorphism $|\cdot|_\infty:=\prod_{v\in S_\infty}|\cdot|_v$ and call

$$
T_\infty:=\tau(\mathbf R_{>0}).
$$

We further call $E_\infty$ the image under the continuous homomorphism $\mathrm{GL}_1(\mathbf A_F)\to\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ of the idelic fundamental domain $E_F^1$ from (A.2.3.14), which is, in turn, the finite union of $E_0\times\widehat{\mathcal O}_F^\times$ and of its $g_i$-translates, for $\{g_i\}_{1\le i\le h_F}$ a finite set of representatives in $\mathrm{GL}_1(\mathbf A_F)^1$ of the $h_F$ ideal classes in $\mathrm{Pic}(\mathcal O_F)$. Therefore, $E_\infty$ is, concretely, the finite union of $E_0$ and the $g_{i,\infty}$-translates of $E_0$ within $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$, where $g_{i,\infty}$ is the image of $g_i$ into $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ for each $1\le i\le h_F$.

By Lemma A.2.3.11, $T_\infty\subset\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ is a closed (Lie) subgroup, and by Lemma A.2.3.10, $E_\infty$ is relatively compact.

LEMMA 2.2.2.1 (Averaging over $F^\times$-orbits). *Let $F$ be a number field. We let $f\in\mathcal S(\mathbf A_F)$ be a Schwartz-Bruhat function over $\mathbf A_F$. Then the following series:*

$$
\Psi_F(f)(g,x):=\sum_{\xi\in F^\times}f(g(\xi+x)),\quad (g,x)\in\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F \tag{2.2.2.1}
$$

*converges absolutely and uniformly over the compact subsets of $\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$. As a function of $(g,x)\in\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$, this satisfies the following conditions:*

*(1) $\Psi_F(f)(g,x)$ is a continuous function of $(g,x)\in\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$, and the function*

$$
\Psi_F(f)(g,x)+f(gx)
$$

*(adding in the term $f(gx)$ for $\xi=0$) is, as a function of $(g,x)$, invariant under the left translation action of $1\times F\subset\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$.*

*(2) $\Psi_F(f)(g,0)$ is a continuous function of $g\in\mathrm{GL}_1(\mathbf A_F)$, invariant under the left translation action of $F^\times\subset\mathrm{GL}_1(\mathbf A_F)$.*

*(3) If $f\in\mathcal S(\mathbf A_F)$ has the special form*

$$
f=f_\infty\prod_{v\in\Sigma_{F,f}}f_v \tag{2.2.2.2}
$$

## PDF page 78

78    CHAPTER 2.  ADELIC $\theta$-FUNCTIONS

*where $f_\infty\in\mathcal S(\mathbf A_{F,S_\infty})$ and $f_v=1_{K_v}$ for $K_v\subset\mathcal O_{F_v}$ a compact open subset for all finite places $v$ of $F$, with $K_v=\mathcal O_{F_v}$ for all but finitely many finite places $v$ of $F$, then there exists a fractional ideal $I_f\subset F$ such that*

$$
\sum_{\xi\in F^\times}|f(\xi g)|\le\sum_{\xi\in I_f-\{0\}}|f_\infty(\xi g_\infty)| \tag{2.2.2.3}
$$

*where $g_\infty\in\mathrm{GL}_1(\mathbf A_{F,S_\infty})$, the image of $g$ under the projection $\mathrm{GL}_1(\mathbf A_F)\to\mathrm{GL}_1(\mathbf A_{F,S_\infty})$, is allowed to vary over the subset $T_\infty\cdot E_\infty\subset\mathrm{GL}_1(\mathbf A_{F,S_\infty})$.*

REMARK 2.2.2.2. We note that no constraint on $(g,x)$ is assumed in Lemma 2.2.2.1(1),(2), whereas $g_\infty$ in (3) is assumed to be constrained to vary over $T_\infty\cdot E_\infty$. The assertions in (1) and (2) are local in nature and can be checked by reducing to the case of $f$ as in (3), leveraging (2.2.2.3) over $T_\infty\cdot E_\infty$, insofar as checking the relevant assertions over general compact subsets of $\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$ can be reduced to the case of the single class of compact subsets $(K\cdot\overline{E}_F^1)\times\overline{D}_F$, where $E_F^1$ is the idelic fundamental domain from (A.2.3.14), $D_F$ is the adelic fundamental domain from (A.2.1.2), and $K$ varies over the compact subsets of $T:=s_F(\mathbf R_{>0})$, where $s_F$ is the canonical section to the idelic norm (see (A.2.2.9)).

We refer the reader to the details within the argument below.

PROOF. We write $f$ as a finite $\mathbf C$-linear combination

$$
f=\sum_{k=1}^m c_k f_k
$$

where each $f_k$ is of the form

$$
f_k(x)=f_\infty(x_\infty)\prod_{v\in\Sigma_{F,f}}1_{K_v}(x_v),\;x=(x_\infty,(x_v)_{v\in\Sigma_{F,f}})\in\mathbf A_F \tag{2.2.2.4}
$$

with $f_\infty\in\mathcal S(\mathbf A_{F,S_\infty})$, where $x_\infty=(x_v)_{v\in S_\infty}\in\prod_{v\in S_\infty}F_v\simeq\mathbf A_{F,S_\infty}$, with $K_v\subset F_v$ a compact subset for all finite places $v$ of $F$ and $K_v=\mathcal O_{F_v}$ for all but finitely many finite places $v$ (since finite $\mathbf C$-linear combinations of the functions of the form in (2.2.2.4) span $\mathcal S(\mathbf A_F)$, as per Proposition 2.1.3.2(3)).

Since all the statements of the Lemma are stable under finite $\mathbf C$-linear combinations of Schwartz-Bruhat functions, we may rename any of the $f_k$ as $f$ and reduce to the case $f$ is of the form in (2.2.2.4).

Any compact subset in $\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$ is contained in a finite union of $(F^\times\times F)$-translates of subsets of the form $Z=(s_F([a,b])\cdot E_F^1)\times\overline{D}_F$, for $E_F^1$ the idelic fundamental domain of (A.2.3.14), $s_F\colon\mathbf R_{>0}\to\mathrm{GL}_1(\mathbf A_F)$ the canonical section to the idelic norm, and $[a,b]\subset\mathbf R_{>0}$ a sufficiently large (dependent on the given compact subset in $\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$) compact interval, and $\overline{D}_F$ the compact subset $\mathbf A_F$ obtained as the closure of the fundamental domain $D_F$ from (A.2.1.2) for the additive translation action of $F$ on $\mathbf A_F$. By Proposition A.2.3.10(1), $Z$ is indeed compact in $\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F$.

In order to show the locally uniform convergence of (2.2.2.1), at the cost of replacing the function $f$ with an $F^\times$-translate and applying an $F$-translation to the summation index in $\sum_{\xi\in F}$, it is enough to prove uniform convergence over compact subsets of the form $Z_0\times\overline{D}_F$ for a compact subset $Z_0\subset\mathrm{GL}_1(\mathbf A_F)$ of the form $s_F([a,b])\cdot\overline{E}_F^1$.

For the moment, let $(g,x)\in Z$ be fixed. Then the set of those $\xi\in F$ such that $f(g(\xi+x))$ is nonzero, satisfies the following condition: for every finite place $v$ of $F$, $\xi\in -x+g^{-1}K_v\subset F_v$ with $\xi$ viewed as an element of $F_v$ and $\xi\in -x+g^{-1}\mathcal O_{F_v}$ for all but finitely many $v$.

We call

$$
F_{(g,x)}:=\{\xi\in F:f(g(\xi+x))\ne 0\}\subset F \tag{2.2.2.5}
$$

## PDF page 79

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **79**

and observe that for every finite place $v$ of $F$, the $v$-adic absolute value of any $\xi\in F_{(g,x)}$ satisfies

$$
0\le\lvert\xi\rvert_v\le\max\{\lvert x\rvert_v,C_v\lvert g_v\rvert_v^{-1}\}\le\max\{1,C_v\lvert g_v\rvert_v^{-1}\} \tag{2.2.2.6}
$$

with $C_v:=\lvert K_v\rvert_v\ge 0$, which is finite being $K_v$ compact and $\lvert\cdot\rvert_v:F_v\to\mathbf{R}_{\ge 0}$ continuous. We have used that for every $x\in\overline{D}_F$, $\lvert x_v\rvert_v\le 1$ for every finite place $v$ (see (A.2.1.2)).

We call $S$ the finite set of finite places of $F$ such that $K_v\ne\mathcal{O}_{F_v}$.

We have:

(1) If $K_v=\mathcal{O}_{F_v}$, we have $\lvert\xi\rvert_v\le\max\{1,\lvert g_v\rvert_v^{-1}\}$. This is because $\lvert\mathcal{O}_v\rvert\le 1$ for every finite place $v$ of $F$, and $K_v=\mathcal{O}_v$ for all such finite places $v$.

Moreover, there exists a finite set of finite places $S_g$ of $F$ such that $\lvert g_w\rvert_w=1$ for all $w\in\Sigma_{F,f}-S_g$, since $g$ is an idele. It follows that for all $v\in\Sigma_{F,f}-(S_g\cup S)$, we have $\lvert\xi\rvert_v\le 1$.

(2) For $v\in S$, $\lvert\xi\rvert_v$ is bounded above by a positive constant $C$ independent of $a$, $b$, but possibly depending on $F$, $S$. Namely, we call

$$
C:=\max_{1\le i\le h_F}\max\{C_v\lvert g_{i,v}\rvert_v^{-1}:v\in S\} \tag{2.2.2.7}
$$

where $g_1,\ldots,g_{h_F}\in\mathrm{GL}_1(\mathbf{A}_F)^1$ is the choice of representatives for the $h_F$ ideal classes in $\mathrm{Pic}(\mathcal{O}_F)$, chosen in the construction of $E_F^1$.

We now let $(g,x)$ vary over the compact subset $Z=Z_0\times\overline{D}_F$ of $\mathrm{GL}_1(\mathbf{A}_F)\times\mathbf{A}_F$.

We observe that the chosen subset $\bigcup_{g\in Z_0}S_g$ of the set of finite places of $F$, is itself finite.

Indeed, by (A.2.3.16), given the structure of $E_F^1$ from (A.2.3.14) and the fact that $s_F([a,b])$ is contained in the closed subgroup $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times 1\subset\mathrm{GL}_1(\mathbf{A}_F)$, the non-Archimedean coordinates of the points in $Z_0$ are contained in a subset of $\mathrm{GL}_1(\mathbf{A}_F^f)$ of the following form:

$$
\overline{g_1}\widehat{\mathcal O}_F^{\times}\cup\ldots\cup\overline{g_{h_F}}\widehat{\mathcal O}_F^{\times} \tag{2.2.2.8}
$$

where $h_F$ is the class number of $F$, and with each $\overline{g_i}\in\mathrm{GL}_1(\mathbf{A}_F^f)$ the projection onto $\mathrm{GL}_1(\mathbf{A}_F^f)$ of an element $g_i\in\mathrm{GL}_1(\mathbf{A}_F)^1$.

It follows that we have

$$
\bigcup_{g\in Z_0}S_g\subset S_{g_1}\cup\ldots\cup S_{g_{H_{\Gamma}}} \tag{2.2.2.9}
$$

a finite set.

Upon renaming $S\cup\bigcup_{(g,x)\in Z}S_g=S\cup\bigcup_{g\in Z_0}S_g$ as $S$, again a finite set of finite places of $F$, we may and do assume that we have, calling

$$
F_Z:=\bigcup_{(g,x)\in Z}F_{(g,x)}=\{\xi\in F:f(g(\xi+x))\ne 0\text{ for some }(g,x)\in Z\}\subset F \tag{2.2.2.10}
$$

that for every $\xi\in F_Z$, the following conditions hold:

(1) If $v\in\Sigma_{F,f}-S$, we have $\lvert\xi\rvert_v\le 1$.

(2) For $v\in S$, we have $\lvert\xi\rvert_v\le C$.

In other words, upon defining

$$
U:=\{(u_v)\in\mathbf{A}_F^f:\lvert u_v\rvert_v\le C\text{ for all }v\in S,\ \lvert u_v\rvert_v\le 1\text{ for all }v\in\Sigma_{F,f}-S\}\subset\mathbf{A}_F^f
$$

a compact open subgroup of $\mathbf{A}_F^f$ since $S$ is finite, we have $F_Z\subset U$, with $F$ diagonally embedded into $\mathbf{A}_F^f$.

For each $v\in S$, we call $n_v$ a nonnegative integer such that $\lvert\pi_v\rvert_v^{n_v}\ge C$. Since $S$ is finite, then the subset $I_f:=\prod_{v\in S}\mathfrak{p}_v^{n_v}\subset F$ is a fractional ideal, and $I_f\mathbf{A}_F^f$ contains $U$.

## PDF page 80

**80** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

We therefore have, for every $(g,x)\in Z$:

$$
\sum_{\xi\in F^{\times}}\lvert f(g(\xi+x))\rvert\le\sum_{\xi\in I_f-\{0\}}\lvert f_\infty(g_\infty(\xi+x_\infty))\rvert\left\lvert\prod_{v\in S}f_v(g_v(\xi+x_v))\right\rvert\le\sum_{\xi\in I_f-\{0\}}\lvert f_\infty(g_\infty(\xi+x_\infty))\rvert \tag{2.2.2.11}
$$

where $x_\infty=(x_v)_{v\in S_\infty}\in\mathbf{A}_{F,S_\infty}$ is the image of $x\in\overline{D}_F$ into $\mathbf{A}_{F,S_\infty}$ under the projection $\mathbf{A}_F\to\mathbf{A}_{F,S_\infty}$, and $g_\infty\in\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ is the image of $g\in Z_0\subset\mathrm{GL}_1(\mathbf{A}_F)$ under the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$.

Here we have used that $\lvert f_v\rvert\le 1$ for every $v\in\Sigma_{F,f}$, because, regardless of whether $v\in S$ or not, $f_v$ is an indicator function, hence valued in $\{0,1\}$.

Upon choosing $x=0$, then the leftmost side of (2.2.2.11) is invariant under left translation by $F^{\times}$ on $g\in\mathrm{GL}_1(\mathbf{A}_F)$, if convergent. In particular, the inequality in (2.2.2.11) with $x=0$ holds for all $g\in F^{\times}(s_F([a,b])\cdot\overline{E}_F^1)=s_F([a,b])\cdot\mathrm{GL}_1(\mathbf{A}_F)^1$ and as $g_\infty$ varies over $s_F([a,b])\cdot\overline{E}_\infty$.

Moreover, since formation of $I_f$ does not depend on $a,b$, $g$ is allowed to vary over $\bigcup_{a<b}s_F([a,b])\cdot\mathrm{GL}_1(\mathbf{A}_F)^1=\mathrm{GL}_1(\mathbf{A}_F)$, and the inequality in (2.2.2.11) with $x=0$ still holds as $g_\infty$ varies over $T_\infty\cdot\overline{E}_\infty$, which is what we wanted to show. This proves (3), provided the rightmost side in (2.2.2.11) converges uniformly over our choice of $Z$. (Note that formation of $I_f$ depends on our choice of $Z$.)

We now study the uniform convergence of the right side of (2.2.2.11) over $Z=Z_0\times\overline{D}_F$ where

$$
Z_0=s_F([a,b])\cdot\left(\bigcup_{1\le i\le h_F}g_i(\overline{E}_0\times\widehat{\mathcal O}_F^{\times})\right)
$$

for $g_i\in\mathrm{GL}_1(\mathbf{A}_F)^1$ representives of $\mathrm{Pic}(\mathcal{O}_F)$ (see Proposition A.2.3.9). It is enough to replace $Z$ with $s_F([a,b])\cdot(\overline{E}_0\times\widehat{\mathcal O}_F^{\times})$, with $E_0\subset\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1$ defined in (A.2.3.13).

We therefore let the Archimedean component $g_\infty$ of $g\in\mathrm{GL}_1(\mathbf{A}_F)$, vary over the compact subset $s_{F,\infty}([a,b])\cdot\overline{E}_0$ of $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$, and we let $x_\infty$, the Archimedean component of $x$, vary over $\overline{D}_{F,\infty}$, the compact closure of $D_{F,\infty}$ from (A.2.1.1). Recall that $s_{F,\infty}$ is the continuous one-parameter subgroup of $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ induced by the canonical section $s_F$ to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$, being its image contained in $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times 1\subset\mathrm{GL}_1(\mathbf{A}_F)$ (see (A.2.2.9)).

For each integer $N\ge 1$, there exist a compact subset $B\subset\mathbf{A}_{F,S_\infty}\simeq\prod_{v\in S_\infty}F_v$ containing the origin, a real number $C_{N,B}>0$, such that $\lvert f_\infty(y_\infty)\rvert\le C_{N,B}\lVert y_\infty\rVert^{-N}$ for all $y_\infty\in\mathbf{A}_{F,S_\infty}-B$, where $\lVert\cdot\rVert$ is the standard Euclidean norm on $\mathbf{A}_{F,S_\infty}$ induced by the absolute values $\lvert\cdot\rvert_v$ for each infinite place $v$ of $F$, defined by $\lVert y_\infty\rVert^2=\sum_{v\in S_\infty}\lvert y_v\rvert_v^{N_v}$ where $N_v=2$ if $v$ is real, and $N_v=1$ if $v$ is complex, and with $y_\infty=(y_v)_{v\in S_\infty}$.

We define $Z_\infty:=(s_{F,\infty}([a,b])\cdot\overline{E}_0)\times\overline{D}_{F,\infty}$.

For $(g_\infty,x_\infty)$ varying over $Z_\infty$, the condition on $\xi\in I_f-\{0\}$:

$$
g_\infty(\xi+x_\infty)\in B
$$

reads

$$
\xi\in -\overline{D}_{F,\infty}+(s_{F,\infty}([a,b])\cdot\overline{E}_0)^{-1}B.
$$

Since $I_f\subset\mathbf{A}_{F,S_\infty}$ is discrete, its intersection with the compact subset

$$
Y:=-\overline{D}_{F,\infty}+(s_{F,\infty}([a,b])\cdot\overline{E}_0)^{-1}B
$$

of $\mathbf{A}_{F,S_\infty}$ is finite and the convergence of the rightmost side of (2.2.2.11) is equivalent to the convergence of the series

$$
\sum_{\xi\in I_f-Y\cap I_f}\lvert f_\infty(g_\infty(\xi+x_\infty))\rvert \tag{2.2.2.12}
$$

uniformly over $Z_\infty$.

## PDF page 81

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **81**

This is in turn implied by that of the series

$$
\sum_{\xi\in I_f-Y\cap I_f}\lVert g_\infty(\xi+x_\infty)\rVert^{-N} \tag{2.2.2.13}
$$

over $Z_\infty$.

Since $s_{F,\infty}([a,b])\cdot\overline{E}_0\subset\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ is compact, and $g_\infty$ varies over a compact subset of $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$, hence away from the origin, the convergence of the series in (2.2.2.13) uniformly over $Z_\infty$ is implied by that of the series

$$
\sum_{\xi\in I_f-B\cap I_f}\lVert\xi+x_\infty\rVert^{-N} \tag{2.2.2.14}
$$

uniformly over $\overline{D}_{F,\infty}$. This holds for $N>[F:\mathbf{Q}]=\dim_{\mathbf{R}}(\mathbf{A}_{F,S_\infty})$ locally uniformly with respect to $x_\infty$ by Proposition 2.2.1.3 applied to (2.2.2.14) with $\Gamma=I_f$ up to $\mathbf{R}$-linear isomorphism of Euclidean spaces.

The inequality in (2.2.2.11) shows that the series in (2.2.2.1) converges absolutely and uniformly on the compact subset $Z\subset\mathrm{GL}_1(\mathbf{A}_F)\times\mathbf{A}_F$.

Local uniformity of the convergence and continuity of $f$ implies that the sum of the series is itself continuous as a function of $(g,x)\in\mathrm{GL}_1(\mathbf{A}_F)\times\mathbf{A}_F$.

Both invariance conditions (1) and (2) hold by inspection, given the absolute convergence of the series. $\square$

REMARK 2.2.2.3. To later study the functions arising as

$$
\Psi_F(f)(g,0)=\sum_{\xi\in F^{\times}}f(\xi g)
$$

we will need to know that for $f$ as in part (3) of the Lemma, formation of $I_f$ depends on $f$ only through its non-Archimedean tensor component, and through the choice of $E_F^1$, but not through $f_\infty$.

What the argument is saying is that for each choice of compact subset $Z\subset\mathrm{GL}_1(\mathbf{A}_F)\times\mathbf{A}_F$, at least one such $I_f$ exists. The existence of $I_f$ can be reduced to the case $Z=Z_0\times\overline{D}_F$ with $Z_0$ of the form $K\cdot E_F^1$, for some compact subset $K$ of $s_F(\mathbf{R}_{>0})$.

By inspection of the proof, formation of $I_f$ will not depend on $K$. It does rest upon the structure of $E_F^1$, and so the $I_f$ constructed above will do for the choice $Z=(K\cdot E_F^1)\times\overline{D}_F$, for any compact subset $K\subset s_F(\mathbf{R}_{>0})$.

**2.2.3. The $\theta$-function operator $\Phi_F:\mathcal{S}(\mathbf{A}_F)\to C(C_F)$.** In this section we study the linear operator

$$
\Phi_F:\mathcal{S}(\mathbf{A}_F)\to C(C_F)
$$

defined by sending a Schwartz-Bruhat function on $\mathbf{A}_F$ to its restriction to the idele group $\mathrm{GL}_1(\mathbf{A}_F)$, averaged over the orbits under the action of the discrete subgroup $F^{\times}$.

The operator $\Phi_F$ is a special case of $\Psi_F$ defined in Lemma 2.2.2.1. The Riemann-Roch Theorem in [CF, Thm.4.2.1] will enable sharp estimates for the resulting functions over the idele class group $C_F$, over *both* loci $C_F^{\gg 1}$ and $C_F^{\ll 1}$, i.e. the subsets of those idele classes whose idelic norm is very large, respectively very small.

By Lemma 2.2.2.1(2), for any $f\in\mathcal{S}(\mathbf{A}_F)$ the continuous function $\Psi_F(g,0)$ of $g\in\mathrm{GL}_1(\mathbf{A}_F)$ is invariant under the left translation action by the discrete subgroup $F^{\times}\subset\mathrm{GL}_1(\mathbf{A}_F)$.

DEFINITION 2.2.3.1 (Global adelic $\theta$-functions). Let $F$ be a number field, $f\in\mathcal{S}(\mathbf{A}_F)$ a Schwartz-Bruhat function.

We denote by

$$
\Phi_F(f)(g):=\Psi_F(f)(g',0)=\sum_{\xi\in F^{\times}}f(\xi g') \tag{2.2.3.1}
$$

## PDF page 82

**82** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

the continuous function of $g\in C_F$ obtained from $f$ by averaging the restriction of $f$ to $\mathrm{GL}_1(\mathbf{A}_F)$ over the $F^{\times}$-orbits, where $g'$ is any choice of lift of $g$ under the continuous surjective homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to C_F$.

We refer to the function $\Phi_F(f)$ on $C_F$ as the *global adelic $\theta$-function of $f$*.

The definition of $\Phi_F$ in (2.2.3.1) is independent of such choice by $F^{\times}$-invariance of $\Psi_F(g,0)$.

The assignment $\Phi_F$ on $\mathcal{S}(\mathbf{A}_F)$ is valued in $C(C_F)$ and its formation is $\mathbf{C}$-linear. We will now proceed to study the function $\Phi_F(f)(g)$ of $g\in C_F$, and its asymptotic behavior as $\lvert g\rvert_F\to 0^+$ and as $\lvert g\rvert_F\to +\infty$.

We refer to $\Phi_F(f)$ as “$\theta$-function”, with a non-capitalized $\theta$, because the true direct analog of the Jacobi $\Theta$-function from Riemann’s paper on the number of prime numbers below a given magnitude, is the function defined by the full sum

$$
\Theta_F(f)(g):=\sum_{\xi\in F}f(\xi g)
$$

i.e. not merely the sum over the translates by *nonzero* elements of $F$. The construction under consideration is indeed the one in use throughout this work, i.e. we will be using $\Phi_F(f)$ throughout this work, as opposed to $\Theta_F(f)$.

We have taken a habit of using the letter $\Phi$ to denote the adelic $\theta$-functions thus defined, because we will be showing that the operator $\Phi_F$ is valued in the Schwartz-Bruhat space $\mathcal{S}(C_F)$ of the idele class group, and we will be denoting with the letter $\phi$ the generic element of $\mathcal{S}(C_F)$.

*2.2.3.1. Estimates over the idele class group.* The following Theorem is Tate’s “Riemann-Roch Theorem”, for which we refer the reader to [CF, Ch.XV, §4, Thm.4.2.1].

THEOREM 2.2.3.2 (Adelic Riemann-Roch Theorem). *Let $F$ be a number field, $f\in\mathcal{S}(\mathbf{A}_F)$ a Schwartz-Bruhat function. As continuous functions over $C_F$, the following identity holds:*

$$
\Phi_F(f)(g)=\lvert g\rvert_F^{-1}\Phi_F(\widehat{f})(g^{-1})+\lvert g\rvert_F^{-1}\widehat{f}(0)-f(0). \tag{2.2.3.2}
$$

REMARK 2.2.3.3 (On the volume normalization and the global Fourier Transform). We note that the choice of Haar measure on $\mathbf{A}_F$, respectively $\mathbf{A}_{F,S}$, in force throughout this work, is the unique choice of Haar measure such that, upon endowing the discrete subgroups $F\subset\mathbf{A}_F$, respectively $\mathcal{O}_{F,S}\subset\mathbf{A}_{F,S}$, with the counting measure, the unique measure determined as per Theorem D.1.2.1 on the compact Hausdorff quotients $\mathbf{A}_F/F$, respectively $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$, gives such quotients volume 1.

We refer the reader to Remark A.3.4.2, and to Remark A.3.2.5, and the references contained therein.

This choice of measure is the same being made in [CF, Ch.XV, §4] and in [Co, Appendix I, (34), p.57], and removes volume factors from the statement of Theorem 2.2.3.2 (since they equal 1); see the beginning of [CF, Ch.XV, §4, p.334].

PROOF. This is a direct consequence of [CF, Ch.XV, Thm.4.2.1] and Lemma 2.2.2.1, which shows that the Theorem applies. We have, by [CF, Ch.XV, Thm.4.2.1]:

$$
\Psi_F(g,0)-\lvert g\rvert_F^{-1}\widehat{f}(0)+f(0)=\lvert g\rvert_F^{-1}\Psi_F(\widehat{f})(g^{-1},0) \tag{2.2.3.3}
$$

as continuous functions on $\mathrm{GL}_1(\mathbf{A}_F)$. Since $\lvert\cdot\rvert_F$ is continuous and $F^{\times}$-invariant, then the identity in (2.2.3.3) reads, as an identity of continuous functions of $g\in C_F$:

$$
\Phi_F(f)(g)-\lvert g\rvert_F^{-1}\widehat{f}(0)+f(0)=\lvert g\rvert_F^{-1}\Phi_F(\widehat{f})(g^{-1})
$$

which is (2.2.3.2). $\square$

The following is the main result of this subsection:

THEOREM 2.2.3.4 (Estimates over the Idele Classes - I). *Let $f\in\mathcal{S}(\mathbf{A}_F)$ be a Schwartz-Bruhat function on $\mathbf{A}_F$. The continuous function $\Phi_F(f)$ on $C_F$, satisfies the following growth conditions:*

## PDF page 83

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **83**

(1) *for every integer $N\ge 0$, there exists a real number $C_N>0$ such that for every $g\in C_F$, we have*

$$
\lvert\Phi_F(f)(g)\rvert\le C_N\lvert g\rvert_F^{-N} \tag{2.2.3.4}
$$

*as $g\in C_F$ is such that $\lvert g\rvert_F\to +\infty$.*

(2) *For every integer $N\ge 0$, there exists a real number $C_N>0$ such that for every $g\in C_F$, we have*

$$
\lvert\Phi_F(f)(g)-\lvert g\rvert_F^{-1}\widehat{f}(0)+f(0)\rvert\le C_N\lvert g\rvert_F^{N} \tag{2.2.3.5}
$$

*as $g\in C_F$ is such that $\lvert g\rvert_F\to 0$.*

(3) *Assume $f(0)=\widehat{f}(0)=0$. For every integer $N\ge 0$, there exists a real number $C_N>0$ such that for every $g\in C_F$, we have*

$$
\lvert\Phi_F(f)(g)\rvert\le C_N e^{-N\lvert\log\lvert g\rvert_F\rvert} \tag{2.2.3.6}
$$

*as $g\in C_F$ is such that $\lvert\log\lvert g\rvert_F\rvert\to +\infty$ (equivalently, $\lvert g\rvert_F\to 0,+\infty$).*

(4) *Let $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_F)$ be a bounded subset. For every integer $N\ge 0$, there exist real numbers $C_{\mathcal{B},N},T_{\mathcal{B},N}>0$ such that (2.2.3.4), (2.2.3.5) and (2.2.3.6) hold for $C_N=C_{\mathcal{B},N}$, and for all $g\in C_F$ such that $\lvert g\rvert_F>T_{\mathcal{B},N}$, respectively $\lvert g\rvert_F<T_{\mathcal{B},N}$, respectively $e^{-\lvert\log\lvert g\rvert_F\rvert}<T_{\mathcal{B},N}$.*

(5) *For every integer $N\ge 0$, the assertions in (4) all hold with $T_{\mathcal{B},N}=1$ and with a possibly larger but still uniform $C_{\mathcal{B},N}>0$.*

PROOF. By Lemma 2.2.2.1, the series (2.2.2.1) defining $\Psi_F(f)(g,0)=\sum_{\xi\in F^{\times}}f(\xi g)$ converges absolutely and uniformly on the compact subsets of $\mathrm{GL}_1(\mathbf{A}_F)$ to a continuous function of $g\in\mathrm{GL}_1(\mathbf{A}_F)$.

By Theorem 2.2.3.2, we have, as continuous functions on $C_F$:

$$
\Phi_F(f)(g)-\lvert g\rvert_F^{-1}\widehat{f}(0)+f(0)=\lvert g\rvert_F^{-1}\Phi_F(\widehat{f})(g^{-1}). \tag{2.2.3.7}
$$

The change of variable $g\mapsto g^{-1}$ on $C_F$ therefore reduces (2.2.3.5) for $f$ to (2.2.3.4) for $\widehat{f}$, and since (3) follows from the combination of (1) and (2), it is enough to verify that (1) holds.

We write $f=\sum_{k=1}^{m}c_k f_k$ with $m\ge 1$ an integer, $c_k\in\mathbf{C}$ and $f_k\in\mathcal{S}(\mathbf{A}_F)$ of the special form $f_k=f_{k,\infty}\prod_{v\nmid\infty}f_{k,v}$, with $f_{k,\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ and $f_{k,v}\in\mathcal{S}(F_v)$ with $f_{k,v}=1_{\mathcal{O}_{F_v}}$ for all but finitely many finite places $v$ of $F$. Since formation of $\Phi_F$ in (2.2.3.4) is $\mathbf{C}$-linear with respect to $f$, we may rename any of $f_k$ as $f$ and reduce to the case $f$ is of this special form.

We claim that (2.2.3.4) follows from the rapid decay condition on $f_{\infty}$. By replacing $g$ with an $F^{\times}$-translate, we can assume $g$ varies over $T_{\infty}\cdot E_{\infty}$ ($T_{\infty}$ and $E_{\infty}$ being defined in the discussion preceding Lemma 2.2.2.1). The continuous homomorphic section $\tau$ to $\prod_{v\in S_{\infty}}\lvert\cdot\rvert_v$ and therefore $\lvert\cdot\rvert_F$, that we are choosing, is the diagonal section $s_{F,\delta}$, constructed in (A.2.2.11), a choice that will interact well with the supremum norm on the Euclidean space $\mathbf{A}_{F,S_{\infty}}\simeq\mathbf{R}^{r_1+2r_2}$.

Thus Lemma 2.2.2.1(3) applies, and we have

$$
\sum_{\xi\in F^{\times}}\lvert f(\xi g)\rvert\le\sum_{\xi\in I_f-\{0\}}\lvert f_{\infty}(\xi g_{\infty})\rvert \tag{2.2.3.8}
$$

for a fractional ideal $I_f$ depending on $f$, where $g_{\infty}$ is the image of $g$ under the continuous projection $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$, and $g_{\infty}$ is allowed to vary over the subset $T_{\infty}\cdot E_{\infty}\subset\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$.

Since $f_{\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$, then for any integer $N'\ge 0$, there exists a large enough compact subset $B\subset\mathbf{A}_{F,S_{\infty}}\simeq\prod_{v\in S_{\infty}}F_v$ containing the origin, and a real number $C_{B,N'}>0$, such that for all $x_{\infty}\in\mathbf{A}_{F,S_{\infty}}-B$ we have

$$
\lvert f_{\infty}(x_{\infty})\rvert\le C_{B,N'}\lVert x_{\infty}\rVert^{-N'}
$$

where $\lVert\cdot\rVert$ is the Euclidean supremum norm on $\mathbf{A}_{F,S_{\infty}}$ induced by the Archimedean absolute value on each $F_v$, defined by $\lVert x_{\infty}\rVert:=\sup_{v\in S_{\infty}}\lvert x_v\rvert_v^{N_v}$ where $N_v=1$ if $v$ is real, and $N_v=1/2$ if $v$ is complex.

## PDF page 84

**84** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

We define $T=s_{F,\delta}(\mathbf{R}_{>0})$ for $s_{F,\delta}$ the diagonal section to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$ from (A.2.2.11), and $E_F^1$ denotes the fundamental domain of the $F^{\times}$-action on $\mathrm{GL}_1(\mathbf{A}_F)^1$ from (A.2.3.14). Since $I_f\subset\mathbf{A}_{F,S_{\infty}}$ is discrete, there exists a large enough real number $C>0$ such that for all $t\in T$ for which $\lvert t\rvert_F>C$ we have, upon calling $E_{\infty}$ the image of $E_F^1$ under the continuous projection $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ and $t_{\infty}$ the image of $t$:

$$
B\cap (t_{\infty}\cdot (I_f-\{0\})\cdot E_{\infty})=\varnothing. \tag{2.2.3.9}
$$

Note that the subset $E_{\infty}$ is bounded. We claim that there exists a constant $C>0$ such that for any $t\in T$ for which $\lvert t\rvert_F>C$, $B\cap t_{\infty}\xi E_{\infty}=\varnothing$ for all $\xi\in I_f-\{0\}$. The proof rests on the inequality

$$
\lVert t_{\infty}\xi E_{\infty}\rVert\ge A\lVert t_{\infty}\xi\rVert=A\lvert t\rvert_F\lVert\xi\rVert \tag{2.2.3.10}
$$

for a real number $A>0$ depending only on $E_{\infty}$ and $\lVert B\rVert$ is a compact subset of $\mathbf{R}_{>0}$. Indeed, assume there exists an element $x\in B\cap t_{\infty}\xi E_{\infty}$, so $\lVert x\rVert$ is contained in the intersection of $[0,\max\lVert B\rVert]$ and $[A\lvert t\rvert_F\lVert\xi\rVert,+\infty)$. We will now show that these latter two intervals do not overlap (thereby getting a contradiction from the assumed existence of such $x$) when $\lvert t\rvert_F$ is sufficiently large and $\xi$ is arbitrary in $I_f-\{0\}$.

Since $I_f\subset\mathbf{A}_{F,S_{\infty}}$ is a lattice, let $M:=\min_{\xi\in I_f-\{0\}}\lVert\xi\rVert>0$. We define $C:=(AM)^{-1}\max\lVert B\rVert$. For any $\xi\in I_f-\{0\}$, from (2.2.3.10) we have:

$$
\lVert t_{\infty}\xi E_{\infty}\rVert\ge AM\lvert t\rvert_F \tag{2.2.3.11}
$$

and hence the intersection $B\cap t_{\infty}\xi E_{\infty}$ is empty for all $\xi\in I_f-\{0\}$ and when $\lvert t\rvert_F>C$.

We therefore have, for every $g\in\mathrm{GL}_1(\mathbf{A}_F)$ of the form $g=s_{F,\delta}(t_0)g_0$ for unique $t_0\in\mathbf{R}_{>0}$, and $g_0\in E_F^1$, with respective projections $t_{\infty}$ and $g_{0,\infty}$ onto $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$

$$
\lvert f_{\infty}(\xi t_{\infty}g_{0,\infty})\rvert\le C_{B,N'}\lVert\xi t_{\infty}g_{0,\infty}\rVert^{-N'}=C_{B,N'}t_0^{-N'}\lVert\xi g_{0,\infty}\rVert^{-N'} \tag{2.2.3.12}
$$

for any $\xi\in I_f-\{0\}$ and $t_0\in\mathbf{R}_{>0}$ with $t_0>C$, equivalently $\lvert s_{F,\delta}(t_0)\rvert_F>C$.

The series $\sum_{\xi\in I_f-\{0\}}\lVert\xi g_{0,\infty}\rVert^{-N'}$ converges for all $N'>r_1+2r_2=\dim_{\mathbf{R}}(\mathbf{A}_{F,S_{\infty}})$ by Proposition 2.2.1.3 and uniformly with respect to $g_{0,\infty}$ varying over $E_{\infty}$ (since its closure in $\mathbf{A}_{F,S_{\infty}}$ is compact and contained in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$). Moreover, this sum is bounded on the compact subset $\overline{E}_{\infty}$ by continuity with respect to $g_{0,\infty}$. Thus, if we choose $N'=1+\max\{r_1+2r_2,N\}$ then there exists a constant $C_N>0$ such that

$$
\sum_{\xi\in I_f-\{0\}}\lvert f_{\infty}(\xi t_{\infty}g_{0,\infty})\rvert\le C_N\lvert t\rvert_F^{-N}=C_N\lvert g\rvert_F^{-N}, \tag{2.2.3.13}
$$

where we have used that $\lvert g\rvert_F>C>1$, and hence $\lvert g\rvert_F^{-N'}\le\lvert g\rvert_F^{-N}$.

(4) : By Proposition 2.1.2.4 and Proposition 2.1.2.8(1), $\mathcal{S}(\mathbf{A}_F^f)$ carries the finest locally convex topology (see also the proof of Proposition 2.1.3.2), and hence each bounded subset of $\mathcal{S}(\mathbf{A}_F^f)$ is contained in a finite dimensional subspace of $\mathcal{S}(\mathbf{A}_F^f)$ by Proposition C.2.5.1(4).

Let $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_F)$ be a bounded subset. By Proposition 2.1.3.2(2), the canonical linear operator $\mathcal{S}(\mathbf{A}_{F,S_{\infty}})\otimes_{\iota}\mathcal{S}(\mathbf{A}_F^f)\to\mathcal{S}(\mathbf{A}_F)$ is a linear topological isomorphism, and hence by Proposition C.2.3.13(2), and writing $\mathcal{S}(\mathbf{A}_F^f)$ as the strict locally convex inductive limit of a countable family of finite dimensional $\mathbf{C}$-vector subspaces, the bounded subset $\mathcal{B}$ in $\mathcal{S}(\mathbf{A}_F)$ is contained, by [Scha, Ch.II,§6,6.5,p.59], in one which is the image of

$$
\mathrm{cch}(\mathcal{B}_{\infty}\otimes\mathcal{B}_f)
$$

the convex circled hull of the subset $\mathcal{B}_{\infty}\otimes\mathcal{B}_f$, with $\mathcal{B}_{\infty}\subset\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$, and $\mathcal{B}_f$ bounded in a finite dimensional $\mathbf{C}$-linear subspace of $\mathcal{S}(\mathbf{A}_F^f)$ (we refer the reader to [Jar, Part III,Ch.15,§15.1,p.324] for the analogous assertion for the projective tensor topology and its own bounded subsets).

There therefore exist finitely many $f_1,\ldots,f_m\in\mathcal{S}(\mathbf{A}_F^f)$ whose linear span contains $\mathcal{B}_f$. In particular, all the functions in $\mathcal{B}_f$ are supported on a large enough compact open subset $K\subset\mathbf{A}_F^f$.

## PDF page 85

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **85**

Every element of $\mathcal{B}$ is therefore a finite absolutely convex $\mathbf{C}$-linear combination (i.e. one whose coefficients have complex Euclidean absolute values that sum to a real number bounded above by 1; see [Jar, Part I,Ch.6,§6.1,p.102] for $r=1$; see also [NB, Thm.4.2.11]) of Schwartz-Bruhat functions of the form $f_{\infty}\otimes f_0$ with each of the $f_0$ supported on the common $K$ whose existence was proved above. Moreover, each $f_0$ is obtained as a finite linear combination of indicator functions of compact open subsets all contained in $K$, with complex coefficients of complex absolute value bounded above by a positive real number depending only on $\mathcal{B}_f$ (since $\mathcal{B}_f$ is a bounded subset of a finite dimensional Euclidean $\mathbf{C}$-vector space, and hence, within such finite dimensional Euclidean $\mathbf{C}$-vector space, upon choosing a $\mathbf{C}$-linear basis $\{f_1,\ldots,f_m\}$ as in the foregoing, $\mathcal{B}_f$ is contained within a compact box).

By construction of $C_N$ from (1), this constant therefore depends on the element of $\mathcal{B}_{\infty}\otimes\mathcal{B}_f$ only through the $\mathcal{B}_{\infty}$-tensor factor, through $K$, and through the positive real constant bounding from above the complex absolute values of the coefficients of the $\mathbf{C}$-linear expansion of the generic element $f_0\in\mathcal{B}_f$ with respect to the chosen $\mathbf{C}$-linear basis of indicator functions $\{f_1,\ldots,f_m\}$.

Specifically, the dependence through $K$ is through the formation of the fractional ideal $I_f\subset F$.

That the real number $T_N>0$ such that (2.3.1.3) holds if $\lvert g\rvert_F>T_N$, and whose formation is uniform as $f$ varies over $\mathcal{B}$, exists, is seen by observing that formation of $B$ from the foregoing depends on $f$ through $f_{\infty}$, for $f$ of the special form $f=f_{\infty}\otimes f_0\in\mathcal{B}_{\infty}\otimes\mathcal{B}_f$.

In particular, the same ball $B\subset\mathbf{A}_{F,S_{\infty}}$ qualifies to give, through the argument from the foregoing, the estimate in (2.2.3.8) as $f_{\infty}$ varies over the bounded subset $\mathcal{B}_{\infty}\subset\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$.

We have now shown that (2.3.1.3) holds for each $f$ of the special form $f_{\infty}\otimes f_0$ with $f_{\infty}\in\mathcal{B}_{\infty}$ and $f_0\in\mathcal{B}_f$, with $C_N$ and $T_N$ existing and depending only on $\mathcal{B}_{\infty}$ and $\mathcal{B}_f$.

By linearity of $\Phi_F$ and the design of the convex circled hull (see [Jar, Part I,Ch.6,§6.1,p.102] for $r=1$; see also [NB, Thm.4.2.11]), the estimate in (2.2.3.4) propagates with the same $C_N$ and $T_N$ to the elements of $\mathrm{cch}(\mathcal{B}_{\infty}\otimes\mathcal{B}_f)$, and hence to all the elements of the bounded subset $\mathcal{B}$.

We rename $C_N$ as $C_{\mathcal{B},N}$, and $T_N$ as $T_{\mathcal{B},N}$, and these constants satisfy the requirements of (4).

The case of (2.2.3.5) and (2.2.3.6) follows from the foregoing (at the cost of changing $T_{\mathcal{B},N}$, obtaining another constant that still depends only on $\mathcal{B}$ and $N$, and this is possible since the Fourier transform on $\mathcal{S}(\mathbf{A}_F)$ is a linear topological automorphism, hence preserves bounded subsets in both directions.

(5) : By (4), there exist, for each integer $N\ge 0$, positive real numbers $C_{\mathcal{B},N},T_{\mathcal{B},N}>0$ such that the assertions in (1),(2) and (3) hold, respectively, for all $f\in\mathcal{B}$, upon replacing $T_N$ with $T_{\mathcal{B},N}$ and $C_N$ with $C_{\mathcal{B},N}$.

We prove that there exists $C_{\mathcal{B}}>0$, such that for all $f\in\mathcal{B}$, we have:

$$
\lvert\Phi_F(f)(g)\rvert\le C_{\mathcal{B}} \tag{2.2.3.14}
$$

for all $g\in C_F$ satisfying $\lvert g\rvert_F\in[1/t_{\mathcal{B},N},t_{\mathcal{B},N}]$, where $t_{\mathcal{B},N}:=\max\{1/T_{\mathcal{B},N},T_{\mathcal{B},N}\}$.

If so, then we rename $\max\{C_{\mathcal{B}},C_{\mathcal{B},N}\}$ as $C_{\mathcal{B},N}$, and (5) follows upon replacing $T_{\mathcal{B},N}$ with 1, and with this choice of $C_{\mathcal{B},N}$.

As in the argument for (4), there exists a bounded subset $\mathcal{B}_{\infty}\subset\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ and a bounded subset $\mathcal{B}_f\subset\mathcal{S}(\mathbf{A}_F^f)$ entirely contained in a finite dimensional $\mathbf{C}$-linear subspace of $\mathcal{S}(\mathbf{A}_F^f)$, such that $\mathcal{B}\subset\mathrm{cch}(\mathcal{B}_{\infty}\otimes\mathcal{B}_f)$, the convex circled hull of the subset $\mathcal{B}_{\infty}\otimes\mathcal{B}_f\subset\mathcal{S}(\mathbf{A}_F)$.

The generic element of $\mathrm{cch}(\mathcal{B}_{\infty}\otimes\mathcal{B}_f)$ is therefore an absolutely convex finite $\mathbf{C}$-linear combitation of elements of the form $f_{\infty}\otimes f_0$, with $f_{\infty}\in\mathcal{B}_{\infty}$, and, upon choosing a $\mathbf{C}$-linear basis $\{f_1,\ldots,f_m\}$ for a fixed large enough finite dimensional $\mathbf{C}$-linear subspace of $\mathcal{S}(\mathbf{A}_F^f)$ containing $\mathcal{B}_f$ (which exists by [Scha, Ch.II,§6,6.5,p.59]), $f_0$ is in turn a finite $\mathbf{C}$-linear combination of $f_1,\ldots,f_m$ whose complex coefficients have complex absolute value bounded above by a positive real number which depends only on $\mathcal{B}_f$.

## PDF page 86

**86** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

To obtain the estimate from (2.2.3.14) with a constant $C_{\mathcal{B}}$ that does not depend on $f\in\mathcal{B}$, but only on $\mathcal{B}$, it is therefore enough to find such constant when $f$ is of the form $f_{\infty}\otimes f_k$, for each $1\le k\le m$. We let $K\subset\mathbf{A}_F^f$ be a compact open subset containing the supports of all the finitely many $f_1,\ldots,f_m$.

There exists a fractional ideal $I\subset F$ depending only on $K$, such that:

$$
\lvert\Phi_F(f_{\infty}\otimes 1_K)(g)\rvert\le\sum_{\xi\in I-\{0\}}\lvert f_{\infty}(\xi g_{\infty})\rvert \tag{2.2.3.15}
$$

for all $g\in\tau(\mathbf{R}_{>0})\cdot E_F^1$, with $g_{\infty}$ the image of $g\in\mathrm{GL}_1(\mathbf{A}_F)$ into $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ under the continuous homomorphic projection $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$, where $\tau$ is a choice of continuous homomorphic section to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$, and $E_F^1$ is the idelic fundamental domain from (A.2.3.14); see Lemma 2.2.2.1(3).

The series on the right side of (2.2.3.15) converges uniformly on the compact subsets of $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$, and hence its limit is a continuous function on the image of $\tau(\mathbf{R}_{>0})\cdot E_F^1$ into $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$. Since $\tau([1/t_{\mathcal{B},N},t_{\mathcal{B},N}])\cdot E_F^1$ is relatively compact and with non-empty interior, and $I$ does not depend on $f_{\infty}$, we deduce that:

$$
\alpha:f_{\infty}\mapsto\sup_{g\in\tau([1/t_{\mathcal{B},N},t_{\mathcal{B},N}])\cdot E_F^1}\sum_{\xi\in I-\{0\}}\lvert f_{\infty}(\xi g_{\infty})\rvert
$$

is a continuous function on $\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$. Continuity is seen as follows: for any $f_{\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ and any sequence $\{f_{\infty,j}\}_{j\ge 0}\subset\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ converging to $f_{\infty}$ in $\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$, for each fixed integer $r\ge 1$ there a compact subset $Z\subset\mathbf{A}_{F,S_{\infty}}$ containing the origin and such that, for every $j\ge 0$, $\lvert f_{\infty,j}(x)\rvert\le C\lVert x\rVert^{-r}$ for every $x\in\mathbf{A}_{F,S_{\infty}}-Z$, for a real number $C>0$ independent of $j\ge 0$, and upon choosing a norm $\lVert\cdot\rVert$ on $\mathbf{A}_{F,S_{\infty}}$ inducing the Euclidean topology on $\mathbf{A}_{F,S_{\infty}}$.

The sum $\sum_{\xi\in I-\{0\}}\lvert f_{\infty,j}(\xi g_{\infty})\rvert$ is therefore split into the sum of a finite sum, whose finite index is independent of $j\ge 0$ but only depends on $Z$ and $I$, and of a series of positive real numbers bounded above by a series of the form $C\sum_{\xi\in I-\{0\}}\lVert\xi g_{\infty}\rVert^{-r}$, which converges over $\mathbf{A}_{F,S_{\infty}}-Z$ uniformly on compact subsets (see Proposition 2.2.1.3), upon choosing $r>[F:\mathbf{Q}]$.

By Dominated Convergence, the limit as $j\to +\infty$ of $\sum_{\xi\in I-\{0\}}\lvert f_{\infty,j}(\xi g_{\infty})\rvert$ is $\sum_{\xi\in I-\{0\}}\lvert f_{\infty}(\xi g_{\infty})\rvert$, proving sequential continuity of the function $f_{\infty}\mapsto\sum_{\xi\in I-\{0\}}\lvert f_{\infty}(\xi g_{\infty})\rvert$. Since $\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ is metrizable, it is a sequential topological space, and hence the function $f_{\infty}\mapsto\sum_{\xi\in I-\{0\}}\lvert f_{\infty}(\xi g_{\infty})\rvert$ is continuous, being sequentially continuous.

Since $\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ is Montel by Theorem 2.1.3.2, it has the Heine-Borel property, and hence the closure of $\mathcal{B}_{\infty}$ is compact in $\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$.

The continuous function $\alpha$ is therefore bounded on $\mathcal{B}_{\infty}$, by a positive real number $C_{\mathcal{B}_{\infty}}>0$. Upon maximizing $C_{\mathcal{B}_{\infty}}$ finitely many times, one per each choice of $f_k$, for $1\le k\le m$, and then multiplying it by the maximum of the positive real number and its reciprocal, which bounds from above the complex coefficients of each $\mathbf{C}$-linear expansion of each element of $\mathcal{B}_f$ with respect to the $\mathbf{C}$-linear basis $\{f_1,\ldots,f_m\}$ of the finite dimensional Euclidean space of $\mathcal{S}(\mathbf{A}_F^f)$ containing $\mathcal{B}_f$, we obtain a real number $C_{\mathcal{B}}>0$ such that (2.2.3.14) holds for all $f\in\mathcal{B}_{\infty}\otimes\mathcal{B}_f$, and therefore for all the elements of its convex circled hull, and hence for all $f\in\mathcal{B}$.
$\square$

**2.2.4. Compatibility with directional derivatives: global adelic $\theta$-functions.** We fix a choice $\tau:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$ of continuous homomorphic section to the idelic norm. This is a continuous 1-parameter subgroup, which, we thought of as such, we denote by $\gamma_{\tau}:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$. It makes sense to form derivatives along $\gamma_{\tau}$ of smooth functions on $\mathrm{GL}_1(\mathbf{A}_F)$ and $C_F$.

Before we state and prove the main results of this subsection, we classify the images of the continuous 1-parameter subgroups of $\mathrm{GL}_1(\mathbf{A}_F)$, i.e. continuous homomorphisms $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$ of Hausdorff locally compact abelian groups.

LEMMA 2.2.4.1. *Let $F$ be a number field. Let $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$ be a continuous 1-parameter subgroup.*

## PDF page 87

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **87**

*Then $\gamma(\mathbf{R}_{>0})$ is contained in the closed subgroup:*

$$
\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times\{1\}\subset \mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times \mathrm{GL}_1(\mathbf{A}_F^f)=\mathrm{GL}_1(\mathbf{A}_F). \tag{2.2.4.1}
$$

*Then $\gamma$ satisfies exactly one of the following two conditions:*

(1) *The composition $\lvert\cdot\rvert_F\circ\gamma$ is a smooth automorphism of the abelian Lie group $\mathbf{R}_{>0}$, and there exists a unique nonzero real number $\alpha$ such that $\lvert\gamma(t)\rvert_F=t^{\alpha}$ for all $t\in\mathbf{R}_{>0}$.*

(2) *The image of $\gamma$ is contained in the closed subgroup $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1\times\{1\}$ of $\mathrm{GL}_1(\mathbf{A}_F)$.*

PROOF. Since $\mathrm{GL}_1(\mathbf{A}_F)=\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times \mathrm{GL}_1(\mathbf{A}_F^f)$ as Hausdorff locally compact topological abelian groups, and $\mathrm{GL}_1(\mathbf{A}_F^f)$ is totally disconnected, then, as $\mathbf{R}_{>0}$ is connected, $\gamma(\mathbf{R}_{>0})$ is connected and hence contained in the identity component of $\mathrm{GL}_1(\mathbf{A}_F)$, which is indeed contained within the closed subgroup $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times\{1\}$ from (2.2.4.1).

The composition $\lvert\cdot\rvert_F\circ\gamma$ is a continuous group endomorphism of $\mathbf{R}_{>0}$, and it is therefore smooth (by the Closed Subgroup Theorem: a closed subgroup of a Lie group is an embedded Lie group), being $\mathbf{R}_{>0}$ a Lie group. Its tangent map is multiplication by a real number $\alpha$. If $\alpha\ne 0$, then it is smoothly invertible and hence a Lie group automorphism. Since $\mathbf{R}_{>0}$ is simply connected, it is of the form $t\mapsto t^{\alpha}$.

If $\alpha=0$, then $\gamma(\mathbf{R}_{>0})\subset \mathrm{GL}_1(\mathbf{A}_F)^1\cap(\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times\{1\})=\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1\times\{1\}$. $\square$

LEMMA 2.2.4.2. *Let $F$ be a number field, $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$ a continuous $1$-parameter subgroup, $f\in\mathcal{S}(\mathbf{A}_F)$ a Schwartz-Bruhat function.*

Then the limit:

$$
(\partial_{\gamma}f)(x):=\lim_{t\to 1}\frac{f(\gamma(t)x)-f(x)}{t-1} \tag{2.2.4.2}
$$

*exists for every $x\in\mathbf{A}_F$, and it is a Schwartz-Bruhat function on $\mathbf{A}_F$. Moreover, $\partial_{\gamma}:\mathcal{S}(\mathbf{A}_F)\to\mathcal{S}(\mathbf{A}_F)$ is continuous with respect to the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{A}_F)$.*

PROOF. Since the continuous linear operator from (2.1.3.2) is a linear topological isomorphism by Proposition 2.1.3.2, for each Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_F)$, there exist Schwartz-Bruhat functions $f_1,\ldots,f_m\in\mathcal{S}(\mathbf{A}_F)$, each of the form:

$$
f_k=f_{k,\infty}\otimes\bigotimes_{v\in\Sigma_{F,f}}f_{k,v}
$$

with $f_{k,v}\in\mathcal{S}(F_v)$ for each finite place $v$, $f_v=1_{\mathcal{O}_{F_v}}$ for all but finitely many $v$, and $f_{k,\infty}\in\mathcal{S}(\mathbf{A}_{F,S_\infty})$ for each $1\le k\le m$, and complex numbers $c_1,\ldots,c_m$, such that $f=\sum_{1\le k\le m}c_k f_k$.

Since formation of the limit in (2.2.4.2) is $\mathbf{C}$-linear with respect to $f$, the existence of the limit is reduced to the case $f=f_k$ for some $1\le k\le m$, i.e. $f$ is of the form $f=f_\infty\otimes\bigotimes_{v\in\Sigma_{F,f}}f_v$, for $f_v$ the indicator function of some compact open subset $K_v\subset F_v$ for each $v\in S$, $S$ the minimal finite set of places containing all the Archimedean places of $F$, such that for every finite place $v\notin S$, $f_v=1_{\mathcal{O}_{F_v}}$.

In this special case, since each $f_v$ is unaffected by the dilation under the idele $\gamma(t)$ for each $t\in\mathbf{R}_{>0}$ in light of Lemma 2.2.4.1, we are further reduced to the case $S=S_\infty$, where the derivation operator $\partial_{\gamma}$ is the directional derivative along the continuous, hence smooth, $1$-parameter subgroup $\gamma:\mathbf{R}_{>0}\to\mathbf{A}_{F,S_\infty}$.

The Schwartz function space $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ is stable under directional derivation, since it is so under partial derivation, and the partial derivative operators $\partial_{x_i}$, for $x_i$ a choice of smooth coordinates on the real Euclidean space $\mathbf{A}_{F,S_\infty}$, are continuous with respect to the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$.

We now observe that the composition of $\gamma_\infty$ with each projection $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\to F_v^{\times}$ for each Archimedean place $v$, is a connected subgroup of $F_v^{\times}$, acting on $F_v$ by multiplication by a nonzero scalar $\gamma_v(t)\in F_v^{\times}$ for each $t\in\mathbf{R}_{>0}$.

The scalar $\gamma_v(t)$ is of the form $t^{\alpha_v}$, for $\alpha_v\in\mathbf{R}$ if $v$ is real, and for $\alpha_v\in\mathbf{C}$ for $v$ complex. We define

$$
\alpha(y):=\gamma_\infty(e^{y})\cdot x \tag{2.2.4.3}
$$

## PDF page 88

**88** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

a smooth curve in the Euclidean space $\mathbf{A}_{F,S_\infty}$, such that $\alpha(0)=x$.

We have:

$$
\lim_{y\to 0}\frac{f_\infty(\alpha(y))-f_\infty(\alpha(0))}{y}=\lim_{t\to 1}\frac{f_\infty(\gamma_\infty(t)x)-f_\infty(x)}{t-1} \tag{2.2.4.4}
$$

since $\lim_{y\to 0}\frac{e^{y}-1}{y}=1$.

Upon fixing smooth coordinates $x_v:\mathbf{R}\to\mathbf{R}^{r_1}\times\mathbf{C}^{r_2}\simeq\mathbf{A}_{F,S_\infty}$ for $v$ real, and holomorphic and anti-holomorphic $z_v,\bar z_v:\mathbf{C}\to\mathbf{R}^{r_1}\times\mathbf{C}^{r_2}\simeq\mathbf{A}_{F,S_\infty}$, for $v$ complex, we write the left side of (2.2.4.4) as:

$$
\lim_{y\to 0}\frac{f_\infty(\alpha(y))-f_\infty(\alpha(0))}{y}=\sum_{v\ \mathrm{real}}\alpha_v x_v\partial_{x_v}f_\infty(x)+\sum_{v\ \mathrm{complex}}\{(\partial_{z_v}+\partial_{\bar z_v})f_\infty(x)\,\mathrm{Re}(\alpha_v z_v)-i\,(-\partial_{z_v}+\partial_{\bar z_v})f_\infty(x)\,\mathrm{Im}(\alpha_v z_v)\} \tag{2.2.4.5}
$$

which exhibits the limits in (2.2.4.4) as existing and being valued in $\mathcal{S}(\mathbf{A}_{F,S_\infty})$, defining the linear operator $\partial_{\gamma_\infty}$, which is in turn exhibited as a finite linear combination of continuous linear endomorphisms of $\mathcal{S}(\mathbf{A}_{F,S_\infty})$.

We have just shown that the composition of $\partial_{\gamma}$ with the continuous linear operator $\pi_S:\mathcal{S}(\mathbf{A}_{F,S})\to\mathcal{S}(\mathbf{A}_F)$ from (2.1.4.5) is continuous for each finite $S$ containing all the Archimedean places of $F$. It follows, by Proposition 2.1.4.1, since $\mathcal{S}(\mathbf{A}_F)$ is a strict locally convex inductive limit of the $\mathcal{S}(\mathbf{A}_{F,S})$ as $S$ varies over the filtered set of finite subsets of $\Sigma_F$ containing $S_\infty$ (see [Scha, Ch.II,§6,pp.58-59]), that $\partial_{\gamma}:\mathcal{S}(\mathbf{A}_F)\to\mathcal{S}(\mathbf{A}_F)$ is continuous.

The foregoing implies that under the linear topological isomorphism:

$$
T:\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_{\iota}\mathcal{S}(\mathbf{A}_F^f)\to\mathcal{S}(\mathbf{A}_F)
$$

from (2.1.3.2) of Proposition 2.1.3.2(2), we have

$$
T\circ(\partial_{\gamma_\infty}\otimes\mathrm{id}_{\mathcal{S}(\mathbf{A}_F^f)})\circ T^{-1}=\partial_{\gamma} \tag{2.2.4.6}
$$

as linear endomorphisms of $\mathcal{S}(\mathbf{A}_F)$. Since $T$ and $T^{-1}$ are continuous, and $\partial_{\gamma_\infty}$, the directional derivative on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ along the continuous, hence smooth, $1$-parameter subgroup $\gamma_\infty$ induced by the composition $\gamma_\infty$ of $\gamma$ by the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$, is continuous, then so is $\partial_{\gamma}$.

The identity in (2.2.4.6) as $\mathbf{C}$-linear endomorphisms of $\mathcal{S}(\mathbf{A}_F)$, holds because the composition $\gamma_\infty$ of $\gamma$ with the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ remains injective by Lemma 2.2.4.1. $\square$

LEMMA 2.2.4.3 (Existence of directional derivatives - global adelic $\theta$-functions). *Let $f\in\mathcal{S}(\mathbf{A}_F)$ be a Schwartz-Bruhat function on $\mathbf{A}_F$. Let $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$ be a continuous $1$-parameter subgroup. The directional derivative $\partial_{\gamma}\Phi_F(f)$ exists, it is continuous, and we have*

$$
\Phi_F(\partial_{\gamma}f)=\partial_{\gamma}\Phi_F(f) \tag{2.2.4.7}
$$

as continuous functions on $C_F$.

PROOF. By linearity of both $\partial_{\gamma}$ and $\Phi_F$, we may and do assume $f=f_\infty\otimes\bigotimes_{v\in\Sigma_{F,f}}f_v$ for $f_\infty\in\mathcal{S}(\mathbf{A}_{F,S_\infty})$, $f_v\in\mathcal{S}(F_v)$ for all $v\in\Sigma_{F,f}$, and $f_v=1_{K_v}$ for a compact open subset $K_v\subset F_v$ for all finite places $v$ (see Proposition 2.1.3.2), with $K_v=\mathcal{O}_{F_v}$ for all but finitely many $v$.

We choose a continuous homomorphic section $\tau$ to the idelic norm, and we call $T:=\tau(\mathbf{R}_{>0})$ the closed (by Lemma ??) subgroup of $\mathrm{GL}_1(\mathbf{A}_F)$.

We denote by $T_\infty\subset\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ the image of $T$ under the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$. The subgroup $T_\infty$ is closed since it is the image of $\mathbf{R}_{>0}$ under the injective continuous group homomorphism induced by the section $\tau$ (see Lemma A.2.3.11).

Lemma 2.2.2.1(3) provides a fractional ideal $I_f\subset F$ such that, for all $g\in\mathrm{GL}_1(\mathbf{A}_F)$ and for $g_\infty\in\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ the image of $g$ under the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$, under the constraint $g_\infty\in T_\infty\cdot E_\infty$ (where $E_\infty$ is the image of the idelic fundamental domain $E_F^1$ from (A.2.3.14) under

## PDF page 89

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **89**

the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$), the following inequality holds:

$$
\sum_{\xi\in F^{\times}}\lvert f(\xi g)\rvert\le\sum_{\xi\in I_f-\{0\}}\lvert f_\infty(\xi g_\infty)\rvert. \tag{2.2.4.8}
$$

The fractional ideal $I_f$ depends on $f$ only through $\bigotimes_{v\in\Sigma_{F,f}}f_v$ (and it depends on the idelic fundamental domain $E_F^1\subset\mathrm{GL}_1(\mathbf{A}_F)^1$: see Remark 2.2.2.3). In particular, the two Schwartz-Bruhat functions $f$ and $\gamma(t)^*f$, the latter being the function $x\mapsto f(\gamma(t)x)$ on the adeles $\mathbf{A}_F$ of $F$ (where the idele $\gamma(t)$ acts on $\mathbf{A}_F$ continuously by left multiplication) share the same non-Archimedean component $\bigotimes_{v\in\Sigma_{F,f}}f_v$, and their Archimedean components are $f_\infty$, respectively $\gamma(t)^*f_\infty$. The latter is the function on $\mathbf{A}_{F,S_\infty}$ defined by $x_\infty\mapsto f_\infty(\gamma(t)x_\infty)$, where $\gamma(t)x_\infty$ is succint notation to denote the left multiplication by the projection of $\gamma(t)\in\mathrm{GL}_1(\mathbf{A}_F)$ onto $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$, on the element $x_\infty\in\mathbf{A}_{F,S_\infty}$.

For $t\ne 1$, the inequality in (2.2.4.8) therefore remains valid for

$$
\frac{\gamma(t)^*f-f}{t-1}-\partial_{\gamma}f \tag{2.2.4.9}
$$

replacing $f$, and correspondingly

$$
\frac{\gamma_\infty(t)^*f_\infty-f_\infty}{t-1}-\partial_{\gamma_\infty}f_\infty \tag{2.2.4.10}
$$

replacing $f_\infty$, with the same $I:=I_f$, since this fractional ideal provided by Lemma 2.2.2.1(3) qualifies for $\gamma(t)^*f$, $\partial_{\gamma}f$ and $f$ (its formation only depends on the non-Archimedean components of $\gamma(t)^*f$, $\partial_{\gamma}f$ and $f$ and on the idelic fundamental domain $E_F^1$, which in turn does not depend on $f$).

From (2.2.4.8) applied to (2.2.4.9) in the role of $f$ and (2.2.4.10) in the role of $f_\infty$, we have

$$
\left\lvert\frac{\Phi_F(\gamma(t)^*f)(g)-\Phi_F(f)(g)}{t-1}-\Phi_F(\partial_{\gamma}f)\right\rvert\le\sum_{\xi\in I-\{0\}}\left\lvert\frac{\gamma_\infty(t)^*f_\infty(\xi g_\infty)-f_\infty(\xi g_\infty)}{t-1}-\partial_{\gamma_\infty}f_\infty(\xi g_\infty)\right\rvert \tag{2.2.4.11}
$$

for all $g\in T\cdot E_F^1$, with $g_\infty\in T_\infty\cdot E_\infty$.

Since $f_\infty\in\mathcal{S}(\mathbf{A}_{F,S_\infty})$, its rapid decay at infinity ensures that uniformly over the compact subsets of $T_\infty\cdot E_\infty$, the series on the right side of (2.2.4.11) converges. We will now set out to proving this convergence assertion.

Since $f_\infty$ is smooth, the function, for $t\ne 1$

$$
u(t,g_\infty):=\frac{\gamma_\infty(t)^*f_\infty(g_\infty)-f_\infty(g_\infty)}{t-1}-\partial_{\gamma_\infty}f_\infty(g_\infty)
$$

extends to a continuous function over $\mathbf{R}_{>0}\times\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ vanishing at $t=1$ (note that continuity follows from uniform differentiability of Schwartz functions on Euclidean spaces, i.e. the incremental ratios converge uniformly), and the complex valued function $\psi$ over

$$
\mathbf{R}_{>0}\times\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})
$$

defined as

$$
\phi(t,y,g_\infty):=u(t,yg_\infty) \tag{2.2.4.12}
$$

is also continuous.

We now fix two compact intervals $[a,b]$, $[a',b']\subset\mathbf{R}_{>0}$, and assume $1\in(a,b)$. The function defined as

$$
\widetilde{\phi}(y):=\sup_{(t,g_\infty)\in[a,b]\times\tau([a',b'])\cdot\bar E_\infty}\lvert\phi(t,y,g_\infty)\rvert
$$

is continuous over $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ since $[a,b]\times\tau([a',b'])\cdot\bar E_\infty$ is compact Hausdorff and metrizable (for a continuous function $u:X\times Y\to\mathbf{C}$ with $X,Y$ metric spaces, and $Y$ compact, $\sup_{y\in Y}u(x,y)$ is a continuous function of $x\in X$).

## PDF page 90

**90** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

We now prove that for each integer $N\ge 1$ we can find a large enough compact subset $B\subset\mathbf{A}_{F,S_\infty}$ depending on $N$ such that for all $\xi\in I$ not contained in $B$

$$
\widetilde{\phi}(\xi)\le C_{B,N}\lVert\xi\rVert^{-N} \tag{2.2.4.13}
$$

for some constant $C_{B,N}> 0$.

To see this, we proceed as follows. The assignment $u:t\mapsto u(t,\cdot)$ is a continuous $1$-parameter family of Schwartz functions on the Euclidean space $\mathbf{A}_{F,S_\infty}$, i.e. it is a continuous map:

$$
u:\mathbf{R}_{>0}\to\mathcal{S}(\mathbf{A}_{F,S_\infty}).
$$

Here we have used Lemma 2.2.4.2 to deduce that $\partial_{\gamma_\infty}f_\infty$ is itself a Schwartz function.

Since $[a,b]$ is compact Hausdorff, so is $\mathcal{B}:=u([a,b])$, and hence $\mathcal{B}$ is bounded in $\mathcal{S}(\mathbf{A}_{F,S_\infty})$. The assignment

$$
p:u\mapsto\sup_{x_\infty\in\mathbf{A}_{F,S_\infty}}\lVert x_\infty\rVert^{N}\lvert u(x_\infty)\rvert
$$

is a continuous seminorm on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$, and hence $p(\mathcal{B})\subset[0,r]\subset\mathbf{R}$ for a real number $r\ge 0$.

There therefore exists a compact subset $B\subset\mathbf{A}_{F,S_\infty}$ such that:

$$
\sup_{x_\infty\in\mathbf{A}_{F,S_\infty}-B}\lvert u(t,x_\infty)\rvert\le r\lVert x_\infty\rVert^{-N}. \tag{2.2.4.14}
$$

From (2.2.4.14), since $r$ is independent of $t,y,g_\infty$ (reprising the notation from (2.2.4.12)) we deduce that

$$
\widetilde{\phi}(y)\le A_N\lVert y\rVert^{-N} \tag{2.2.4.15}
$$

for all $y\in\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ satisfying the largeness condition:

$$
y\notin(\gamma([a,b])\cdot\tau([a',b'])\cdot\bar E_\infty)^{-1}\cdot B \tag{2.2.4.16}
$$

with $A_N$ obtained from $r\lVert\gamma(t)yg_\infty\rVert^{-N}$ by maximizing with respect to $\gamma(t)g_\infty$ varying over the compact subset $\gamma([a,b])\cdot\tau([a',b'])\cdot\bar E_\infty$ (which, note, does not contain the origin of the Euclidean space $\mathbf{A}_{F,S_\infty}$).

We rename $(\gamma([a,b])\cdot\tau([a',b'])\cdot\bar E_\infty)^{-1}\cdot B$ as $B$, and $A_N$ as $C_{B,N}$. We have shown that for these choices of $B$ and $C_{B,N}$, (2.2.4.13) holds.

The discreteness of $I\subset\mathbf{A}_{F,S_\infty}$ ensures that $(I-\{0\})\cap B$ is finite. For $t\in[a,b]$ and $g_\infty\in E_\infty$, the sum in the right side of (2.2.4.11) is bounded above by

$$
\sum_{\xi\in(I-\{0\})\cap B}\left\lvert\frac{\gamma_\infty(t)^*f_\infty(\xi g_\infty)-f_\infty(\xi g_\infty)}{t-1}-\partial_{\gamma_\infty}f_\infty(\xi g_\infty)\right\rvert+C_{B,N}\sum_{\xi\in I-\{0\}:\xi\notin B}\lVert\xi\rVert^{-N}. \tag{2.2.4.17}
$$

By Proposition 2.2.1.3, the series $\sum_{\xi\in I-\{0\}:\xi\notin B}\lVert\xi\rVert^{-N}$ is absolutely convergent so long as we choose $N>[F:\mathbf{Q}]$. Since $I$ is discrete within $\mathbf{A}_{F,S_\infty}$, for every $\varepsilon>0$ we may choose a compact subset $B_\varepsilon\subset\mathbf{A}_{F,S_\infty}$ large enough so as to have:

$$
C_{B,N}\sum_{\xi\in I-\{0\}:\xi\notin(B_\varepsilon\cup B)}\lVert\xi\rVert^{-N}<\varepsilon/2. \tag{2.2.4.18}
$$

Since we will be wanting to let $t$ be arbitrarily close to $1$, we note that $B\cup B_\varepsilon$ is independent of $t\in[a,b]$. Continuity of $u(t,g_\infty)$ (which, recall, is implied by uniform differentiability of the Schwartz function $f_\infty$) now allows us to choose $\delta>0$ such that for all $t\in\mathbf{R}_{>0}$ satisfying $0<\lvert t-1\rvert<\delta$ we have

$$
\left\lvert\frac{\gamma_\infty(t)^*f_\infty(\xi g_\infty)-f_\infty(\xi g_\infty)}{t-1}-\partial_{\gamma_\infty}f_\infty(\xi g_\infty)\right\rvert\le\frac{\varepsilon}{2\lvert(I-\{0\})\cap(B\cup B_\varepsilon)\rvert}, \tag{2.2.4.19}
$$

which implies

$$
\sum_{\xi\in(I-\{0\})\cap(B_\varepsilon\cup B)}\left\lvert\frac{\gamma_\infty(t)^*f_\infty(\xi g_\infty)-f_\infty(\xi g_\infty)}{t-1}-\partial_{\gamma_\infty}f_\infty(\xi g_\infty)\right\rvert<\frac{\varepsilon}{2}. \tag{2.2.4.20}
$$

## PDF page 91

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **91**

Upon combining (2.2.4.17), (2.2.4.20) and (2.2.4.19), we have shown that for every $\varepsilon > 0$, there exists $\delta > 0$ such that for every $t\in\mathbf{R}_{>0}$ satisfying $0 < \lvert t-1\rvert < \delta$, we have:

$$
\left\lvert \frac{\Phi_F(\gamma(t)^*f)(g)-\Phi_F(f)(g)}{t-1}-\Phi_F(\partial_\gamma f)(g)\right\rvert < \varepsilon \tag{2.2.4.21}
$$

for all $g\in \tau([a',b'])\cdot E_F^1$.

This shows that

$$
\lim_{t\to 1}\frac{\Phi_F(f)(\gamma(t)g)-\Phi_F(f)(g)}{t-1} \tag{2.2.4.22}
$$

exists for all $g\in \tau([a',b'])\cdot E_F^1$, and it equals $\Phi_F(\partial_\gamma f)(g)$. Since $[a',b']\subset\mathbf{R}_{>0}$ is arbitrary, we see that the limit in (2.2.4.22) exists for all $g\in T\cdot E_F^1$ and the convergence is uniform on the compact subsets of $T\cdot E_F^1$, and hence for all $g\in\mathrm{GL}_1(\mathbf{A}_F)$ since the two continuous functions $\Phi_F(\gamma(t)^*f)$ and $\Phi_F(f)$ are invariant under the left-translation action by $F^{\times}$ on $\mathrm{GL}_1(\mathbf{A}_F)$ for all $t\in\mathbf{R}_{>0}$.

Since the limit in (2.2.4.22), if it exists, is the directional derivative $\partial_\gamma\Phi_F(f)$ as a function on $C_F$, we see that (2.2.4.7) holds pointwise over $C_F$. By Lemma 2.2.4.1 we know $\partial_\gamma f$ is a Schwartz-Bruhat function over $\mathbf{A}_F$, so $\Phi_F(\partial_\gamma f)$ is continuous as a function over $C_F$ by Lemma 2.2.2.1 and hence so is $\partial_\gamma\Phi_F(f)$. $\square$

*2.2.4.1. Directional derivatives and the global polar hyperplanes.* Throughout the remainder of this subsection we study the compatibility of formation of directional derivatives along continuous 1-parameter subgroups $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$, and formation of the two polar hyperplanes $\ker(\delta_0)$ and $\ker(\widehat{\delta}_0)$ on $\mathcal{S}(\mathbf{A}_F)$.

DEFINITION 2.2.4.4 (Global polar hyperplanes). Let $F$ be a number field.

We define:

$$
\mathcal{S}_0(\mathbf{A}_F) := \ker(\delta_0)\cap\ker(\widehat{\delta}_0) \tag{2.2.4.23}
$$

where $\delta_0:\mathcal{S}(\mathbf{A}_F)\to\mathbf{C}$ is the continuous functional $\delta_0(f):=f(0)$, and $\widehat{\delta}_0$ is its adelic Fourier transform, i.e. $\widehat{\delta}_0(f):=\widehat{f}(0)$.

We will be explaining the role of the two hyperplanes $\ker(\delta_0)$ and $\ker(\widehat{\delta}_0)$ in Chapter 3 (see Theorem 3.2.2.1 and Example 3.2.2.4).

LEMMA 2.2.4.5. *Let $F$ be a number field. Let $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$ be a continuous 1-parameter subgroup. Then:*

(1) *The continuous linear endomorphism*

$$
\partial_\gamma:\mathcal{S}(\mathbf{A}_F)\to\mathcal{S}(\mathbf{A}_F) \tag{2.2.4.24}
$$

*preserves the closed subspace $\mathcal{S}_0(\mathbf{A}_F)$.*

(2) *For*

$$
T:\mathcal{S}(\mathbf{A}_F)/\mathcal{S}_0(\mathbf{A}_F)\to\mathbf{C}\oplus\mathbf{C} \tag{2.2.4.25}
$$

*the linear isomorphism $(\delta_0,\widehat{\delta}_0)$, the induced linear map*

$$
\partial_\gamma:\mathcal{S}(\mathbf{A}_F)/\mathcal{S}_0(\mathbf{A}_F)\to\mathcal{S}(\mathbf{A}_F)/\mathcal{S}_0(\mathbf{A}_F) \tag{2.2.4.26}
$$

*satisfies:*

$$
T\circ\partial_\gamma\circ T^{-1} = \begin{pmatrix} 0 & 0 \\ 0 & -\alpha_\gamma \end{pmatrix} \tag{2.2.4.27}
$$

*where $\alpha_\gamma$ is the unique real number such that $\lvert\cdot\rvert_F\circ\gamma$, a smooth endomorphism of $\mathbf{R}_{>0}$, is of the form $t\mapsto t^{\alpha_\gamma}$.*

## PDF page 92

**92** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

(3) *For $f\in\mathcal{S}(\mathbf{A}_F)$, the pointwise limit*

$$
\lim_{t\to 1}\frac{1}{t-1}\left\{ \lvert\gamma(t)\rvert_F^{-1}\gamma(t)^*\widehat{f}-\widehat{f}\right\} \tag{2.2.4.28}
$$

*as functions on $\mathbf{A}_F$ (where $\gamma(t)^*u(x)=u(\gamma(t)^{-1}x)$ as functions on $\mathbf{A}_F$) exists and is given by*

$$
\lim_{t\to 1}\frac{1}{t-1}\left\{ \lvert\gamma(t)\rvert_F^{-1}\gamma(t)^*\widehat{f}-\widehat{f}\right\} = \widehat{\partial_\gamma f}, \tag{2.2.4.29}
$$

*so it belongs to $\mathcal{S}(\mathbf{A}_F)$. Explicitly, its value at any $x\in\mathbf{A}_F$ is equal to*

$$
\int_{\mathbf{A}_F} f(y)\overline{\psi}(xy)\left\{ -\alpha_\gamma+2\pi i\overline{\Lambda(\gamma'(1)xy)}\right\} \mathrm{d}\nu(y). \tag{2.2.4.30}
$$

REMARK 2.2.4.6. The mode of convergence of the limit in (2.2.4.28) is uniform on bounded subsets in $\mathcal{S}(\mathbf{A}_F)$, i.e. it converges in $\mathscr{L}_\beta(\mathcal{S}(\mathbf{A}_F))$. This is due to the fact that $\mathcal{S}(\mathbf{A}_F)$ is barrelled and complete, hence quasi-complete. Indeed, as $t$ varies over a compact neighborhood of $1$, the proof of (3) shows that

$$
\frac{1}{t-1}\left\{ \lvert\gamma(t)\rvert_F^{-1}\gamma(t)^*\widehat{f}-\widehat{f}\right\}
$$

is bounded in $\mathcal{S}(\mathbf{A}_F)$, being the image of a compact Hausdorff space under a continuous map, hence equicontinuous by Uniform Boundedness (see [Scha, Ch.III,§3.4,Corollary,p.82] and [Scha, Ch.III,Thm.4.2,p.83]).

PROOF. (1) and (3) : If $f\in\mathcal{S}(\mathbf{A}_F)$, we note that by definition

$$
(\partial_\gamma f)(0) = \lim_{t\to 1}\frac{f(\gamma(t)0)-f(0)}{t-1} = 0 \tag{2.2.4.31}
$$

since $\gamma(t)0 = 0$ within $\mathbf{A}_F$.

We now want to show that we have

$$
\widehat{\partial_\gamma f}(0) = 0.
$$

We will check this by proving (3) first, from which it follows by choosing $x = 0$. Indeed, (2.2.4.29) reads

$$
\widehat{(\partial_\gamma f)}(x) = \lim_{t\to 1}\frac{1}{t-1}\left\{ \lvert\gamma(t)\rvert_F^{-1}\widehat{f}(\gamma(t)^{-1}x)-\widehat{f}(x)\right\}
$$

which gives

$$
\widehat{(\partial_\gamma f)}(0) = \lim_{t\to 1}\frac{1}{t-1}\left\{ \lvert\gamma(t)\rvert_F^{-1}\widehat{f}(\gamma(t)^{-1}0)-\widehat{f}(0)\right\} = 0
$$

since $\gamma(t)^{-1}0 = 0$.

In the calculations that follow, setting $x = 0$ from the outset leads to substantial simplifications. The reader is welcome to assume $x = 0$ throughout, leading to the formula in (2.2.4.29) in this special case only.

We now assume $f\in\mathcal{S}(\mathbf{A}_F)$ is of the form

$$
f = f_\infty\otimes\bigotimes_{v\in\Sigma_{F,f}} f_v
$$

for $f_v\in\mathcal{S}(F_v)$ with $f_v = 1_{K_v}$ for $K_v\subset F_v$ a compact open subset for all $v\in\Sigma_{F,f}$, and $K_v = \mathcal{O}_{F_v}$ for all but finitely many $v\in\Sigma_{F,f}$. We further assume $f_\infty$ is *compactly supported*.

By [RV, Prop.5.6(iii)], we have

$$
\widehat{(\partial_\gamma f)}(x) = \int_{\mathbf{A}_F}(\partial_\gamma f)(y)\overline{\psi(xy)}\mathrm{d}\nu(y) = \left(\int_{\mathbf{A}_{F,S_\infty}}(\partial_{\gamma_\infty}f_\infty)(y_\infty)\prod_{v\in S_\infty}\overline{\psi_v(x_vy_v)}\mathrm{d}\nu_\infty(y_\infty)\right)\prod_{v\in\Sigma_{F,f}}\int_{F_v}f_v(x_v)\overline{\psi_v(x_vy_v)}\mathrm{d}\nu_v(y_v) \tag{2.2.4.32}
$$

for $\psi:\mathbf{A}_F\to\mathrm{U}(1)$ the standard additive character (see [RV, Ch.7,§7.1,p.253]), where $\nu$ is the additive global Tamagawa measure on $\mathbf{A}_F$ from Definition A.3.1.1, $\psi_v:F_v\to\mathrm{U}(1)$ is the standard additive character

## PDF page 93

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **93**

(see [RV, Ch.7,§7.1,pp.249-253]), $\nu_v$ is the additive local Tamagawa measure on $F_v$ for each $v\in\Sigma_F$, and $\nu_\infty := \bigotimes_{v\in S_\infty}\nu_v$.

We analyze the integral:

$$
\int_{\mathbf{A}_{F,S_\infty}}(\partial_{\gamma_\infty}f_\infty)(y_\infty)\prod_{v\in S_\infty}\overline{\psi_v(x_vy_v)}\mathrm{d}\nu_\infty(y_\infty) \tag{2.2.4.33}
$$

Let $[a,b]\subset\mathbf{R}_{>0}$ an arbitrary compact interval such that $1\in(a,b)$. We define $K := \gamma_\infty([a,b])\cdot\mathrm{supp}(f_\infty)\subset\mathbf{A}_{F,S_\infty}$. Since $\mathrm{supp}(f_\infty)$ is compact, so is $K$ as a subset of $\mathbf{A}_{F,S_\infty}$.

By Dominated Convergence, applied to a bounded absolutely $\nu_\infty$-integrable majorant to

$$
\lvert (f_\infty(\gamma_\infty(t)y_\infty)-f_\infty(y_\infty))/(t-1)\rvert
$$

for $y_\infty\in\mathrm{supp}(f_\infty)$ and $t\in[a,b]$ varying over a sequence tending to $1$ (which exists as a consequence of smoothness of $f_\infty$ over $\mathbf{A}_{F,S_\infty}$ and Hadamard's Lemma), we may write the integral in (2.2.4.33) as the following limit with $t$ varying through a sequence:

$$
\lim_{t\to 1}\frac{1}{t-1}\left\{ \int_{\mathbf{A}_{F,S_\infty}}f_\infty(\gamma_\infty(t)y_\infty)\prod_{v\in S_\infty}\overline{\psi_v(x_vy_v)}\mathrm{d}\nu_\infty(y_\infty)-\int_{\mathbf{A}_{F,S_\infty}}f_\infty(y_\infty)\prod_{v\in S_\infty}\overline{\psi_v(x_vy_v)}\mathrm{d}\nu_\infty(y_\infty)\right\}. \tag{2.2.4.34}
$$

Upon defining $\psi_\infty:\mathbf{A}_{F,S_\infty}\to\mathrm{U}(1)$ as $\psi_\infty := \prod_{v\in S_\infty}\psi_v$, this limit is the same as

$$
\lim_{t\to 1}\frac{1}{t-1}\left\{ \lvert\gamma_\infty(t)\rvert_\infty^{-1}\int_{\mathbf{A}_{F,S_\infty}}f_\infty(y_\infty)\prod_{v\in S_\infty}\overline{\psi_\infty(x_\infty\gamma_\infty(t)^{-1}y_\infty)}\mathrm{d}\nu_\infty(y_\infty)-\int_{\mathbf{A}_{F,S_\infty}}f_\infty(y_\infty)\prod_{v\in S_\infty}\overline{\psi_v(x_vy_v)}\mathrm{d}\nu_\infty(y_\infty)\right\}. \tag{2.2.4.35}
$$

By Lemma 2.2.4.1, we have $\lvert\gamma_\infty(t)\rvert_\infty = \lvert\gamma(t)\rvert_F$ for every $t\in\mathbf{R}_{>0}$, where $\lvert\cdot\rvert_\infty = \prod_{v\in S_\infty}\lvert\cdot\rvert_v$.

Upon combining (2.2.4.35) and (2.2.4.32), then by [RV, Prop.5.6(iii)] we have:

$$
\widehat{(\partial_\gamma f)}(x) = \lim_{t\to 1}\frac{1}{t-1}\left\{ \lvert\gamma(t)\rvert_F^{-1}\widehat{f}(\gamma(t)^{-1}x)-\widehat{f}(x)\right\} \tag{2.2.4.36}
$$

for each $x\in\mathbf{A}_F$ where again $t\to 1$ through a sequence, and therefore with $t\to 1$ in general. This proves (3) for the special class of $f$ considered above (especially with $f_\infty$ compactly supported).

Formation of both sides of (2.2.4.36) is $\mathbf{C}$-linear with respect to $f$. It follows that (2.2.4.36) holds for all Schwartz-Bruhat functions $f\in\mathcal{S}(\mathbf{A}_F)$ that are finite $\mathbf{C}$-linear combinations of functions of the form $f_\infty\otimes\bigotimes_{v\in\Sigma_{F,f}}f_v$, with $f_v\in\mathcal{S}(F_v)$ for every $v\in\Sigma_{F,f}$, and $f_v = 1_{K_v}$ for all finite places $v$ of $F$, with $K_v\subset F_v$ a compact open subset, and $K_v = \mathcal{O}_{F_v}$ for all but finitely many finite places, and $f_\infty$ with *compact support*.

The goal is to now show that formation of the limit

$$
\lim_{t\to 1}\frac{1}{t-1}\left\{ \lvert\gamma(t)\rvert^{-1}\widehat{f}(\gamma(t)^{-1}x)-\widehat{f}(x))\right\}
$$

is sequentially continuous in $f$ for each $x$. Since the linear span of the class of functions on which we have proved that (2.2.4.28) holds is sequentially dense in $\mathcal{S}(\mathbf{A}_F)$, sequential continuity of both sides of the identity at each $x$ will propagate the identity to the whole $\mathcal{S}(\mathbf{A}_F)$, proving (2.2.4.29) of (3) in general.

The expression in (2.2.4.28) is not well-suited to analyzing sequential continuity in $f$ at each $x$. Since it is a limit of integrals, our aim is to use the Dominated Convergence Theorem to rewrite it as a single integral so as to better understand its continuity properties in $f$.

Since

$$
\frac{\lvert\gamma(t)\rvert_F^{-1}\widehat{f}(\gamma(t)^{-1}x)-\widehat{f}(x)}{t-1} = \int_{\mathbf{A}_F}f(y)\left\{ \frac{\lvert\gamma(t)\rvert_F^{-1}\overline{\psi(\gamma(t)^{-1}xy)}-\overline{\psi(xy)}}{t-1}\right\} \mathrm{d}\nu(y) \tag{2.2.4.37}
$$

## PDF page 94

**94** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

for $t\neq 1$ by definition of the Fourier transform, and $f$ has rapid decay, to apply Dominated Convergence we aim to bound the integrand factor

$$
\frac{\lvert\gamma(t)\rvert_F^{-1}\overline{\psi(\gamma(t)^{-1}xy)}-\overline{\psi(xy)}}{t-1} \tag{2.2.4.38}
$$

for $t$ near $1$ and uniformly in $y\in\mathbf{A}_F$ with each fixed $x$ (we will even obtain such a bound with uniformity in $x$).

We have

$$
\frac{\lvert\gamma(t)\rvert_F^{-1}\overline{\psi(\gamma(t)^{-1}xy)}-\overline{\psi(xy)}}{t-1} = \left\{ \frac{\lvert\gamma(t)\rvert_F^{-1}-1}{t-1}\overline{\psi(\gamma(t)^{-1}xy)}\right\}+\frac{\overline{\psi(\gamma(t)^{-1}xy)}-\overline{\psi}(xy)}{t-1} \tag{2.2.4.39}
$$

with $\lvert\overline{\psi(\gamma(t)^{-1}xy)}\rvert = 1$, it is enough to bound the function

$$
\frac{\psi(\gamma(t)^{-1}xy)-\psi(xy)}{t-1} \tag{2.2.4.40}
$$

for $t$ near $1$ uniformly with respect to $y$.

We can rewrite this difference quotient as

$$
\frac{\phi(t)-\phi(1)}{t-1}
$$

where $\phi(t) := \psi(\gamma(t^{-1})xy)-\psi(xy) = e^{2\pi i\Lambda(\gamma(t^{-1})xy)}$ where $\Lambda(u) = \sum_{v\in S_\infty}\Lambda_v(u_v)$, for $\Lambda_v$ the standard local additive character at $v$ (see Remark A.3.2.5).

We have

$$
\frac{\phi(t)-\phi(1)}{t-1} = \frac{1}{t-1}\int_1^t\phi'(u)\,\mathrm{d}u = \int_0^1\phi'(1+u(t-1))\,\mathrm{d}u.
$$

We compute (for $v\neq 0$)

$$
\phi'(v) = 2\pi i\,e^{2\pi i\Lambda(\gamma(v^{-1})xy)}\Lambda\left(\frac{\mathrm{d}}{\mathrm{d}v}(\gamma(v^{-1}))xy\right) = 2\pi i\,e^{2\pi i\Lambda(\gamma(v^{-1})xy)}\Lambda\left(\frac{\gamma'(v^{-1})}{-v^2}xy\right)
$$

and so

$$
\lvert\phi'(v)\rvert \le 2\pi\left\lvert\Lambda\left(\frac{\gamma'(v^{-1})}{-v^2}xy\right)\right\rvert \le 2\pi C\lVert x\rVert\lVert y\rVert\frac{\lVert\gamma'(v^{-1})\rVert}{v^2} \tag{2.2.4.41}
$$

for some constant $C > 0$ (via continuity of $\Lambda$), for $v = 1+u(t-1)$ with $0\le u\le 1$ and $-1/2\le t-1\le 1/2$ we have $1/2\le v\le 3/2$, and hence

$$
\lvert\phi'(v)\rvert \le 2\pi\left\lvert\Lambda\left(\frac{\gamma'(v^{-1})}{-v^2}xy\right)\right\rvert \le 2\pi C'\lVert x\rVert\lVert y\rVert \tag{2.2.4.42}
$$

where the constant $C'$ is $4C\max_{v\in[1/2,3/2]}\lVert\gamma'(v^{-1})\rVert$.

It follows that the function from (2.2.4.38) is bounded above by $u(x,y) := 2\pi C'\lVert x\rVert\lVert y\rVert$, and so by Dominated Convergence (since $f\in\mathcal{S}(\mathbf{A}_F)$) applied to the integral in (2.2.4.37), we deduce that we can exchange the order of formation of the limit as $t\to 1$ and of the integral, to obtain

$$
\lim_{t\to 1}\int_{\mathbf{A}_F}f(y)\left\{ \frac{\lvert\gamma(t)\rvert_F^{-1}\overline{\psi(\gamma(t)^{-1}xy)}-\overline{\psi(xy)}}{t-1}\right\} \mathrm{d}\nu(y) = \int_{\mathbf{A}_F}f(y)\lim_{t\to 1}\left\{ \frac{\lvert\gamma(t)\rvert_F^{-1}\overline{\psi(\gamma(t)^{-1}xy)}-\overline{\psi(xy)}}{t-1}\right\} \mathrm{d}\nu(y).
$$

The right side is finite and it equals

$$
\int_{\mathbf{A}_F}f(y)\overline{\psi}(xy)\left\{ -\alpha_\gamma+2\pi i\overline{\Lambda(\gamma'(1)xy)}\right\} \mathrm{d}\nu(y),
$$

(where $\alpha_\gamma$ is the unique real number such that $\lvert\gamma(t)\rvert_F = t^{\alpha_\gamma}$ for all $t\in\mathbf{R}_{>0}$) which is visibly sequentially continuous in $f$.

## PDF page 95

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **95**

Since the adelic Fourier transform is a linear topological automorphism of $\mathcal{S}(\mathbf{A}_F)$ and $\partial_\gamma$ is a continuous
linear endomorphism of $\mathcal{S}(\mathbf{A}_F)$ by Lemma 2.2.4.2, the left side of (2.2.4.36) is also continuous as a $\mathbf{C}$-linear
endomorphism on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$, and hence we see that both sides of (2.2.4.36) are sequentially continuous $\mathbf{C}$-linear
endomorphisms of $\mathcal{S}(\mathbf{A}_F)$, which agree on a sequentially dense $\mathbf{C}$-linear subspace. We deduce that the identity
in (2.2.4.36) holds for all $f\in\mathcal{S}(\mathbf{A}_F)$. This proves (3) and finishes the proof of (1).

(2) : From (1) we know $\delta_0(\partial_\gamma f)=0$. From (2.2.4.29) we deduce $\widehat{\delta}_0(\partial_\gamma f)=-\alpha_\gamma\widehat{\delta}_0(f)$.
$\square$

**2.2.5. The homogeneous $\theta$-function operators $\Phi_{F,\omega}:\mathcal{S}(\mathbf{A}_F)\to C(C_F/C_F^1)$.** In this subsection
we define a version of the $\theta$-function operator $\Phi_F$ which is $\omega$-homogeneous with respect to the continuous
left-translation action by $C_F^1$, the closed subgroup of $C_F$ of norm-one idele classes.

We recall that we choose on $C_F^1$ the Haar measure $\overline{\mu}_1$ induced as per Theorem D.1.2.1 by the choices of
the counting measure on $F^{\times}$ and the Haar measure $\mu_1$ on $\mathrm{GL}_1(\mathbf{A}_F)^1$ constructed in Definition A.3.2.1.

The Haar measure $\mu_1$ was constructed upon choosing a continuous homomorphic section to the idelic
norm. The Haar measure $\overline{\mu}_1$, however, does not depend on such choice, but only on the volume it assigns to
the compact Hausdorff abelian group $C_F^1$.

DEFINITION 2.2.5.1 ($\omega$-homogeneous global adelic $\theta$-functions). Let $F$ be a number field, $\omega\in\widehat{C_F^1}$ a
continuous character. We define the $\mathbf{C}$-linear operator

$$
\Phi_{F,\omega}:\mathcal{S}(\mathbf{A}_F)\to C(C_F) \tag{2.2.5.1}
$$

by

$$
\Phi_{F,\omega}(f)(g):=\int_{C_F^1}\Phi_F(f)(hg)\omega(h)\,\mathrm{d}\overline{\mu}_1(h) \tag{2.2.5.2}
$$

for $f\in\mathcal{S}(\mathbf{A}_F)$ and $g\in C_F$. We refer to $\Phi_{F,\omega}(f)$ as the $\omega$-homogeneous global adelic $\theta$-function of $f$.

The (absolute) convergence of the above integral is immediate from the compactness of $C_F^1$ but the
continuity in $g$ requires an argument since $f$ is not compactly supported on $\mathrm{GL}_1(\mathbf{A}_F)$ (unless $f=0$). This
continuity is part of Lemma 2.2.5.2(2).

2.2.5.1. *Properties of the homogeneous $\theta$-function operator.* We prove that formation of $\Phi_{F,\omega}$ is linear and
valued in continuous functions on $C_F$, $\omega$-homogeneous under the left-translation action of $C_F^1$ on $C(C_F)$.

LEMMA 2.2.5.2. *Let $f\in\mathcal{S}(\mathbf{A}_F)$ be a Schwartz-Bruhat function, and $\omega\in\widehat{C_F^1}$ a continuous character.*
*Then, upon denoting $\widetilde{\omega}:\mathrm{GL}_1(\mathbf{A}_F)^1\to \mathrm{U}(1)$ the composition of $\omega$ with the continuous quotient homomorphism*
$\mathrm{GL}_1(\mathbf{A}_F)^1\to C_F^1$:

(1) *The integral*

$$
\int_{\mathrm{GL}_1(\mathbf{A}_F)^1}f(hg)\widetilde{\omega}(h)\,\mathrm{d}\mu_1(h) \tag{2.2.5.3}
$$

*is absolutely convergent and its formation is continuous as a function of $g\in\mathrm{GL}_1(\mathbf{A}_F)$. The resulting*
*continuous function is $\widetilde{\omega}$-homogeneous under the left-translation action by $\mathrm{GL}_1(\mathbf{A}_F)^1$.*

(2) *We have, as functions of $g\in\mathrm{GL}_1(\mathbf{A}_F)$:*

$$
\Phi_{F,\omega}(f)(g)=\int_{\mathrm{GL}_1(\mathbf{A}_F)^1}f(hg)\widetilde{\omega}(h)\,\mathrm{d}\mu_1(h). \tag{2.2.5.4}
$$

*In particular, $\Phi_{F,\omega}(f)$ is a continuous function on $C_F$.*

PROOF. (1) : By (2.2.2.3) from Lemma 2.2.2.1, we have, for every $g\in C_F$ and $g'\in\mathrm{GL}_1(\mathbf{A}_F)$ any lift of $g$
to $\mathrm{GL}_1(\mathbf{A}_F)$, whose image in $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ under the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$

## PDF page 96

**96** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

we denote $g_\infty$:

$$
\sum_{\xi\in F^{\times}}\lvert f(\xi g')\rvert\le\sum_{\xi\in I_f-\{0\}}\lvert f_\infty(\xi g_\infty)\rvert \tag{2.2.5.5}
$$

where $I_f\subset F$ is a fractional ideal depending on $f$, and $f_\infty\in\mathcal{S}(\mathbf{A}_{F,S_\infty})$ is the Schwartz function on the
Euclidean space $\mathbf{A}_{F,S_\infty}$ that serves as the Archimedean component of $f$.

We consider the idelic fundamental domain $E_F^1$ from (A.2.3.14) for the continuous $F^{\times}$-action on $\mathrm{GL}_1(\mathbf{A}_F)^1$.
The subset $E_F^1\subset\mathrm{GL}_1(\mathbf{A}_F)^1$ is, recall from (A.2.3.16), of the form

$$
E=(E_0\times\widehat{\mathcal O}_F^{\times})\cup(g_{2,\infty}E_0\times g_{2,f}\widehat{\mathcal O}_F^{\times})\cup\ldots\cup(g_{h_F,\infty}E_0\times g_{h_F,f}\widehat{\mathcal O}_F^{\times})\subset\mathrm{GL}_1(\mathbf{A}_F)^1 \tag{2.2.5.6}
$$

where $g_i=(g_{i,\infty},g_{i,f})$ is an idele for each integers $1\le i\le h_F$ with $g_1=1$ and $\lvert g_i\rvert_F=1$ for every $1\le i\le h_F$.

Since the measurable function $\sum_{\xi\in F^{\times}}\lvert f(\xi g')\rvert$ on $\mathrm{GL}_1(\mathbf{A}_F)$ is $F^{\times}$-invariant and continuous, being the
series in the right side of (2.2.5.5) convergent uniformly on the compact subsets of $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$, the integral

$$
\int_{C_F^1}\sum_{\xi\in F^{\times}}\lvert f(\xi g')\rvert\,\mathrm{d}\overline{\mu}_1(g) \tag{2.2.5.7}
$$

where $\overline{\mu}_1$ is the unique Haar measure on $C_F^1$ prescribed by Theorem D.1.2.1 by the choices of the counting
measure as the Haar measure on $F^{\times}$, and $\mu_1$ as the Haar measure on $\mathrm{GL}_1(\mathbf{A}_F)^1$ from Definition A.3.2.1,
under the canonical isomorphism of abelian topological groups $C_F^1\simeq\mathrm{GL}_1(\mathbf{A}_F)^1/F^{\times}$.

The integral in (2.2.5.7) equals

$$
\int_{E_F^1}\sum_{\xi\in F^{\times}}\lvert f(\xi g')\rvert\,\mathrm{d}\mu_1(g') \tag{2.2.5.8}
$$

by Proposition D.1.2.4 (see also [Bou-II, INT VII.52,§3,Thm.4(c)], applied to $n=1$, since the action of $F^{\times}$
on $\mathrm{GL}_1(\mathbf{A}_F)^1$ is free, and to $k(g)=\sum_{\xi\in F^{\times}}\lvert f(\xi g')\rvert$ as a function of $g\in\mathrm{GL}_1(\mathbf{A}_F)^1/F^{\times}$, which is measurable
and integrable over the compact quotient $\mathrm{GL}_1(\mathbf{A}_F)^1/F^{\times}$, being $k$ continuous). Since $E_F^1$ is relatively compact
by Lemma A.2.3.8(1), and the function $g'\mapsto\sum_{\xi\in F^{\times}}\lvert f(\xi g')\rvert$ is continuous on $\mathrm{GL}_1(\mathbf{A}_F)^1$, the integral (2.2.5.8)
is finite, proving the absolute convergence of the integral (2.2.5.3) in light of Lemma D.1.2.3 (see also [DE,
Cor.1.5.4]). By Dominated Convergence, formation of the integral in (2.2.5.3) is continuous with respect to
$g\in C_F$.

By invariance of the Haar measure $\mu_1$ on $\mathrm{GL}_1(\mathbf{A}_F)$, formation of the continuous function on $\mathrm{GL}_1(\mathbf{A}_F)$
whose value at $g\in\mathrm{GL}_1(\mathbf{A}_F)$ is given by the integral in (2.2.5.3), is $\widetilde{\omega}$-homogenous with respect to the left
translation action by $\mathrm{GL}_1(\mathbf{A}_F)^1$.

We verify this explicitly. We note that by $hg$ within the integral over $C_F^1$ defining $\Phi_{F,\omega}(f)$ in (2.2.5.2), we
mean the image of $g\in\mathrm{GL}_1(\mathbf{A}_F)$ into $C_F$, translated by $h^{-1}$ on the left using the continuous left-translation
action of $C_F^1$ on $C_F$, being $C_F^1$ a subgroup of $C_F$. In particular, for each $g\in\mathrm{GL}_1(\mathbf{A}_F)$, $\Phi_F(f)(hg)$ makes
sense for every $h\in C_F^1$ as a function of $g\in\mathrm{GL}_1(\mathbf{A}_F)$ invariant under the left-translation action of $F^{\times}$ on
$\mathrm{GL}_1(\mathbf{A}_F)$.

## PDF page 97

**2.2. GLOBAL ADELIC $\theta$-FUNCTIONS** · **97**

By invariance of the Haar measure $\overline{\mu}_1$, we have that for any $h_0\in C_F^1$ and any choice of lift $\widetilde{h}_0\in\mathrm{GL}_1(\mathbf{A}_F)^1$
of $h_0$, and $\widetilde{h}$ of $h\in C_F^1$, and any fixed choice $\chi\in\widehat{C_F}$ of continuous character whose restriction to $C_F^1$ is $\omega$:

$$
\begin{aligned}
\Phi_{F,\omega}(f)(\widetilde{h}_0^{-1}g)&=\int_{\mathrm{GL}_1(\mathbf{A}_F)^1}f(\widetilde{h}_0^{-1}\widetilde{h}g)\chi(\widetilde{h})\,\mathrm{d}\mu_1(\widetilde{h})\\
&=\chi(\widetilde{h}_0)\int_{\mathrm{GL}_1(\mathbf{A}_F)^1}f(\widetilde{h}g)\chi(\widetilde{h})\,\mathrm{d}\mu_1(\widetilde{h})\\
&=\omega(h_0)\int_{C_F^1}\Phi_F(f)(hg)\omega(h)\,\mathrm{d}\overline{\mu}_1(h)\\
&=\omega(h_0)\Phi_{F,\omega}(f)(g)
\end{aligned}
$$

where we have used Theorem D.1.2.1 to justify both the first and last of the above identities, valid for all
$g\in\mathrm{GL}_1(\mathbf{A}_F)$. Since $\Phi_F(f)$ is $F^{\times}$-invariant, as a function on $\mathrm{GL}_1(\mathbf{A}_F)$, so is $\Phi_{F,\omega}(f)$, and hence $\Phi_{F,\omega}(f)(\widetilde{h}_0^{-1}g)$
only depends on $\widetilde{h}_0^{-1}g$ through the image of this element of $\mathrm{GL}_1(\mathbf{A}_F)$ in $C_F$, which is $h_0^{-1}g$. We have shown
that we have:

$$
\Phi_{F,\omega}(f)(h_0^{-1}g)=\omega(h_0)\Phi_{F,\omega}(f)(g)
$$

for all $g\in\mathrm{GL}_1(\mathbf{A}_F)$, and hence, $\Phi_{F,\omega}(f)$ is, as a continuous function on $C_F$, $\omega$-homogeneous under the
continuous left-translation action by $C_F^1$ on $C(C_F)$.

(2) : By (1) and Theorem D.1.2.1 (see also [DE, Thm.1.5.3]), the identity in (2.2.5.4) holds for every
$g\in C_F$, and since both sides are continuous functions of $g\in C_F$, it holds as continuous functions on $C_F$. $\square$

2.2.5.2. *Decay estimates over $C_F/C_F^1$.* Lemma 2.2.5.2(1) justifies the terminology “$\omega$-homogeneous” from
Definition 2.2.5.1.

We have yet to collect the global adelic $\theta$-functions into a $\mathbf{C}$-linear space and endow it with a Hausdorff
locally convex topology, and with this aim in mind we construct the $\omega$-homogeneous $\theta$-functions directly first,
proving their properties below.

REMARK 2.2.5.3. Lemma 4.3.3.1 from Chapter 3 provides a systematic method to produce elements in
appropriate Hausdorff locally convex topological $\mathbf{C}$-vector spaces equipped with a suitable continuous action
of a compact Hausdorff abelian group $G$, that are $\omega$-homogeneous, for a fixed choice of continuous character
$\omega\in\widehat{G}$.

In this subsection we provide an analog of the estimates from Theorem 2.2.3.4.

THEOREM 2.2.5.4 (Estimates over the idele classes - II). *We let $f\in\mathcal{S}(\mathbf{A}_F)$ be a Schwartz-Bruhat function,*
*and $\omega\in\widehat{C_F^1}$ a continuous character. The function $\Phi_{F,\omega}(f)$ on $C_F$ satisfies the following conditions:*

(1) *$\Phi_{F,\omega}(f)$ is a continuous function on $C_F$, $\omega$-homogeneous under the left translation action by $C_F^1$.*

(2) *It satisfies the following growth condition: for every integer $N\ge 0$, there exists a real number $C_N>0$*
*depending on $N$ and $f$, such that for every $g\in C_F$, we have*

$$
\lvert\Phi_{F,\omega}(f)(g)\rvert\le C_N\lvert g\rvert_F^{-N} \tag{2.2.5.9}
$$

*as $\lvert g\rvert_F\to +\infty$. For every integer $N\ge 0$, there exists a real number $C_N>0$ depending on $N$ and $f$, such*
*that*

$$
\lvert\Phi_{F,\omega}(f)(g)-(\lvert g\rvert_F^{-1}\overline{\mu}_1(C_F^1)\widehat{f}(0)-\overline{\mu}_1(C_F^1)f(0))\delta_\omega\rvert\le C_N\lvert g\rvert_F^N \tag{2.2.5.10}
$$

*as $\lvert g\rvert_F\to 0$, where $\delta_\omega=0$ if $\omega$ is non-trivial on $C_F^1$, and $\delta_\omega=1$ if $\omega$ is trivial on $C_F^1$.*

(3) *For any continuous 1-parameter subgroup $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$, we have:*

$$
\Phi_{F,\omega}(\partial_\gamma f)=\partial_\gamma\Phi_{F,\omega}(f). \tag{2.2.5.11}
$$

## PDF page 98

**98** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

*In particular, $\Phi_{F,\omega}(f)$, composed with the quotient $\mathrm{GL}_1(\mathbf{A}_F)\to C_F$, is a smooth in the Archimedean*
*directions.*

(4) *If either $f(0)=\widehat{f}(0)=0$ or $\omega|_{C_F^1}$ is non-trivial, then for every integer $N\ge 0$, there exists a real number*
*$C_N>0$ depending on $N$ and $f$, such that*

$$
\lvert\Phi_{F,\omega}(f)(g)\rvert\le C_Ne^{-N\lvert\log\lvert g\rvert_F\rvert} \tag{2.2.5.12}
$$

*as $\lvert\log\lvert g\rvert_F\rvert\to +\infty$. In particular, $\overline{\omega}\Phi_{F,\omega}(f)$, as a function of $\log\lvert g\rvert_F$, is a Schwartz function on $\mathbf{R}$ with*
*exponential decay at infinity, together with all of its derivatives.*

(5) *Let $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_F)$ be a bounded subset. For every integer $N\ge 0$, there exist real numbers $C_{\mathcal{B},N},T_{\mathcal{B},N}>0$,*
*such that (2.2.5.9), (2.2.5.10), (2.2.5.11), (2.2.5.12), hold with $C_N=C_{\mathcal{B},N}$ and for all $\log\lvert g\rvert_F>T_{\mathcal{B},N}$,*
*respectively $\log\lvert g\rvert_F^{-1}>T_{\mathcal{B},N}$, respectively $\lvert\log\lvert g\rvert_F\rvert>T_{\mathcal{B},N}$, and for all $f\in\mathcal{B}$.*

(6) *For every integer $N\ge 0$, the assertions in (5) all hold with $T_{\mathcal{B},N}=1$, upon possibly replacing the constant*
*$C_{\mathcal{B},N}>0$ with a larger, still uniform, constant.*

PROOF. Parts (1), (2), and (5) follow from Lemma 2.2.5.2 and Theorem 2.2.3.4 since $C_F^1$ is compact
Hausdorff and $\overline{\mu}_1$ is Radon, hence finite on $C_F^1$, and integration over $C_F^1$ preserves the growth conditions from
(2.2.3.4) and (2.2.3.5), from which (4) follows.

(3) : We use Lemma 2.2.4.3 to prove (2.2.5.11) to show that $\partial_\gamma$ commutes with integration over $C_F^1$ with
respect to the finite Radon measure $\overline{\mu}_1$. More specifically, we need to prove that for each $g\in C_F$ and $t$ varying
in a compact neighborhood $[a,b]$ of $1$

$$
\frac{\Phi_F(f)(\gamma(t^{-1})gh)\omega(h)-\Phi_F(f)(\gamma(t^{-1})gh)\omega(h)}{t-1} \tag{2.2.5.13}
$$

as a function of $h\in C_F^1$ (a compact space) is bounded by a constant independent of $t$ (but possibly depending
on $g$) for all $t\in[a,b]$, $t\ne 1$. This will justify the use of Dominated Convergence to pass the limit in $t$ of
(2.2.5.13) through the $\overline{\mu}_1$-integral over $C_F^1$.

We have the inequality

$$
\left\lvert\frac{\Phi_F(\gamma(t^{-1})gh)\omega(h)-\Phi_F(gh)\omega(h)}{t-1}\right\rvert\le\sup_{t_0\in[a,b]}\left\lvert\frac{\mathrm{d}}{\mathrm{d}t}\Phi_F(\gamma(t^{-1})gh)\right\rvert_{t=t_0} \tag{2.2.5.14}
$$

with

$$
\frac{\mathrm{d}}{\mathrm{d}t}\Phi_F(\gamma(t^{-1})gh)|_{t=t_0}=\frac{1}{t_0}\partial_\gamma\Phi_F(f)(\gamma(t_0^{-1})gh)=\frac{1}{t_0}\Phi_F(\partial_\gamma(f))(\gamma(t_0^{-1})gh) \tag{2.2.5.15}
$$

by Lemma 2.2.4.3. That same lemma gives that $\Phi_F(\partial_\gamma f)$ is continuous over $C_F$. It follows that as $(t_0,h)$
varies in the compact $[a,b]\times C_F^1$ the right side in (2.2.5.14) is bounded above by a positive real number $A$
(dependent on $g$). By varying $\gamma$, $\Phi_{F,\omega}(f)$ composed back to $\mathrm{GL}_1(\mathbf{A}_F)$ is a smooth function in the Archimedean
directions (note that a general derivative at a point along a 1-parameter subgroup $\gamma$ can be computed in terms
of the derivative along $\gamma$ at 1 for a translate of the function). This finishes the proof of (3).

(4) : From (2) it follows that since the idelic norm is a submersion $\Phi_{F,\omega}$ is smooth as a function of $\log\lvert g\rvert_F$
and the growth condition in (2.2.5.12) implies that $\Phi_{F,\omega}(f)$ decays faster than any positive integer power of
$e^{-\lvert\log\lvert g\rvert_F\rvert}$, and so do its derivatives by repeated use of (2.2.5.11).

(6) : The assertion follows from Theorem 2.2.3.4(5), by replacing $C_{\mathcal{B},N}$ in that result with its product
against the $\overline{\mu}_1$-volume of $C_F^1$.

$\square$

**2.3. $S$-local adelic $\theta$-functions**

Let $F$ be a number field. Throughout this section, we fix a finite set $S$ of places containing all of the
Archimedean places of $F$. We refer the reader to §A.1.5 of Appendix A, on $S$-local adeles, ideles and class
groups, and the $S$-local analogs of the respective fundamental domains within $\mathbf{A}_F$ and $\mathrm{GL}_1(\mathbf{A}_F)$.

## PDF page 99

**2.3. S-LOCAL ADELIC $\theta$-FUNCTIONS** · **99**

We further refer the reader to Definition A.3.4.1 for the construction of the $S$-local additive and multiplicative Tamagawa measures $\nu_S$ on $\mathbf{A}_{F,S}$, $\mu_S$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})$, $\overline{\mu}_S$ on $C_{F,S}$, as well as $\mu_{S,1}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$ and $\overline{\mu}_{S,1}$ on $J^1_{F,S}$.

Recall that we denote by $\mathbf{A}_{F,S}$ the product $\prod_{v\in S}F_v$, where $F_v$ is the additive topological group of the local field $F_v$.

The Hausdorff locally compact abelian group $\mathrm{GL}_1(\mathbf{A}_{F,S})$ is therefore isomorphic to the product $\prod_{v\in S}F_v^{\times}$, on which the $S$-units $\mathcal{O}_{F,S}^{\times}$ acts properly and freely as a discrete closed subgroup. The quotient is denoted by $J_{F,S}$, a Hausdorff locally compact abelian group which, equipped with the proper continuous homomorphism $\lvert\cdot\rvert_{F,S}:J_{F,S}\to\mathbf{R}_{>0}$, in particular, its kernel $J^1_{F,S}$ is compact.

In the previous sections we studied the “global averaging” of Schwartz-Bruhat functions on the adeles $\mathbf{A}_F$ over the orbits in $\mathrm{GL}_1(\mathbf{A}_F)$ of the $F^{\times}$-action, leading to the global adelic $\theta$-functions of Definition 2.2.3.1. In this section, we define $S$-local analogs of the $\theta$-function operators $\Phi_F$ and $\Phi_{F,\omega}$, for $\omega$ now a continuous character of $J^1_{F,S}$.

The reason we seek $S$-local analogues is as follows. Eventually we will collect the global adelic $\theta$-functions discussed so far into a topological vector space, and study several large quotients of that space (for example, proving that such quotients admit Schauder bases with certain good properties for later use, to compute traces). The study of the topological vector spaces of global $\theta$-functions rests on the following principle: we “exhaust” them by more manageable $S$-local analogs, where explicit constructions are possible and several additional tools available. One illustration of this is that smooth compactly supported functions on $\mathrm{GL}_1(\mathbf{A}_F)$ do *not* extend by zero to global Schwartz-Bruhat functions on $\mathbf{A}_F$ (the ideles have additive measure zero within the adeles), but they do at the $S$-local level.

We further note that there is a relation between continuous characters of $C^1_F$ and of $J^1_{F,S}$, as will be discussed in the next Chapter. For $\omega\in\widehat{C^1_F}$, we may restrict $\omega$ to $C^1_{F,S}$, where $C_{F,S}$ is the quotient of $\mathrm{GL}_1(\mathbf{A}_{F,S})\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v}^{\times}$ by the diagonal action of the $S$-units. For $S$ large enough so as to have $\mathrm{Pic}(\mathcal{O}_{F,S})=1$, we have that the continuous injective open group homomorphism $C_{F,S}\to C_F$ is an isomorphism of Hausdorff locally compact abelian groups. Clearly $J_{F,S}$ is also the quotient of $C_{F,S}$ by the compact Hausdorff closed subgroup defined as the image in $C_{F,S}$ of $\Gamma:=\{1\}\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v}^{\times}$.

If $\omega$ is unramified away from $S$, i.e. the restriction of $\omega$ to $\mathcal{O}_{F_v}^{\times}$ is trivial for all $v\notin S$, then $\omega$ is $\Gamma$-invariant, and it uniquely determines a continuous character of $J^1_{F,S}$. Conversely, a continuous character of $J^1_{F,S}$ uniquely determines a continuous character of $C^1_{F,S}$, which for $S$ large enough so as to have $\mathrm{Pic}(\mathcal{O}_{F,S})=1$ uniquely extends to a continuous character of $C^1_F$ that is unramified outside $S$.

**2.3.1. $S$-local $\theta$-function operators.** In this section, we study $S$-local analogs of the $\theta$-function operators $\Phi_F$ and $\Phi_{F,\omega}$.

NOTATION 2.3.1.1. For $F$ a number field, and $S$ a finite set of places of $F$ containing all the Archimedean places, we will be denoting by $S_f$ the intersection:

$$
S_f:=\Sigma_{F,f}\cap S
$$

the finite set of all the finite places of $F$ contained in $S$.

DEFINITION 2.3.1.1 ($S$-local adelic $\theta$-functions). Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places of $F$. We define:

$$
\Phi_{F,S}:\mathcal{S}(\mathbf{A}_{F,S})\to C(\mathrm{GL}_1(\mathbf{A}_{F,S})) \tag{2.3.1.1}
$$

to be the linear operator determined by the assignment, for every Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_{F,S})$:

$$
\Phi_{F,S}(f)(g):=\sum_{\xi\in\mathcal{O}_{F,S}^{\times}}f(\xi g) \tag{2.3.1.2}
$$

## PDF page 100

**100** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

as functions of $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$. We refer to $\Phi_{F,S}(f)$ as the $S$-local adelic $\theta$-function.

**2.3.1.1. *Estimates over $J_{F,S}$.*** A consequence of the Proposition below is that indeed formation of $\Phi_{F,S}$ is well-defined, linear and valued in continuous functions on $\mathrm{GL}_1(\mathbf{A}_{F,S})$, and is invariant under the continuous left-translation action by the discrete abelian group $\mathcal{O}_{F,S}^{\times}$.

PROPOSITION 2.3.1.2 (Estimates over the $S$-idele classes - I). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

(1) *For every $f\in\mathcal{S}(\mathbf{A}_{F,S})$, the series defining $\Phi_{F,S}(f)$ in (2.3.1.1) converges absolutely and uniformly over the compact subsets of $\mathrm{GL}_1(\mathbf{A}_{F,S})$. The sum is a continuous function over $\mathrm{GL}_1(\mathbf{A}_{F,S})$, invariant under the continuous left-translation action by the discrete subgroup $\mathcal{O}_{F,S}^{\times}$.*

(2) *For every integer $N\ge 1$, there exists a real number $C_N>0$ such that:*

$$
\lvert\Phi_{F,S}(f)(g)\rvert\le C_N\lvert g\rvert_{F,S}^{-N} \tag{2.3.1.3}
$$

*as $\lvert g\rvert_{F,S}\to +\infty$.*

(3) *Let $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_{F,S})$ be a bounded subset. Then for every integer $N\ge 0$, there exist real numbers $C_{\mathcal{B},N}>0$ and $T_{\mathcal{B},N}>0$, such that such that (2.3.1.3) holds with $C_N=C_{\mathcal{B},N}$ for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ such that $\lvert g\rvert_{F,S}>T_{\mathcal{B},N}$.*

(4) *For every integer $N\ge 0$, the assertions in (3) all hold with $T_{\mathcal{B},N}=1$, upon replacing the constant $C_{\mathcal{B},N}>0$ with a possibly larger, still uniform, constant.*

We refer the reader to the end of [Co, §VII,p.30] and the beginning of [Co, §VII,p.31], from the proof of [Co, §VII,Lemma 1(a),p.30], for a method similar to the one for the proof of (1) and (2) below, which applies to prove (1) and (2) of Proposition 2.3.1.2 too.

See also the beginning of [Co, §VII,p.30] (where $\Phi_{F,S}(f)$ is denoted $E_0(f)$).

PROOF. We denote by $S_f$ the intersection $S_f:=S\cap\Sigma_{F,f}$. Since the linear map

$$
\mathcal{S}(\mathbf{A}_{F,S_{\infty}})\otimes\bigotimes_{v\in S_f}\mathcal{S}(F_v)\to\mathcal{S}(\mathbf{A}_{F,S})
$$

is an isomorphism (see (2.1.4.1) from Proposition 2.1.4.1), for each Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_{F,S})$ there exist Schwartz-Bruhat functions $f_1,\ldots,f_m\in\mathcal{S}(\mathbf{A}_{F,S})$, each of the form:

$$
f_k=f_{k,\infty}\otimes\bigotimes_{v\in S_f}f_{k,v}
$$

with $f_{k,v}\in\mathcal{S}(F_v)$ for each $v\in S_f$ and $f_{k,\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ for each $1\le k\le m$, and complex numbers $c_1,\ldots,c_m$, such that $f=\sum_{1\le k\le m}c_kf_k$.

If (1) and (2) hold for each $f_k$, then they hold for $f$ (with different constants $C_N$). We may rename any of the $f_k$ as $f$ and reduce to the case $f=f_{\infty}\otimes\bigotimes_{v\in S_f}f_v$ for $f_{\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ and $f_v\in\mathcal{S}(F_v)$ for each $v\in S_f$. Without loss of generality, we may assume $f_v=\mathrm{1}_{K_v}$ for each $v\in S_f$, with $K_v$ a compact open subset of $F_v$.

We choose a continuous homomorphic section $\tau:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_{F,S})$ to the $S$-idelic norm.

(1) : For the purpose of studying the $\mathcal{O}_{F,S}^{\times}$-invariant sum (2.3.1.2) near a point $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$, by Proposition A.2.4.4 we can replace $g$ with an $\mathcal{O}_{F,S}^{\times}$-translate so that $g\in\tau(\mathbf{R}_{>0})\cdot\overline{E}^1_{F,S}$. We recall that $E^1_{F,S}$ is the $S$-idelic fundamental domain from (A.2.4.4), for the continuous left-translation action of the discrete subgroup $\mathcal{O}_{F,S}^{\times}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

## PDF page 101

**2.3. S-LOCAL ADELIC $\theta$-FUNCTIONS** · **101**

We have

$$
\sum_{\xi\in\mathcal{O}_{F,S}^{\times}}\lvert f(\xi g)\rvert\le\left(\prod_{v\in S_f}\lVert f_v\rVert_u\right)\sum_{\xi\in I}\lvert f_{\infty}(\xi g_{\infty})\rvert \tag{2.3.1.4}
$$

where $g_{\infty}\in\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ is the image of $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ under the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_{F,S})\to\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ induced by the containment $S_{\infty}\subset S$ and $I$ is a discrete subset of $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ constructed as follows.

For each $v\in S_f$, we define $C_v:=\max\lvert K_v\rvert_v>0$. We fix $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$, and the summand $f(\xi g)$ in the sum defining $\Phi_{F,S}$ from (2.3.1.2) is nonzero if and only if $\xi\in g_v^{-1}K_v$ for every $v\in S_f$. If $g\in\tau(\mathbf{R}_{>0})\cdot\overline{E}^1_{F,S}$, then by compactness of $\overline{E}^1_{F,S}$ we have $\lvert g_v^{-1}\rvert_v\le C$ for $C$ a positive real number independent of $v\in S_f$. It follows that $\xi\in\mathcal{O}_{F,S}^{\times}$ satisfies:

$$
\lvert\xi\rvert_v\le CC_v
$$

for all $v\in S_f$ and upon renaming $C\cdot\max_{v\in S_f}C_v$ as $C$ we obtain that $\xi\in\mathcal{O}_{F,S}^{\times}$ satisfies $\lvert\xi\rvert_v\le C$ for all $v\in S$ if $f(\xi g)\ne 0$ for some $g\in\tau(\mathbf{R}_{>0})\cdot\overline{E}^1_{F,S}$. In other words, $\xi$ is contained in the cross-product:

$$
\{x\in\mathbf{A}_{F,S}:\lvert x_v\rvert\le C\text{ for all }v\in S_f\}\times_{\mathbf{A}_{F,S}}\mathcal{O}_{F,S}^{\times}. \tag{2.3.1.5}
$$

The fractional ideal $J:=\prod_{v\in S_f}\mathfrak{p}_v^{n_v}\subset F$, for $n_v$ the least integer such that $\lvert\pi_v\rvert_v^{n_v}\le C$, with $\pi_v$ any choice of local uniformizer at $v$, contains the subset in (2.3.1.5). Note that if $S_f$ is empty then $J=\mathcal{O}_F$ (a consequence of the definition).

We define $I:=J-\{0\}$. We aim at applying Proposition 2.2.1.3 to deduce that the series in the right side of (2.3.1.4) converges, uniformly on compact subsets of the image of $\tau(\mathbf{R}_{>0})\cdot\overline{E}_{S,0}$, and hence so does the series defining $\Phi_{F,S}(f)$ in (2.3.1.2), absolutely and uniformly over compact subsets of $\tau(\mathbf{R}_{>0})\cdot\overline{E}_{S,0}$. We refer the reader to (A.2.4.5) for the definition of $E_{S,0}$ in relation to $E^1_{F,S}$.

In order to do so, we proceed as follows. Let $[a,b]\subset\mathbf{R}_{>0}$ be an arbitrary compact interval, and we call $E_{S,\infty}$ the image in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ of the relatively compact subset $E_{S,0}$ of $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

We define:

$$
\widetilde{\psi}(y):=\sup_{t\in[a,b],g_{\infty}\in\overline{E}_{S,\infty}}\lvert\psi(t,y,g_{\infty})\rvert \tag{2.3.1.6}
$$

where $\psi(t,y,g_{\infty}):=f_{\infty}(\tau(t)yg_{\infty})$ as a function of $(t,y,g_{\infty})\in\mathbf{R}_{>0}\times\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})\times\overline{E}_{S,\infty}$. The function $\widetilde{\psi}:\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})\to\mathbf{R}_{\ge 0}$ is continuous, since $\psi$ is and $[a,b]\times\overline{E}_{S,\infty}$ is Hausdorff with compact closure and $\psi$ is defined and bounded on such closure for every $y\in\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$.

Since $f_{\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ is Schwartz, for every integer $N\ge 1$ there exists a large enough closed ball $B\subset\mathbf{A}_{F,S_{\infty}}$ containing the origin and a real number $C_{B,N}>0$ such that $\lvert f_{\infty}(x_{\infty})\rvert\le C_{B,N}\lVert x_{\infty}\rVert^{-N}$ for all $x_{\infty}\in\mathbf{A}_{F,S_{\infty}}-B$ and $\lVert\cdot\rVert$ is any choice of quasi-norm on $\mathbf{A}_{F,S_{\infty}}$ (it satisfies the triangle inequality up to a universal constant) inducing the Euclidean topology (noting that the constant $C_{B,N}$ and the closed ball $B$ itself depend on such choice).

It follows that for all $(t,y,g_{\infty})\in\mathbf{R}_{>0}\times\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})\times\overline{E}_{S,\infty}$ such that $\tau(t)yg_{\infty}\notin B$, we have

$$
\lvert\psi(t,y,g_{\infty})\rvert\le C_{B,N}\lVert\tau(t)yg_{\infty}\rVert^{-N}. \tag{2.3.1.7}
$$

For every $y\notin(\tau([a,b])\cdot\overline{E}_{S,\infty})^{-1}\cdot B\subset\mathbf{A}_{F,S_{\infty}}$ and for every $(t,g_{\infty})\in[a,b]\times\overline{E}_{S,\infty}$, (2.3.1.7) therefore holds, and it remains valid upon maximizing over $(t,g_{\infty})\in[a,b]\times\overline{E}_{S,\infty}$. We claim that there exists a real number $C_{B,S,N,a,b}>0$ (depending on $C_{B,N}$, on $\overline{E}_{S,\infty}$, on $a,b$ and $B$) such that

$$
\widetilde{\psi}(\xi)\le C_{B,S,N,S,a,b}\lVert\xi\rVert^{-N} \tag{2.3.1.8}
$$

for every $\xi\in I$ away from $(\tau([a,b])\cdot\overline{E}_{S,\infty})^{-1}\cdot B$.

## PDF page 102

**102** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

We now obtain the constant $C_{B,N,S,a,b}$. Multiplication by $\tau(t)g_{\infty}$ is a linear automorphism $A_{t,g_{\infty}}$ of the vector space $\mathbf{A}_{F,S_{\infty}}$ of dimension $[F:\mathbf{Q}]$. We equip $\mathbf{A}_{F,S_{\infty}}$ with the vector space quasi-norm $\lVert\cdot\rVert:=\sup_{v\in S_{\infty}}\{\lvert\cdot\rvert_v^{1/N_v}\}$ with $N_v=1$ if $v$ is real, and $N_v=2$ if $v$ is complex and observe that $A_{t,g_{\infty}}$ is bounded below, i.e. for every $y\in\mathbf{A}_{F,S_{\infty}}$, we have $\lVert A_{t,g_{\infty}}y\rVert\ge C_0(t,g_{\infty})\lVert y\rVert$ for a positive real number $C_0(t,g_{\infty})>0$. For example

$$
C_0(t,g_{\infty}):=\min_{v\in S_{\infty}}\lvert\tau(t)_vg_{\infty,v}\rvert_v^{1/N_v}
$$

qualifies. As a function of $(t,g_{\infty})$ over the compact subset $[a,b]\times\overline{E}_{S,\infty}$, $C_0(t,g_{\infty})$ is bounded below by a positive real number $A$ because $[a,b]\times\overline{E}_{S,\infty}$ is compact.

We observe that we have $1/\lvert\tau(t)_vg_{\infty,v}\rvert_v^{N/N_v}\le C_0(t,g_{\infty})^{-N}\le A^{-N}$ for every $(t,g_{\infty})\in[a,b]\times\overline{E}_{S,\infty}$. We then define

$$
C_{B,S,N,a,b}:=C_{B,N}\cdot A^{-N}.
$$

The constant $C_{B,S,N,a,b}$ works because of the following inequality:

$$
\lvert\psi(t,y,g_{\infty})\rvert\le C_{B,N}\lVert\tau(t)yg_{\infty}\rVert^{-N}\le C_{B,N}\cdot A^{-N}\lVert y\rVert^{-N}=C_{B,S,N,a,b}\lVert y\rVert^{-N}
$$

for every $y\notin(\tau([a,b])\cdot\overline{E}_{S,\infty})^{-1}\cdot B$.

We choose a closed ball $B'$ containing $(\tau([a,b])\cdot\overline{E}_{S,\infty})^{-1}\cdot B$. Since $I$ is discrete, $I\cap B'$, and so convergence of the series in the right side of (2.3.1.4) holds so long as the series $\sum_{\xi\in I-B'}\lVert\xi\rVert^{-N}$ is convergent. We now choose $N>[F:\mathbf{Q}]=\dim_{\mathbf{R}}(\mathbf{A}_{F,S_{\infty}})$, and all the constants in the foregoing accordingly, and apply Proposition 2.2.1.3 (with $x=0$) to obtain the desired convergence.

(2) : Since $f_{\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ for each integer $N\ge 1$ there exists $C_{N,0}>0$ such that $\lvert f_{\infty}(x_{\infty})\rvert\le C_{N,0}\lVert x_{\infty}\rVert_{\infty}^{-N}$ for all $x_{\infty}\in\mathbf{A}_{F,S_{\infty}}$ away from a large enough closed ball $B_0\subset\mathbf{A}_{F,S_{\infty}}$, where $\lVert\cdot\rVert_{\infty}$ is the sup-norm on the Euclidean space $\mathbf{A}_{F,S_{\infty}}$ defined upon fixing coordinates for each Archimedean place $v$ of $F$, choosing an isomorphism $\mathbf{A}_{F,S_{\infty}}\simeq\mathbf{R}^{r_1+2r_2}$.

We fix a continuous homomorphic section $\tau:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_{F,S})$ to the $S$-idelic norm $\lvert\cdot\rvert_{F,S}$. Since $\mathrm{GL}_1(\mathbf{A}_{F,S})\subset\mathbf{A}_{F,S}$ is an open topological embedding, $E_{S,0}$ is relatively compact in $\mathbf{A}_{F,S}$. Thus, for every real number $T>1$ we see that $\tau([1/T,T])\cdot E_{S,0}$ is relatively compact in $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and $\mathbf{A}_{F,S}$, with non-empty interior.

For any closed ball $B\subset\mathbf{A}_{F,S_{\infty}}$ containing the origin, there exists a real number $T_0>0$ such that $B$ contains the image under $\mathrm{GL}_1(\mathbf{A}_{F,S})\to\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ of $\tau([1/T_0,T_0])\cdot E_{S,0}$, and it does not contain the image of $\tau([1/T,T])\cdot E_{S,0}$ for any $T>T_0$.

We choose $\tau$ to be the section into the copy of $\mathbf{R}_{>0}$ contained within $F_{v_0}^{\times}$, for a choice of $v_0\in S_{\infty}$ (defining $\tau$ as the composition of $s_{F,v_0}$ from (A.2.2.5) with the continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$), to obtain, upon enlarging $T_0$ if necessary, that for $B$ so large as to contain $B_0\cup\tau([1/T_0,T_0])\cdot E_{S,0}$, there exists a constant $C_{0,N}>0$, such that the following inequality holds

$$
\lvert f_{\infty}(\tau(t)\xi g_{\infty})\rvert\le C_{N,0}\lVert\tau(t)\xi g_{\infty}\rVert_{\infty}^{-N}=C_{N,0}t^{-N}\lVert\xi g_{\infty}\rVert_{\infty}^{-N} \tag{2.3.1.9}
$$

for all $t>T_0$, $g_{\infty}\in\overline{E}_{\infty}$ (the closure of the image of $E^1_{F,S}$ into $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$) and $\xi\in I$. Upon maximizing the function of $(x,g_{\infty})\in\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})\times\overline{E}_{\infty}$ given by $\lVert xg_{\infty}\rVert_{\infty}^{-N}$ over $g_{\infty}\in\overline{E}_{\infty}$ (thus obtaining a continuous function of $x$) by a method similar as in the proof of (1) we see that there exists a real number $C_{N,1}>0$ such that

$$
\sup_{g_{\infty}\in\overline{E}_{\infty}}\lVert xg_{\infty}\rVert_{\infty}^{-N}\le C_{N,1}\lVert x\rVert_{\infty}^{-N}
$$

for all $x\in\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ with $\lVert x\rVert_{\infty}$ large enough. Up to enlarging $B$, we may assume that for every $\xi\in I$ with $\xi\notin B$, we have $\lVert\xi\rVert_{\infty}$ is as sufficiently large as required.

## PDF page 103

**2.3. S-LOCAL ADELIC $\theta$-FUNCTIONS** · **103**

Renaming $C_{N,0}\cdot C_{N,1}$ as $C_N$ we see that upon choosing $N>r_1+2r_2$ the sum $\sum_{\xi\in I}\lVert\xi\rVert_\infty^{-N}$ converges by Proposition 2.2.1.3 and upon absorbing its value into the constant $C_N$ we obtain that indeed

$$
\sum_{\xi\in I}\lvert f_\infty(\xi g_\infty\tau(t))\rvert\le C_N t^{-N}
$$

for all $g_\infty\in\overline{E}_\infty$ and all $t>T_0$. This implies that (2.3.1.3) holds.

(3) : Let $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_{F,S})$ be a bounded subset. By Proposition 2.1.4.1(1), the canonical linear operator $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_\iota\bigotimes_{v\in S_f}\mathcal{S}(F_v)\to\mathcal{S}(\mathbf{A}_{F,S})$ is a linear topological isomorphism, and hence by Proposition C.2.3.13(2), a bounded subset $\mathcal{B}$ in $\mathcal{S}(\mathbf{A}_{F,S})$ is contained in one which is the image of

$$
\mathrm{cch}(\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w)
$$

the convex circled hull of the subset $\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w$.

Since, by Lemma 2.1.2.4(1), $\mathcal{S}(F_v)$ carries the finest locally convex topology, $\mathcal{B}_w$ is, for each $w\in S_f$, contained in a finite dimensional subspace of $\mathcal{S}(F_v)$ by Proposition C.2.5.1(4).

There therefore exist finitely many $f_{w,1},\ldots,f_{w,m_w}\in\mathcal{S}(F_w)$ whose linear span contains $\mathcal{B}_w$. In particular, all the functions in $\mathcal{B}_w$ are supported on a large enough compact open subset $K_w\subset F_w$, and this is so for each $w\in S_f$.

We deduce that there exists a large enough compact open subset $K\subset\prod_{v\in S_f}F_v$ such that every element of $\mathcal{B}$ is a finite absolutely convex $\mathbf{C}$-linear combination (i.e. one whose coefficients have complex Euclidean absolute values that sum to a real number bounded above by $1$; see [Jar, Part I,Ch.6,§6.1,p.102] for $r=1$; see also [NB, Thm.4.2.11]) of Schwartz-Bruhat functions of the form $f_\infty\otimes\bigotimes_{w\in S_f}f_w$ with each of the $f_w$ supported on the common $K$ whose existence was proved above.

By construction of $C_N$ from (2), this constant depends on $f\in\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w$, and similarly in light of the estimate from (2.3.1.4), the constants $C_{B,N},C_{B',N,S,a,b},C_{N,0}$ and $C_N$ depend on $f$ through $f_\infty$ and through $K$ only.

Specifically, the dependence through $K$ is through the formation of the discrete subset $I\subset\mathrm{GL}_1(\mathbf{A}_{F,S})$: $I$ depends only on the compact open subset $K$ of $\prod_{v\in S_f}F_v$ obtained by projecting the support of the element $f$ onto $\prod_{v\in S_f}F_v$ (upon inspection of the construction of the subset of $\mathbf{A}_{F,S}$ defined in (2.3.1.5)), and as $f$ varies over the image in $\mathcal{S}(\mathbf{A}_{F,S})$ of $\mathrm{cch}(\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w)$ such projection is contained in $K$, and hence $I$ can be made to depend on $f$ only through $K$, therefore obtaining an $I$ that qualifies for the same role in the argument from the foregoing, for all $f$ varying over $\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w$.

That the real number $T_N>0$ such that (2.3.1.3) holds if $\lvert g\rvert_{F,S}>T_N$, and whose formation is uniform as $f$ varies over $\mathcal{B}$, exists, is seen by observing that formation of $B_0$ depends on $f$ through $f_\infty$, for $f$ of the special form $f=f_\infty\otimes\bigotimes_{v\in S_f}f_v\in\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w$.

In particular, the same ball $B_0\subset\mathbf{A}_{F,S_\infty}$ qualifies to give, through the argument from the foregoing, the estimate in (2.3.1.9) as $f_\infty$ varies over the bounded subset $\mathcal{B}_\infty\subset\mathcal{S}(\mathbf{A}_{F,S_\infty})$.

We have now shown that (2.3.1.3) holds for each $f$ of the special form $f_\infty\prod_{w\in S_f}f_w$ with $f_\infty\in\mathcal{B}_\infty$ and $f_w\in\mathcal{B}_w$ for each $w\in S_f$, with $C_N$ and $T_N$ existing and depending only on $\mathcal{B}_\infty$ and $\bigotimes_{w\in S_f}\mathcal{B}_w$.

By linearity of $\Phi_{F,S}$ and the design of the convex circled hull (see [Jar, Part I,Ch.6,§6.1,p.102] for $r=1$; see also [NB, Thm.4.2.11]), the estimate in (2.3.1.3) propagates with the same $C_N$ and $T_N$ to the elements of $\mathrm{cch}(\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w)$, and hence to all the elements of the bounded subset $\mathcal{B}$. We rename $C_N$ as $C_{\mathcal{B},N}$, and $T_N$ as $T_{\mathcal{B},N}$, and these constants satisfy the requirements of (3).

(4) : The estimate in (2.3.1.4) holds for any $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$, and hence, upon choosing a continuous homomorphic section $\tau$ to the $S$-idelic norm, it holds on $\tau(\mathbf{R}_{>0})\cdot E^1_{F,S}$, where $E^1_{F,S}$ is the $S$-idelic fundamental domain from (A.2.4.4), for the continuous left-translation action of the $S$-units $\mathcal{O}_{F,S}^{\times}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

## PDF page 104

**104** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

Since $\mathcal{B}$ is a fixed bounded subset in $\mathcal{S}(\mathbf{A}_{F,S})$, there exists, by Proposition 2.1.4.1(1), a bounded subset $\mathcal{B}_\infty$ in $\mathcal{S}(\mathbf{A}_{F,S_\infty})$, and a bounded subset $\mathcal{B}_f\subset\mathcal{S}(\prod_{v\in S_f}F_v^{\times})$, contained within a finite dimensional $\mathbf{C}$-linear subspace of $\mathcal{S}(\prod_{v\in S_f}F_v^{\times})$ (since $\mathcal{S}(\prod_{v\in S_f}F_v^{\times})$ carries, by Proposition 2.1.2.4 and Proposition C.2.5.1, the finest locally convex topology) linearly generated by finitely many $f_1,\ldots,f_m\in\mathcal{S}(\prod_{v\in S_f}F_v^{\times})$, such that

$$
\mathcal{B}\subset\mathrm{cch}(\mathcal{B}_\infty\otimes\mathcal{B}_f)
$$

the convex circled hull of the subset of $\mathcal{S}(\mathbf{A}_{F,S})$ of those elements of the form $f_\infty\otimes f_0$, as $f_\infty$ varies over $\mathcal{B}_\infty$ and $f_0$ varies over $\mathcal{B}_f$.

The elements of $\mathcal{B}_f$ are finite $\mathbf{C}$-linear combinations of the basis elements $\{f_1,\ldots,f_m\}_{m\ge 0}$ whose complex coefficients have bounded absolute value by a positive real number $A>0$ which depends only on $\mathcal{B}_f$.

We may choose $m\ge 0$ large enough so as to arrange each $f_k$, $1\le k\le m$, to be of the form $f_k=\bigotimes_{v\in S_f}f_{k,v}$, for $f_{k,v}$ the indicator function of a compact open subset of $F_v$.

The subset $I\subset\mathcal{O}_{F,S}^{\times}$ from (2.3.1.4) depends on $\mathcal{B}$ only through the compact open subsets that serve as the supports of the $f_{k,v}$, for each $v\in S_f$, and $1\le k\le m$.

We obtain from (2.3.1.4) that $\Phi_{F,S}(f)$ satisfies the estimate, for $g\in\tau(\mathbf{R}_{>0})\cdot E^1_{F,S}$:

$$
\lvert\Phi_{F,S}(f)(g)\rvert\le mA\sum_{\xi\in I}\lvert f_\infty(\xi g_\infty)\rvert \tag{2.3.1.10}
$$

where $g_\infty$ is the image of $g$ into $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ under the continuous homomorphic projection $\mathrm{GL}_1(\mathbf{A}_{F,S})\to\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$, and as $f$ varies over the elements of $\mathcal{B}_\infty\otimes\mathcal{B}_f$.

For any integer $N\ge 1$, we let $T_{\mathcal{B},N}>0$ be the real number provided by (4), and define $t_{\mathcal{B},N}:=\max\{T_{\mathcal{B},N},1/T_{\mathcal{B},N}\}$.

The same argument provided in the proof of (5) of Theorem 2.2.3.4, shows that, over the compact subset $\tau([1/t_{\mathcal{B},N},t_{\mathcal{B},N}])\cdot E^1_{F,S}$, formation of the map $f_\infty\mapsto\sum_{\xi\in I}\lvert f_\infty(\xi g_\infty)\rvert$ is sequentially continuous on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$.

Since $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ is a Fréchet space (see Proposition 2.1.1.6), it is metrizable, and hence a sequential topological space.

The map $f_\infty\mapsto\sum_{\xi\in I}\lvert f_\infty(\xi g_\infty)\rvert$ is therefore continuous. Since $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ is Montel by Proposition 2.1.1.6 (being a nuclear Fréchet space), it satisfies the Heine-Borel property, and hence the closure in $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ of the bounded subset $\mathcal{B}_\infty$, itself bounded by [NB, Thm.6.1.5], is compact.

The continuous map $f_\infty\mapsto\sum_{\xi\in I}\lvert f_\infty(\xi g_\infty)\rvert$ on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ is therefore bounded on $\mathcal{B}_\infty$, and hence there exists a positive real number $C_{\mathcal{B}}>0$ such that, over the compact subset $\tau([1/t_{\mathcal{B},N},t_{\mathcal{B},N}])\cdot E^1_{F,S}$, the estimate:

$$
\lvert\Phi_{F,S}(f)(g)\rvert\le mAC_{\mathcal{B}} \tag{2.3.1.11}
$$

holds for all $f\in\mathcal{B}_\infty\otimes\mathcal{B}_f$. It therefore holds over the convex circled hull of $\mathcal{B}_\infty\otimes\mathcal{B}_f$, and hence over $\mathcal{B}$.

Upon renaming the positive real number $\max\{C_{\mathcal{B},N},mAC_{\mathcal{B}}\}$, for $C_{\mathcal{B},N}>0$ the constant provided by (4), as $C_{\mathcal{B},N}$, we obtain that all the assertions in (4) hold for $T_{\mathcal{B},N}=1$, and using the new constant $C_{\mathcal{B},N}$. $\square$

2.3.1.2. *Homogeneous $S$-adelic $\theta$-functions.* Throughout the remainder of this susbection, we choose a continuous homomorphic section to the $S$-idelic norm:

$$
\tau:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_{F,S})
$$

and retain the notation $\mu_{S,1},\bar{\mu}_{S,1}$ for the resulting Haar measures on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$ and $J^1_{F,S}=\mathrm{GL}_1(\mathbf{A}_{F,S})^1/\mathcal{O}_{F,S}^{\times}$.

We recall that $\bar{\mu}_{S,1}$ does not depend on $\tau$ but only on the volume it assigns to the compact Hausdorff abelian group $J^1_{F,S}$.

DEFINITION 2.3.1.3 ($\omega$-homogeneous $S$-local adelic $\theta$-functions). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\omega$ be a continuous character of $J^1_{F,S}$.

## PDF page 105

**2.3. S-LOCAL ADELIC $\theta$-FUNCTIONS** · **105**

We define:

$$
\Phi_{F,S,\omega}:\mathcal{S}(\mathbf{A}_{F,S})\to C(J_{F,S}) \tag{2.3.1.12}
$$

to be the linear operator determined by the assignment, for every Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_{F,S})$:

$$
\Phi_{F,S,\omega}(f)(g):=\int_{J^1_{F,S}}\Phi_{F,S}(f)(gh)\omega(h)\,\mathrm{d}\bar{\mu}_{S,1}(h) \tag{2.3.1.13}
$$

as functions of $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$. We refer to $\Phi_{F,S,\omega}$ as the *$\omega$-homogeneous $S$-local adelic $\theta$-function of $f$*.

2.3.1.3. *Estimates over $J_{F,S}/J^1_{F,S}$.* It is indeed a consequence of Proposition 2.3.1.4 below, that formation of $\Phi_{F,S,\omega}$ is well-defined, linear and valued in continuous functions on $\mathrm{GL}_1(\mathbf{A}_{F,S})$, $\widetilde{\omega}$-homogeneous under the left-translation action by the closed abelian subgroup $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, for $\widetilde{\omega}$ the composition of $\omega$ with the continuous quotient homomorphism $\mathrm{GL}_1(\mathbf{A}_{F,S})^1\to J^1_{F,S}$. Equivalently, $\mathcal{O}_{F,S}^{\times}$-invariant and $\omega$-homogeneous, as continuous functions on $J_{F,S}$, under the continuous left-translation action of $J^1_{F,S}$.

PROPOSITION 2.3.1.4 (Estimates over the $S$-idele classes - II). *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places. Let $\omega$ be a continuous character of $\mathrm{GL}_1(\mathbf{A}_{F,S})^1/\mathcal{O}_{F,S}^{\times}$. We denote by $\widetilde{\omega}\in\widehat{\mathrm{GL}_1(\mathbf{A}_{F,S})^1}$ the composition of $\omega$ with the continuous quotient homomorphism $\mathrm{GL}_1(\mathbf{A}_{F,S})^1\to J^1_{F,S}$.*

(1) *For every $f\in\mathcal{S}(\mathbf{A}_{F,S})$, the integral defining $\Phi_{F,S,\omega}(f)$ in (2.3.1.12) converges absolutely and uniformly over the compact subsets of $\mathrm{GL}_1(\mathbf{A}_{F,S})$. It is a continuous function over $\mathrm{GL}_1(\mathbf{A}_{F,S})$, $\widetilde{\omega}$-homogeneous under the continuous left-translation action by the closed subgroup $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.*

(2) *For every integer $N\ge 1$, there exists a constant $C_N>0$ such that:*

$$
\lvert\Phi_{F,S,\omega}(f)(g)\rvert\le C_N\lvert g\rvert_{F,S}^{-N} \tag{2.3.1.14}
$$

*for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ such that $\lvert g\rvert_{F,S}\to+\infty$.*

(3) *Let $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_{F,S})$ be a bounded subset. There exist real numbers $C_{\mathcal{B},N},T_{\mathcal{B},N}>0$ such that (2.3.1.14) holds for with $C_N=C_{\mathcal{B},N}$ and for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ such that $\lvert g\rvert_{F,S}>T_{\mathcal{B},N}$, for all $f\in\mathcal{B}$.*

(4) *For every integer $N\ge 0$, the assertions in (3) all hold with $T_{\mathcal{B},N}=1$, upon replacing the constant $C_{\mathcal{B},N}>0$ with a possibly larger, still uniform, constant.*

PROOF. Since $J^1_{F,S}=\mathrm{GL}_1(\mathbf{A}_{F,S})^1/\mathcal{O}_{F,S}^{\times}$ is compact Hausdorff, insofar as it receives a continuous surjection from $C^1_{F,S}$, which is compact Hausdorff by Theorem A.1.5.2(1), and $\omega$ is continuous, integration over $\mathrm{GL}_1(\mathbf{A}_{F,S})^1/\mathcal{O}_{F,S}^{\times}$ with respect to $\bar{\mu}_{S,1}$ implies that (1) and (2) and (3) are a consequence of Proposition 2.3.1.2, following the argument provided for the global analog of (1) from Lemma 2.2.5.2.

(4) : For each integer $N\ge 1$, this follows from Proposition 2.3.1.2(4) upon replacing the constant $C_{\mathcal{B},N}>0$ provided by the Proposition, with $\bar{\mu}_{S,1}(J^1_{F,S})C_{\mathcal{B},N}$, after integrating both sides of the estimates asserted in Proposition 2.3.1.2(4) over the compact Hausdorff abelian group $J^1_{F,S}$. $\square$

**2.3.2. Compatibility with directional derivatives.** In this section we discuss analogs of the global results from Lemma 2.2.4.2 and Lemma 2.2.4.3 on compatibility of $\theta$-function operators with directional derivatives along continuous 1-parameter subgroups.

LEMMA 2.3.2.1. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_{F,S})$ be a continuous 1-parameter subgroup.*

*For every Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_{F,S})$, the limit:*

$$
(\partial_\gamma f)(x):=\lim_{t\to 1}\frac{f(\gamma(t)x)-f(x)}{t-1} \tag{2.3.2.1}
$$

*exists for every $x\in\mathbf{A}_{F,S}$, and, as a function of $x\in\mathbf{A}_{F,S}$, it is continuous. Moreover, $\partial_\gamma f$ is itself a Schwartz-Bruhat function on $\mathbf{A}_{F,S}$.*

## PDF page 106

**106** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

*As a linear endomorphism on $\mathcal{S}(\mathbf{A}_{F,S})$, $\partial_\gamma$ is continuous with respect to the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{A}_{F,S})$.*

PROOF. All the assertions are consequences of Lemma 2.2.4.2 (using the insertion operators $\pi_S:\mathcal{S}(\mathbf{A}_{F,S})\to\mathcal{S}(\mathbf{A}_F)$ from (2.1.4.5)). $\square$

PROPOSITION 2.3.2.2 (Existence of directional derivatives over the $S$-idele classes). *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places of $F$. Let $\omega$ be a continuous character of $J^1_{F,S}$.*

*Let $\gamma:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_{F,S})$ be a continuous 1-parameter subgroup.*

*For every Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_{F,S})$, the limits:*

$$
\partial_\gamma\Phi_{F,S}(f)(g):=\lim_{t\to 1}\frac{\Phi_{F,S}(f)(\tau(t)g)-\Phi_{F,S}(f)(g)}{t-1} \tag{2.3.2.2}
$$

*and:*

$$
\partial_\gamma\Phi_{F,S,\omega}(f)(g):=\lim_{t\to 1}\frac{\Phi_{F,S,\omega}(f)(\tau(t)g)-\Phi_{F,S,\omega}(f)(g)}{t-1} \tag{2.3.2.3}
$$

*exist for every $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$, and their formation is continuous with respect to $g$. Moreover, we have:*

$$
\partial_\gamma\Phi_{F,S}(f)=\Phi_{F,S}(\partial_\gamma f),\ \partial_\gamma\Phi_{F,S,\omega}(f)=\Phi_{F,S,\omega}(\partial_\gamma f) \tag{2.3.2.4}
$$

*as continuous functions on $\mathrm{GL}_1(\mathbf{A}_{F,S})$, invariant under the continuous left-translation action of $\mathcal{O}_{F,S}^{\times}$.*

REMARK 2.3.2.3. For $f_S\in\mathcal{S}(\mathbf{A}_{F,S})$ we can build the global Schwartz-Bruhat function $f:=\pi_S(f_S)\in\mathcal{S}(\mathbf{A}_F)$, and pass to its global adelic $\theta$-function $\Phi_F(f)$. We can also associate to $f_S$ its $S$-local adelic $\theta$-function $\Phi_{F,S}(f_S)$. The two $\theta$-functions are indeed related. How this goes will be explained throughout the next Chapters up to Chapter 6. Relating $\Phi_{F,S}(f_S)$ and $\Phi_F(f)$ will require use of the Mellin transform, so it is not elementary. In particular, Proposition 2.3.2.2 cannot be deduced from its global analog (see Lemma 2.2.4.3) at this time, so it requires its own argument which is however very similar to the global argument already seen.

PROOF OF PROPOSITION 2.3.2.2. The existence of the limit in (2.3.2.3) follows from the existence of the limit in (2.3.2.2) by Dominated Convergence and compactness of $J^1_{F,S}$, and the fact that $\bar{\mu}_{S,1}$ is a Radon measure on $J^1_{F,S}$, and the identity $\partial_\gamma\Phi_{F,S,\omega}(f)=\Phi_{F,S,\omega}(\partial_\gamma f)$ in (2.3.2.4) follows from the identity $\partial_\gamma\Phi_{F,S}(f)=\Phi_{F,S}(\partial_\gamma f)$. The details of both arguments are similar to those provided in the global situation for Lemma 2.2.4.3 and Theorem 2.2.5.4(3) upon replacing $C^1_F$ with $J^1_{F,S}$, $E^1_F$ with $E_{S,0}$, and $\bar{\mu}_1$ with $\bar{\mu}_{S,1}$. $\square$

**2.4. Asymptotic behavior as $\lvert g\rvert_{F,S}\to 0^{+}$ by lattice point-counting**

Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. In this section we estimate $\Phi_{F,S}(f)(g)$, for $f\in\mathcal{S}(\mathbf{A}_{F,S})$, as a function of $g\in J_{F,S}$ and in the regime $\lvert g\rvert_{F,S}\to 0^{+}$.

For every Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_{F,S})$, the function $\Phi_{F,S}(f)$ on $J_{F,S}$ is smooth along every continuous 1-parameter subgroup (by Proposition 2.3.2.2. In this section we will be quantifying the unboundedness of $\Phi_{F,S}(f)$ on $J_{F,S}$ as $\lvert g\rvert_{F,S}\to 0^{+}$, proving an estimate of the following form:

$$
\Phi_{F,S}(f)=O(\lvert\log\lvert g\rvert_{F,S}\rvert^{\lvert S\rvert-1})
$$

as $\lvert g\rvert_{F,S}\to 0^{+}$, and discussing the dependencies of the implied constant.

Lattice-point counting methods and Dirichlet's $S$-unit Theorem are the main ingredients in the calculations that lead to such estimate.

**2.4.1. Warm-up: the case of the rational number field.** As a warmup, we begin with the special case $F=\mathbf{Q}$ to provide indications as to the origin of the $O(\lvert\log\lvert g\rvert_{F,S}\rvert^{\lvert S\rvert-1})$ bound. The general case is discussed in §2.4.2 (see Theorem 2.4.2.1).

## PDF page 107

**2.4. ASYMPTOTIC BEHAVIOR AS $|g|_{F,S}\to 0^+$ BY LATTICE POINT-COUNTING** · **107**

We refer the reader to the discussion preceding [Co, §VII,(4),p.29], where reference to a special case of the result in Proposition 2.4.1.1 below is made.

PROPOSITION 2.4.1.1. *Let $S$ a finite set of places of the rational number field $F=\mathbf{Q}$ containing the unique Archimedean place. Let $f\in\mathcal{S}(\mathbf{A}_{\mathbf{Q},S})$.*

*There exists a real number $C_f>0$ depending on $f$, such that:*

$$
\lvert\Phi_{\mathbf{Q},S}(f)(g)\rvert\le C_f\,\lvert\log\lvert g\rvert_{\mathbf{Q},S}\rvert^{\lvert S\rvert-1} \tag{2.4.1.1}
$$

*for all $g\in\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q},S})$ as $\lvert g\rvert_{\mathbf{Q},S}\to 0^+$, and the same holds for $\Phi_{\mathbf{Q},S,\omega}(f)(g)$ for any continuous character $\omega$ of $J^1_{\mathbf{Q},S}$.*

LEMMA 2.4.1.2. *Let $N,M\ge 1$ be two integers, with $N>1$, $a_1,\ldots,a_M>1$ real numbers. Let $\phi:\mathbf{R}_{>0}\to\mathbf{C}$ be function satisfying the following conditions:*

(1) *there exists a real number $C>0$ such that:*

$$
\lvert\phi(t)\rvert\le C \tag{2.4.1.2}
$$

*for all $t>0$.*

(2) *There exist real numbers $A,T>0$ such that $\lvert\phi(t)\rvert\le At^{-N}$ for all $t\ge T$.*

*Then there exist real numbers $T_0,C_\phi>0$:*

$$
\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M}\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert\le C\lvert\log(t)\rvert^M \tag{2.4.1.3}
$$

*as $0<t<T_0$, with $C>0$ depending on $T,M,N$ and $a_1,\ldots,a_M$.*

PROOF. Without loss of generality we may and do assume that we have $1<a_1\le a_2\le\ldots\le a_M$. We fix $t\in(0,T]$.

If any of the $k_j$ in $(k_1,\ldots,k_M)\in\mathbf{N}^M$ is such that

$$
k_j\ge -\log_{a_j}(t)+\log_{a_j}(T)
$$

then $a_1^{k_1}\cdots a_M^{k_M}t\ge T$, and hence $\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert$ is bounded above by $A(a_1^{k_1}\cdots a_M^{k_M}t)^{-N}$.

We obtain, as an upper bound for the sum over the tuples $(k_1,\ldots,k_M)\in\mathbf{N}^M$ such that $k_j\ge -\log_{a_j}(t)+\log_{a_j}(T)$:

$$
\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M,k_j\ge -\log_{a_j}(t)+\log_{a_j}(T)}\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert\le A\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M,k_j\ge -\log_{a_j}(t)+\log_{a_j}(T)}(a_1^{k_1}\cdots a_M^{k_M}t)^{-N} \tag{2.4.1.4}
$$

and we have:

$$
\sum_{k_j\ge -\log_{a_j}(t)+\log_{a_j}(T)}(a_j^{k_j})^{-N}=\frac{a_j^{N\log_{a_j}(t)-N\log_{a_j}(T)}}{1-a_j^{-N}}=\frac{(t/T)^N}{1-a_j^{-N}}. \tag{2.4.1.5}
$$

We deduce from (2.4.1.4) and (2.4.1.5) the estimate:

$$
\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M,k_j\ge -\log_{a_j}(t)+\log_{a_j}(T)}\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert\le A\prod_{1\le j'\le M,j'\ne j}\frac{1}{1-a_{j'}^{-N}}\frac{T^{-N}}{1-a_j^{-N}}=AT^{-N}\prod_{1\le j\le M}\frac{1}{1-a_j^{-N}} \tag{2.4.1.6}
$$

valid for $t\in(0,T]$.

A similar argument shows that each of the sums over the tuples $(k_1,\ldots,k_M)\in\mathbf{N}^M$ such that at least one of the $k_j$ satisfies $k_j\ge -\log_{a_j}(t)+\log_{a_j}(T)$ is bounded as $t\in(0,T]$.

## PDF page 108

**108** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

Explicitly, we have, upon denoting by $P_m$ the set of $m$-tuples of nonnegative integers chosen without repetitions out of the finite set $\{1,\ldots,M\}$, for $0\le m\le M$:

$$
\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M,k_{j_r}\ge -\log_{a_{j_r}}(t)+\log_{a_{j_r}}(T),(j_r)_{1\le r\le m}\in P_m}\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert\le At^{-N}\prod_{1\le j'\le M,j'\ne j_r,1\le r\le m}\frac{1}{1-a_{j'}^{-N}}\prod_{1\le r\le m}\frac{(t/T)^N}{1-a_{j_r}^{-N}} \tag{2.4.1.7}
$$

which in turn equals:

$$
A\prod_{1\le j\le M}\frac{1}{1-a_j^{-N}}t^{(m-1)N}T^{-N} \tag{2.4.1.8}
$$

We deduce that we have:

$$
\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M}\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert\le\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M:k_j\le -\log_{a_j}(t)+\log_{a_j}(T),1\le j\le M}\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert \tag{2.4.1.9}
$$

$$
+ A\prod_{1\le j\le M}\frac{1}{1-a_j^{-N}}\sum_{1\le m\le M}\binom{M}{m}t^{(m-1)N}T^{-N} \tag{2.4.1.10}
$$

as $t\in(0,T]$. We analyze the sum

$$
\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M:k_j\le -\log_{a_j}(t)+\log_{a_j}(T),1\le j\le M}\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert \tag{2.4.1.11}
$$

for $t\in(0,T]$. Since $\lvert\phi(t)\rvert\le C$ for all $t>0$, we have:

$$
\sum_{(k_1,\ldots,k_M)\in\mathbf{N}^M:k_j\le -\log_{a_j}(t)+\log_{a_j}(T),1\le j\le M}\lvert\phi(a_1^{k_1}\cdots a_M^{k_M}t)\rvert\le C(1+\lvert\log_{a_1}(t/T)\rvert)^M \tag{2.4.1.12}
$$

where we have used $1<a_1\le a_j$ for every $1\le j\le M$. Upon combining (2.4.1.9) with (2.4.1.12), we deduce that (2.4.1.3) holds. $\square$

We can now prove Proposition 2.4.1.1:

PROOF OF PROPOSITION 2.4.1.1. We call $S_f:=S\cap\Sigma_{\mathbf{Q},f}$.

Our aim is to reduce the assertion in (2.4.1.1) of the Proposition to Lemma 2.4.1.2. We first reduce to the case $f\in\mathcal{S}(\mathbf{A}_{\mathbf{Q},S})$ is of the form $f_\infty\otimes\bigotimes_{p\in S_f}1_{\mathbf{Z}_p}$. Indeed, since the estimate in (2.4.1.1) is stable under finite $\mathbf{C}$-linear combinations of Schwartz-Bruhat functions on $\mathbf{A}_{\mathbf{Q},S}$, at the cost of replacing the implied constant by a larger one, we may and do assume $f$ is of the form $f=f_\infty\otimes\bigotimes_{p\in S_f}1_{K_p}$ for $K_p\subset\mathbf{Q}_p$ a compact open non-empty subset, for each $p\in S_f$.

Since $\mathbf{Z}_p$ is a compact open subgroup and $\mathbf{Q}_p=\bigcup_{m\ge 0}p^{-m}\mathbf{Z}_p$, there exists a large enough integer $N_p\ge 0$ such that $K_p\subset p^{-N_p}\mathbf{Z}_p$.

Our aim is to estimate the sum

$$
\sum_{\xi\in\mathcal{O}_{\mathbf{Q},S}^\times}\left\lvert f_\infty(\xi g_\infty)\prod_{p\in S_f}1_{K_p}(\xi g_p)\right\rvert \tag{2.4.1.13}
$$

where $g_\infty$ is the image of $g\in\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q},S})$ into $\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q},S_\infty})$ and $g_p$ the image of $g$ into $\mathbf{Q}_p$ for each $p\in S_f$, and since $1_{K_p}\le 1_{p^{-N}\mathbf{Z}_p}$ as real-valued functions on $\mathbf{Q}_p$ then for this purpose it is enough to replace $\mathbf{Q}_p$ with $p^{-N}\mathbf{Z}_p$ at all the finite places $p\in S_f$ such that $K_p\ne\mathbf{Z}_p$ (while we keep $N=0$ at all finite places $p\in S$ such that $K_p=\mathbf{Z}_p$).

Then for any integer $a\ge N$ we have $p^ap^{-N}\in\mathbf{Z}_p$. We choose $a$ so large that $p^ap^{-N_p}\in\mathbf{Z}_p$ holds for all finite places $p\in S$ (such $a$ exists because $S$ is finite).

## PDF page 109

**2.4. ASYMPTOTIC BEHAVIOR AS $|g|_{F,S}\to 0^+$ BY LATTICE POINT-COUNTING** · **109**

We note that $p\in\mathcal{O}_{\mathbf{Q},S}^\times$ since $S$ contains $p$. The convergent sum in (2.4.1.13) is $\mathcal{O}_{\mathbf{Q},S}^\times$-invariant, i.e. invariant under left-translation by $S$-units. We operate by left-translation by $p^a$ and reduce to estimating the sum

$$
\sum_{\xi\in\mathcal{O}_{\mathbf{Q},S}^\times}\left\lvert f_\infty(\xi p^ag_\infty)\prod_{v\in S_f}1_{p^{-N_p}\mathbf{Z}_p}(\xi p^ag_p)\right\rvert=\sum_{\xi\in\mathcal{O}_{\mathbf{Q},S}^\times}\left\lvert f_\infty(\xi p^ag_\infty)\prod_{p\in S_f}1_{p^ap^{-N_p}\mathbf{Z}_p}(\xi p^ag_p)\right\rvert\le\sum_{\xi\in\mathcal{O}_{\mathbf{Q},S}^\times}\left\lvert f_\infty(\xi p^ag_\infty)\prod_{p\in S_f}1_{\mathbf{Z}_p}(\xi g_p)\right\rvert \tag{2.4.1.14}
$$

where $p^a$ denotes both the image of the diagonal element $p^a\in\mathcal{O}_{\mathbf{Q},S}^\times$ in $\mathbf{R}^\times$ and in $\mathbf{Q}_\ell^\times$ for every $\ell\in S$ (including $\ell=p$).

We rename the Schwartz-Bruhat function $x\mapsto f_\infty(p^ax)$ as $f_\infty$ and replace $K_p$ with $\mathbf{Z}_p$. We are therefore reduced to the case $f$ is of the form

$$
f=f_\infty\otimes\bigotimes_{p\in S_f}1_{\mathbf{Z}_p}.
$$

The reduction is performed at the cost of enlarging the implied constant in the estimate from (2.4.1.1).

It is furthermore enough to estimate the sum

$$
\sum_{\xi\in\mathcal{O}_{\mathbf{Q},S}^\times}\lvert f(\xi g)\rvert \tag{2.4.1.15}
$$

for $f$ of such special form, on $g=\tau(t)g_0$, for $\tau$ a choice of continuous homomorphic section to the $S$-idelic norm, and with $t\in\mathbf{R}_{>0}$ and $g_0\in E_{S,0}$, the $S$-idelic fundamental domain from (A.2.4.5). Under such additional constraint on $g$, the only $\xi\in\mathcal{O}_{\mathbf{Q},S}^\times$ that contribute to the sum in (2.4.1.15) non-trivially satisfy $\lvert\xi\rvert_p\le 1$ for every $p\in S_f$, which reads $\xi\in\mathcal{O}_{\mathbf{Q},S}^\times\cap\mathbf{Z}$.

We now note that, upon listing the prime numbers $\{p_1,\ldots,p_{\lvert S\rvert-1}\}$ ordered increasingly, whose non-Archimedean absolute values are contained in $S$, we have

$$
\mathcal{O}_{\mathbf{Q},S}^\times=(\mathbf{Z}[1/(p_1\cdots p_{\lvert S\rvert-1})])^\times
$$

and hence $p_1^{-1},\ldots,p_{\lvert S\rvert-1}^{-1}$ are fundamental units. We define $a_k:=p_k$ for $1\le k\le\lvert S\rvert-1$.

For $K_S\subset\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q},S})$ the compact Hausdorff subgroup:

$$
K_S=\mu_2\times\prod_{p\in S_f}\mathbf{Z}_p^\times
$$

given as the kernel of the $S$-logarithm $\mathscr{L}_S$, we use that $f\in\mathcal{S}(\mathbf{A}_{\mathbf{Q}})$ to see that as a function of $t\in\mathbf{R}_{>0}$, the function

$$
\phi:g\mapsto\sup_{g_0\in E_{S,0}}\sup_{h\in K_S}\lvert f(\xi h\tau(t)g_0)\rvert
$$

on $\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q},S})$ (for $\tau$ the chosen continuous homomorphic section to the $S$-idelic norm, and $E_{S,0}$ the $S$-idelic fundamental domain from (A.2.4.5)) satisfies

$$
\sup_{t\in\mathbf{R}_{>0}}(1+t^N)\lvert\phi(t)\rvert<+\infty
$$

for every integer $N\ge 1$.

In light of the inequality, for all $(t,g_0)\in\mathbf{R}_{>0}\times E_{S,0}$:

$$
\lvert\Phi_{\mathbf{Q},S}(f)(\tau(t)g_0)\rvert\le\sum_{\xi\in\mathcal{O}_{\mathbf{Q},S}^\times}\lvert f(\xi\tau(t)g_0)\rvert\le C\sum_{(k_1,\ldots,k_{\lvert S\rvert-1})\in\mathbf{N}^{\lvert S\rvert-1}}\phi(a_1^{k_1}\cdots a_{\lvert S\rvert-1}^{k_{\lvert S\rvert-1}}t) \tag{2.4.1.16}
$$

for a positive real number $C>0$, we deduce that Lemma 2.4.1.2 applies to $\phi$ with $M=\lvert S\rvert-1$. The Lemma settles Proposition 2.4.1.1 in the case of $S$-local adelic $\theta$-functions (i.e. in the non $\omega$-homogeneous case). The

## PDF page 110

**110** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

case of $\omega$-homogeneous $S$-local adelic $\theta$-functions follows upon integrating over the compact Hausdorff abelian group $J^1_{\mathbf{Q},S}$, up to replacing the constant $C>0$ with $C\cdot\bar{\mu}_{S,1}(J^1_{\mathbf{Q},S})$. $\square$

The preceding result for $F=\mathbf{Q}$ and $S$ the 3-element set containing the real place, as well as the 2-adic and 3-adic places, generalizes an observation made in [Co, §VII,p.29] with a similar intent.

More generally and using the $S$-logarithm $\mathscr{L}_S$ from (A.2.4.7), the effect of left-multiplication by the discrete subgroup of $\mathrm{GL}_1(\mathbf{A}_{F,S})$ generated by the fundamental $S$-units $\varepsilon_1,\ldots,\varepsilon_{\lvert S\rvert-1}$ is ergodic on all the finite intersections of the $S$-adelic “hyperplanes”:

$$
H_v:=\{x\in\mathbf{A}_{F,S}:x_v=0\}
$$

for each $v\in S_f$, where we equip the open subset $U_v$ of $H_v$ of those points $x\in H_v$ such that $x_w\ne 0$ for all $w\in S-\{v\}$, with the measure inherited from the product of the multiplicative Tamagawa measures on $\prod_{w\in S-\{v\}}F_w^\times$, upon realizing $U_v$ as an orbit under $\mathrm{GL}_1(\mathbf{A}_{F,S})$ whose stabilizer is $F_v^\times\subset\mathrm{GL}_1(\mathbf{A}_{F,S})$.

It is the ergodicity of this action that causes not only the $S$-local adelic $\theta$-functions $\Phi_{F,S}(f)$ for $f\in\mathcal{S}(\mathbf{A}_{F,S})$, to be unbounded as $\lvert g\rvert_{F,S}\to 0^+$, but also their Mellin transform to have poles on the imaginary line.

For $\chi\in\widehat{J_{F,S}}$ a fixed choice of continuous character, we consider the function of $s\in\mathbf{C}_{>0}$:

$$
Z_S(f,\chi\lvert\cdot\rvert_{F,S}^s):=\int_{J_{F,S}}\Phi_{F,S}(f)(g)\chi(g)\lvert g\rvert_{F,S}^s\,\mathrm{d}\bar{\mu}_S(g)
$$

where the integral converges absolutely and uniformly for $s\in\mathbf{C}_{>0}$ to a holomorphic function (by the rapid decay of the $S$-local adelic $\theta$-function $\Phi_{F,S}(f)$, proved in Proposition 2.3.1.2(2)).

The reader familiar with the correspondence between asymptotic expansions as in (2.4.1.1) from Proposition 2.4.1.1 and Proposition 2.3.1.2 (see, for instance, Theorem B.2.1.7 in combination with the Asymptotic Residue Theorem of Theorem B.3.2.1, as well as [HL, §2,(2.10),p.385] and [HL, §2,Thm.1b,p.385]) will read off from (2.4.1.1) the following piece of information: if the Mellin transform $Z_S(f,\chi\lvert\cdot\rvert_{F,S}^s)$ of $\Phi_{F,S}(f)$ extends meromorphically to the complex $s$-plane (this will be seen using the local functional equations from [CF, §2.4,Thm.2.4.1,p.315]), then it may have poles on the imaginary line (and possibly elsewhere too, but not over $\mathbf{C}_{>0}$).

The poles on the imaginary line all have multiplicity bounded above by $\lvert S\rvert$, and this is a direct consequence of Mellin Inversion applied to the estimate from (2.4.1.1).

We will be classifying and studying the poles of the meromorphic functions $Z_S(f,\chi\lvert\cdot\rvert_{F,S}^s)$ throughout Chapter 5, and their relation to the Schauder bases that have a fundamental role to play in performing the trace calculation that is the main subject of this work.

It is important to be aware of the relation between such poles, and the action of $\mathcal{O}_{F,S}^\times$ on $\mathbf{A}_{F,S}$ and especially on the “boundary hyperplanes” $H_v$ of which the complement of $\mathrm{GL}_1(\mathbf{A}_{F,S})$ is comprised.

We will be now proving the general version of Proposition 2.4.1.1.

**2.4.2. The general case.** In the special case of $F=\mathbf{Q}$, direct arguments sufficed to establish the desired estimate on $\Phi_{F,S}(f)(g)$ in the regime as $\lvert g\rvert_{F,S}\to 0^+$.

In the Theorem below, we treat the general case, and show that the implied constants can be arranged to be uniform on bounded subsets within $\mathcal{S}(\mathbf{A}_{F,S})$.

Theorem 2.4.2.1 below will serve the later purpose of showing the operators arising as $S$-idelic Zeta functions $L_S$ on $\mathcal{S}(\mathbf{A}_{F,S})$ (see (5.1.1.2)) valued in meromorphic functions on the Riemann surface $\Omega(J_{F,S})$, are continuous with respect to finer topologies than that of uniform convergence on the compact subsets away from the poles.

We refer the reader to [Co, §VII,(6),p.30], where a similar estimate based on lattice-point counting and a volume calculation, is referred to.

## PDF page 111

**2.4. ASYMPTOTIC BEHAVIOR AS $|g|_{F,S}\to 0^+$ BY LATTICE POINT-COUNTING** · **111**

THEOREM 2.4.2.1 (On the asymptotic behavior of the $S$-local $\theta$-functions as $|g|_{F,S}\to 0^+$). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

*Let $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_{F,S})$ be a bounded subset.*

*There exist real numbers $C_{\mathcal{B},1},C_{\mathcal{B},2}>0$ such that we have, for every $f\in\mathcal{B}$:*

$$
|\Phi_{F,S}(f)(g)|\le C_{\mathcal{B},1}|\log|g|_{F,S}|^{|S|-1}+C_{\mathcal{B},2} \tag{2.4.2.1}
$$

*for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ such that $|g|_{F,S}<1$.*

PROOF. Let $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_{F,S})$ be a bounded subset. By Proposition 2.1.4.1(1), the canonical linear operator $\mathcal{S}(\mathbf{A}_{F,S_\infty})\otimes_{\iota}\bigotimes_{v\in S_f}\mathcal{S}(F_v)\to\mathcal{S}(\mathbf{A}_{F,S})$ is a linear topological isomorphism, and by Proposition C.2.3.13(2), combined with Corollary C.2.3.12 and [Jar, Part III,Ch.15,§15.1,p.324], a bounded subset $\mathcal{B}$ in $\mathcal{S}(\mathbf{A}_{F,S})$ is contained in one which is the image of

$$
\mathrm{cch}(\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w)
$$

the convex circled hull of the subset $\mathcal{B}_\infty\otimes\bigotimes_{w\in S_f}\mathcal{B}_w$, with $\mathcal{B}_w$ bounded in a finite dimensional $\mathbf{C}$-linear subspace of $\mathcal{S}(F_w)$ for each finite place $w\in S$.

Indeed, since, by Lemma 2.1.2.4(1), $\mathcal{S}(F_v)$ carries the finest locally convex topology, $\mathcal{B}_w$ can be assumed to be, for each $w\in S_f$, contained in a finite dimensional subspace of $\mathcal{S}(F_v)$ by Proposition C.2.5.1(4).

There therefore exist finitely many $f_{w,1},\ldots,f_{w,m_w}\in\mathcal{S}(F_w)$ whose linear span contains $\mathcal{B}_w$. In particular, all the functions in $\mathcal{B}_w$ are supported on a large enough compact open subset $K_w\subset F_w$, and this is so for each $w\in S_f$.

We deduce that there exists a large enough compact open subset $K\subset\prod_{v\in S_f}F_v$ such that every element of $\mathcal{B}$ is a finite absolutely convex $\mathbf{C}$-linear combination (i.e. one whose coefficients have complex Euclidean absolute values that sum to a real number bounded above by 1; see [Jar, Part I,Ch.6,§6.1,p.102] for $r=1$; see also [NB, Thm.4.2.11]) of Schwartz-Bruhat functions of the form $f_\infty\otimes\bigotimes_{w\in S_f}f_w$ with each of the $f_w$ supported on the common $K$ whose existence was proved above.

These observations have proceeded as in the proof of Proposition 2.3.1.2(3).

There exists a large enough integer $N\ge 0$ such that $K\subset(1/N)\widehat{\mathcal{O}}_{F,S}$. We may therefore rename $(1/N)\widehat{\mathcal{O}}_{F,S}$ as $K$.

The left-translation action of $N^{\mathbf{Z}}\subset\prod_{v\in S_f}F_v^{\times}$ extends to $\mathcal{S}(\mathbf{A}_{F,S})$ through the $\bigotimes_{v\in S_f}\mathcal{S}(F_v)$ tensor factor and the linear topological isomorphism of Proposition 2.1.4.1(1), which is compatible with the left-translation action $\mathrm{GL}_1(\mathbf{A}_{F,S})$ on the source, and the action of each of the factors $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ and $\prod_{v\in S_f}F_v^{\times}$ on the target.

We therefore let $N^{\mathbf{Z}}$ act on $\mathcal{S}(\mathbf{A}_{F,S})$ as $\mathrm{Id}_{\mathcal{S}(\mathbf{A}_{F,S_\infty})}\otimes N$ (where we denote by “$N$” the action of the element $N\in N^{\mathbf{Z}}\subset\prod_{v\in S_f}F_v$ on $\bigotimes_{v\in S_f}\mathcal{S}(F_v)$).

This action of $N^{\mathbf{Z}}$ on $\mathcal{S}(\mathbf{A}_{F,S})$ is continuous, and therefore sends bounded subsets to bounded subsets. We may rename the pre-image of $\mathcal{B}$ under the action of $N^{-1}$ as $\mathcal{B}$, and assume, without loss of generality, that $K=\widehat{\mathcal{O}}_{F,S}$.

We choose a continuous homomorphic section $\tau$ to the $S$-idelic norm. By connectedness of $\tau(\mathbf{R}_{>0})$, its image is contained in the closed subgroup $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})\times\{1\}\subset\mathrm{GL}_1(\mathbf{A}_{F,S})$.

For any real number $M>0$ and any integer $N\ge 2$, there exists a large enough ball $B\subset\mathbf{A}_{F,\infty}$ centered at the origin (the normed structure $\|\cdot\|$ on $\mathbf{A}_{F,S_\infty}$ being any one inducing the Euclidean product topology on $\mathbf{A}_{F,S_\infty}$) such that:

$$
\sup_{x\in\mathbf{A}_{F,S_\infty}-B}|f_\infty(x_\infty)|<M\|x_\infty\|^{-N} \tag{2.4.2.2}
$$

for every element $f_\infty\in\mathcal{B}_\infty$ (since $\sup_{x\in\mathbf{A}_{F,S_\infty}}|\cdot|$ is a continuous seminorm on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$), upon denoting $x_\infty$ the arbitrary point of $\mathbf{A}_{F,S_\infty}$.

## PDF page 112

**112** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

Since $J^1_{F,S}=\mathrm{GL}_1(\mathbf{A}_{F,S})^1/\mathcal{O}_{F,S}^{\times}$ is compact Hausdorff, the function of $(t,g)$ defined as:

$$
\Psi_{F,S,B}(f)(t,g):=\sum_{\xi\in\mathcal{O}_{F,S}^{\times}}f(\xi\tau(t)g)\cdot(1_{B^c}\otimes 1_{\widehat{\mathcal{O}}_{F,S}})(\xi\tau(t)g)
$$

for $1_{B^c}$ the indicator function of $B^c:=\mathbf{A}_{F,S_\infty}-B$, satisfies, in light of (2.4.2.2):

$$
|\Psi_{F,S,B}(f)(t,g)|=O(1) \tag{2.4.2.3}
$$

for all $(t,g)\in\mathbf{R}_{>0}\times J^1_{F,S}$, with an implied constant that depends on $f$ only through $\mathcal{B}$.

We define $A:=\sup_{f_\infty\in\mathcal{B}_\infty}\sup_{\tau(t)g\in B}|f_\infty(\tau(t)g)|$. The supremum defining $A$ exists and it is finite because $\sup_{x\in B}|\cdot|$, is a countinuous seminorm on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$ and $\mathcal{B}_\infty$ is bounded.

We may further replace $B$ with a hypercube containing $B$, i.e. $Q\subset\mathbf{A}_{F,S_\infty}$ of the form

$$
Q=\prod_{v\ \mathrm{real}}[-C_v,C_v]\times\prod_{v\ \mathrm{complex}}([-C_v,C_v]+i[-C_v,C_v]),
$$

for real numbers $C_v>0$ for each Archimedean place $v$ of $F$.

Up to changing the constants $C_{\mathcal{B},N}$ and $T_{\mathcal{B},N}$, we may further assume $A=1$ without loss of generality.

Up to acting on $\mathbf{A}_{F,S_\infty}$ by left-translation by the elements of $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$, each of which defines a continuous linear topological automorphism on $\mathcal{S}(\mathbf{A}_{F,S_\infty})$, hence sending bounded subsets to bounded subsets, we may and do assume $Q$ is the hypercube:

$$
Q=\{x\in\mathbf{A}_{F,S_\infty}:|x|_v\le 1, v\in S_\infty\}.
$$

It follows that it is enough to estimate

$$
\sum_{\xi\in\mathcal{O}_{F,S}^{\times}}u(\xi\tau(t)g)
$$

as a function of $(t,g)\in\mathbf{R}_{>0}\times E_{S,0}$, with $u:=1_Q\otimes 1_{\widehat{\mathcal{O}}_{F,S}}$, i.e. the indicator function of $\{x\in\mathbf{A}_{F,S}:|x|_v\le 1, v\in S\}$, and $E_{S,0}$ the $S$-idelic fundamental domain from (A.2.4.5) of Definition A.2.4.3.

Since $u$ is real-valued and nonnegative, it is therefore enough to show the following: there exist $C,T>0$ such that:

$$
\left|\sum_{\xi\in\mathcal{O}_{F,S}^{\times}}\int_{E_{S,0}}(1_Q\otimes 1_{\widehat{\mathcal{O}}_{F,S}})(\xi\tau(x)g_0)\,\mathrm{d}\bar{\mu}_{S,1}(g_0)\right|\le C\,|\log(t)|^{|S|-1} \tag{2.4.2.4}
$$

for all $t\in\mathbf{R}_{>0}$ such that $t<T$. This, in turn, holds by Theorem A.4.1.1.

We call $C_{\mathcal{B},1}:=C_{\mathcal{B},N}$.

We now call, upon denoting by $T>0$ the constant $T:=T_{\mathcal{B},N}$ obtained from the foregoing, $t:=\max\{T,1/T\}$, and observe that the proof of Proposition 2.3.1.2(4), implies that for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ such that $g\in\tau([1/t,t])\cdot E^1_{F,S}$, for $E^1_{F,S}$ the $S$-idelic fundamental domain from (A.2.4.4) for the continuous left-translation action of the $S$-units $\mathcal{O}_{F,S}^{\times}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, the estimate:

$$
|\Phi_{F,S}(f)(g)|\le C \tag{2.4.2.5}
$$

holds for all $f\in\mathcal{B}$, for a positive real number $C>0$ depending only on $\mathcal{B}$ and $t>0$. Upon defining $C_{\mathcal{B},2}:=\max\{C_{\mathcal{B},1}|\log(t)|,C\}$, we obtain that the estimate in (2.4.2.1), for the constant $C_{\mathcal{B},2}$ defined above, and for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ such $|g|_{F,S}<1$. $\square$

**2.4.3. Order of growth as $|g|_{F,S}\to 0^+$.** We will now collect two consequences of Theorem 2.4.2.1 concerning the asymptotic behavior of the $S$-local adelic $\theta$-functions as $|g|_{F,S}\to 0^+$, to be used in the subsequent

## PDF page 113

**2.4. ASYMPTOTIC BEHAVIOR AS $|g|_{F,S}\to 0^+$ BY LATTICE POINT-COUNTING** · **113**

two Chapters in combination with the local functional equations from [CF, Ch.XV,§2.4,Thm.2.4.1,p.315] and of simpler applicability.

PROPOSITION 2.4.3.1. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places. Let $f\in\mathcal{S}(\mathbf{A}_{F,S})$.*

*We have:*

(1) *for every $\varepsilon>0$:*

$$
\Phi_{F,S}(f)(g)|g|_{F,S}^{\varepsilon}=O_{\varepsilon}(1) \tag{2.4.3.1}
$$

*for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ as $|g|_{F,S}\to 0^+$, and the same holds for $\Phi_{F,S,\omega}(f)(g)|g|_{F,S}^{\varepsilon}$ for any continuous character $\omega$ of $J^1_{F,S}$.*

(2) *For $\mathcal{B}\subset\mathcal{S}(\mathbf{A}_{F,S})$ a bounded subset, there exists a real number $T_{\mathcal{B},\varepsilon}>0$ such that (2.4.3.1) holds with an implied constant that is uniform with respect to $f$ varying over $\mathcal{B}$, and for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ such that $|g|_{F,S}<T_{\mathcal{B},\varepsilon}$. The same holds for $\Phi_{F,S,\omega}(f)(g)|g|_{F,S}^{\varepsilon}$ for any continuous character $\omega$ of $J^1_{F,S}$.*

(3) *The assertions in (2) holds with $T_{\mathcal{B},\varepsilon}=1$, upon replacing the implied constant in (2.4.3.1) with a possibly larger constant depending on $\varepsilon>0$, and which is still uniform with respect to $f$ varying over the bounded subset $\mathcal{B}$.*

A similar result on the growth of the $S$-local adelic $\theta$-functions as $|g|_{F,S}\to 0^+$ is present in R. Meyer’s [Me, §4]. We refer the reader specifically to the beginning of the section, on [Me, §4,p.22], where the space $\mathcal{T}_S$ in loc.cit. is characterized. Its elements can be equivalently described as $S$-local adelic $\theta$-functions. This will follow as a consequence of Theorem 5.4.1.1 from Chapter 4 (i.e. the characterization will be a Theorem, and is not taken as our definition of the analog of Meyer’s $\mathcal{T}_S$ throughout this work, which will instead be introduced as a quotient of the Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}(\mathbf{A}_{F,S})$; see Definition 5.1.1.1 from §5.1.1).

PROOF OF PROPOSITION 2.4.3.1. (1) : We consider the function:

$$
\phi(t,g):=\Phi_{F,S}(f)(\tau(t)g)\omega(g)
$$

of $(t,g)\in\mathbf{R}_{>0}\times\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

By Proposition 2.3.2.2, $\phi(\cdot,g)$ is smooth on $\mathbf{R}_{>0}$ for every $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, and the derivative $(t\partial_t)\phi$ is a continuous function of $(t,g)$ on $\mathbf{R}_{>0}\times\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

Differentiation in the $t$-variable yields:

$$
(x\partial_x)(\phi(x,g)x^{\varepsilon})=x\{\phi'(x,g)x^{\varepsilon}+\varepsilon\phi(x,g)x^{\varepsilon-1}\}=(x\partial_x)(\phi)(x,g)x^{\varepsilon}+\varepsilon\phi(x,g)x^{\varepsilon}.
$$

By the Fundamental Theorem of Calculus, we have:

$$
\phi(t,g)t^{\varepsilon}=-\int_t^{+\infty}(x\partial_x)(\phi(x,g)x^{\varepsilon})\frac{\mathrm{d}x}{x}
$$

for every $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, and hence

$$
|\phi(t,g)t^{\varepsilon}|\le\int_{\mathbf{R}_{>0}}|(x\partial_x\phi)(x,g)x^{\varepsilon}|\frac{\mathrm{d}x}{x}+\varepsilon\int_{\mathbf{R}_{>0}}|\phi(x,g)x^{\varepsilon}|\frac{\mathrm{d}x}{x} \tag{2.4.3.2}
$$

for all $t\in\mathbf{R}_{>0}$.

By Proposition 2.3.2.2, we have $(t\partial_t\phi)(t,g)=\Phi_{F,S}(\partial_{\gamma_\tau}f)(\tau(t)g)$, for $\gamma_\tau:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_{F,S})$ the continuous 1-parameter subgroup that is $\tau$ by another name.

Both integrals in (2.4.3.2) are finite, since, by Proposition 2.3.1.4(2), both $(t\partial_t\phi)$ and $\phi$ are $O_N(t^{-N})$ for every integer $N\ge 1$ as $t\to+\infty$, and by Theorem 2.4.2.1 the singularity of $\phi(t,g)t^{\varepsilon-1}$ as $t\to 0^+$, and of $(t\partial_t)\phi(t,g)t^{\varepsilon-1}$ as $t\to 0^+$, is $\mathrm{d}t$-integrable over $(0,A]$ for every $A>0$, for all $\varepsilon>0$.

## PDF page 114

**114** · **CHAPTER 2. ADELIC $\theta$-FUNCTIONS**

By Dominated Convergence, formation of both integrals in (2.4.3.2) is continuous as a function of $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, and since $\phi(t,g)$ is $\mathcal{O}_{F,S}^{\times}$-invariant as a function of $(t,g)\in\mathbf{R}_{>0}\times\mathrm{GL}_1(\mathbf{A}_{F,S})^1$ with $\mathcal{O}_{F,S}^{\times}$ acting on the second factor, we may maximize the right side of (2.4.3.2) as a function of $g$ over $E_{S,0}$, which is relatively compact and with non-empty interior, to obtain:

$$
|\Phi_{F,S}(f)(g)|g|_{F,S}^{\varepsilon}|\le\sup_{(t,g')\in\mathbf{R}_{>0}\times E_{S,0}}|\phi(t,g')|g'|_{F,S}^{\varepsilon}|<+\infty \tag{2.4.3.3}
$$

where the inequality in (2.4.3.3) is valid for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$, since $\Phi_{F,S}(f)$ and $|\cdot|_{F,S}$ are both $\mathcal{O}_{F,S}^{\times}$-invariant functions on $\mathrm{GL}_1(\mathbf{A}_{F,S})$. This shows that (2.4.3.1) holds.

We consider the function:

$$
\phi(t):=\int_{J^1_{F,S}}\Phi_{F,S}(f)(\tau(t)g)\omega(g)\,\mathrm{d}\bar{\mu}_{S,1}(g)
$$

a function on $\mathbf{R}_{>0}$.

By Proposition 2.3.2.2, $\phi$ is smooth on $\mathbf{R}_{>0}$.

By the Fundamental Theorem of Calculus, we have:

$$
\phi(t)t^{\varepsilon}=-\int_t^{+\infty}(x\partial_x)(\phi(x)x^{\varepsilon})\frac{\mathrm{d}x}{x}
$$

and hence

$$
|\phi(t)t^{\varepsilon}|\le\int_{\mathbf{R}_{>0}}|(x\partial_x\phi)(x)x^{\varepsilon}|\frac{\mathrm{d}x}{x}+\varepsilon\int_{\mathbf{R}_{>0}}|\phi(x)x^{\varepsilon}|\frac{\mathrm{d}x}{x} \tag{2.4.3.4}
$$

for all $t\in\mathbf{R}_{>0}$.

By Proposition 2.3.2.2, we have $(t\partial_t\phi)(t)=\Phi_{F,S,\omega}(\partial_{\gamma_\tau}f)(\tau(t))$, for $\gamma_\tau:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_{F,S})$ the continuous 1-parameter subgroup induced by $\tau$.

Both integrals in (2.4.3.4) are finite, since, by Proposition 2.3.1.4(2), both $(t\partial_t\phi)$ and $\phi$ are $O_N(t^{-N})$ for every integer $N\ge 1$ as $t\to+\infty$, and the singularity of $\phi(t)t^{\varepsilon-1}$ as $t\to 0^+$ and of $(t\partial_t)\phi(t)t^{\varepsilon-1}$ as $t\to 0^+$, is $\mathrm{d}t$-integrable over $(0,A]$ for every $A>0$, for all $\varepsilon>0$, by Theorem 2.4.2.1.

We deduce from (2.4.3.4) that we have:

$$
|\phi(t)t^{\varepsilon}|\le A
$$

for all $t\in\mathbf{R}_{>0}$.

(2) : The uniformity assertion on the implied constant follows from Theorem 2.4.2.1. Indeed, for all $f\in\mathcal{B}$, we can use the constants $C_{\mathcal{B},\varepsilon}$ and $T_{\mathcal{B},\varepsilon}$ to bound the integral of the singularity of $\Phi_{F,S}(f)$ uniformly over $J^{<T_{\mathcal{B},\varepsilon}}_{F,S}$, and formation of the integral $\int_{J^{\ge T_{\mathcal{B},\varepsilon}}_{F,S}}|\Phi_{F,S}(f)(g)|g|_{F,S}^{\varepsilon}|\,\mathrm{d}\bar{\mu}_S(g)$ is sequentially continuous over $\mathcal{S}(\mathbf{A}_{F,S})$ by Dominated Convergence, and hence continuous by [NB, Thm.14.7.3], since $\mathcal{S}(\mathbf{A}_{F,S})$ is a strict LF-space by Proposition 2.1.4.1(2), hence bornological (see [Scha, Ch.II,§8,Cor.1,p.62]) and ultrabornological (see [NB, Thm.13.2.12]), and the target Hausdorff locally convex topological $\mathbf{C}$-vector space of the linear operator $f\mapsto 1_{J^{\ge T_{\mathcal{B},\varepsilon}}_{F,S}}(g)\cdot\Phi_{F,S}(f)(g)|g|_{F,S}^{\varepsilon}$ is $L^1(J_{F,S},\bar{\mu}_S)$, which is webbed by [NB, Thm.14.6.2] being a complete normed space, and hence [NB, Thm.13.2.12] applies.

In particular, the integral $\int_{J^{\ge T_{\mathcal{B},\varepsilon}}_{F,S}}|\Phi_{F,S}(f)(g)|g|_{F,S}^{\varepsilon}|\,\mathrm{d}\bar{\mu}_S(g)$ is uniformly bounded as $f$ varies over the bounded subset $\mathcal{B}$: indeed, the function $\alpha:f\mapsto\int_{J^{\ge T_{\mathcal{B},\varepsilon}}_{F,S}}|\Phi_{F,S}(f)(g)|g|_{F,S}^{\varepsilon}|\,\mathrm{d}\bar{\mu}_S(g)$ is continuous and complex-valued on $\mathcal{S}(\mathbf{A}_{F,S})$ by the foregoing, and since $\mathcal{S}(\mathbf{A}_{F,S})$ is Montel by Proposition 2.1.4.1(2), it has the Heine-Borel property, and hence the closure of $\mathcal{B}$, also bounded by [Scha, Ch.I,§5.1,(ii),p.25], is compact. The continuous function $\alpha$ is therefore bounded on $\mathcal{B}$.

(3) : By Theorem 2.4.2.1, the real number $T_{\mathcal{B},\varepsilon}$ used throughout the proof of (2) can be chosen to be $T_{\mathcal{B},\varepsilon}=1$. $\square$

## PDF page 115

**2.4. ASYMPTOTIC BEHAVIOR AS $|g|_{F,S}\to 0^+$ BY LATTICE POINT-COUNTING** · **115**

COROLLARY 2.4.3.2. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places. Let $f\in\mathcal{S}(\mathbf{A}_{F,S})$.*

*For every real number $\varepsilon>0$, we have:*

$$
|g|_{F,S}^{\varepsilon}\Phi_{F,S}(f)(g)=o_{\varepsilon}(1) \tag{2.4.3.5}
$$

*for all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ as $|g|_{F,S}\to 0^+$, and the same holds for $|g|_{F,S}^{\varepsilon}\Phi_{F,S,\omega}(f)(g)$ for any continuous character $\omega\in\widehat{J^1_{F,S}}$.*

PROOF. Let $\tau$ be a continuous homomorphic section to the $S$-idelic norm.

We deduce from (2.4.3.2) that we have:

$$
|\Phi_{F,S}(f)(\tau(t)g)t^{\varepsilon/2}|\le A_{\varepsilon}
$$

for all $t\in\mathbf{R}_{>0}$ and all $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, and hence:

$$
|\Phi_{F,S}(f)(\tau(t)g)t^{\varepsilon}|\le A_{\varepsilon}\,t^{\varepsilon/2} \tag{2.4.3.6}
$$

for all $t\in\mathbf{R}_{>0}$, where $A_{\varepsilon}$ only depends on $f$ and $\varepsilon>0$ but not on $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, which implies $\sup_{g\in\mathrm{GL}_1(\mathbf{A}_{F,S})^1}|\Phi_{F,S}(\tau(t)g)t^{\varepsilon}|=o_{\varepsilon}(1)$ as $t\to 0^+$. The case of $\Phi_{F,S,\omega}(f)$ is treated in a closely analogous manner, by integration of both sides of (2.4.3.6) over the compact Hausdorff abelian group $J^1_{F,S}$. $\square$

## PDF page 116
