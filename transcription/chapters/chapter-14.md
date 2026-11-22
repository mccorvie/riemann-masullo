## PDF page 523

**CHAPTER 14** · **Complements** · **523**

CHAPTER 14

Complements

14.1. On the multiplicities of the zeros 524

14.1.1. Artin-Weil $L$-functions 524

14.1.2. Expected Multiplicity Bound 528

14.2. The case of global function fields of positive characteristic 534

14.3. The higher rank case 536

**523**

## PDF page 524

**524** · **CHAPTER 14. COMPLEMENTS**

**14.1. On the multiplicities of the zeros**

In this section we record a few complements, and discuss an important sanity check: we explain how the Multiplicity Bound obtained in Theorem 13.3.1.2, is compatible with expectations from Global Langlands and the Grand Simplicity Hypothesis.

We will then explain how the methods discussed throughout this paper, do not adapt to the case of Hecke $L$-functions of global function fields of smooth projective geometrically connected curve $X$ over a finite field $\mathbf F_q$ of positive characteristic $p$.

Specifically, we will be discussing which parts extend to this case, and which, most importantly, do not, and why this is to be expected: briefly, a phenomenon caused by the existence of *maximal curves*, leading to counterexamples to the positive characteristic direct analog of the Simplicity Hypothesis (i.e. that the zeros of the $L$-functions $L(s,\pi)$ attached to cuspidal automorphic representations $\pi$ of $\mathrm{GL}_m$ over $F=\mathbf F_q(t)$ for some integer $m\ge 0$, are simple).

**14.1.1. Artin-Weil $L$-functions.** We let $F$ be a local or global field, and $\overline F$ a fixed choice of separable closure. We denote by $W_F$ any Weil group for $F$. We recall that a Weil group for $F$, is a triple
$$
(W_F,\varphi,\{r_E\}_E)
$$
where $W_F$ is a topological group
$$
\varphi:W_F\to\mathrm{Gal}(\overline F/F)
$$
is a continuous group homomorphism with dense image.

We will be referring to $\varphi$ as the *reciprocity homomorphism*.

For any finite separable sub-extension $E/F$ contained within the chosen $\overline F$, we define $W_E:=\varphi^{-1}(\mathrm{Gal}(\overline F/E))$, noting that since $\varphi$ is continuous, then $W_E\subset W_F$ is an open subgroup of finite index.

If $E/F$ is Galois, then $W_E\subset W_F$ is normal.

Denseness of the image of $\varphi$ ensures that we have a bijection of finite homogeneous spaces:
$$
W_F/W_E\to\mathrm{Gal}(\overline F/F)/\mathrm{Gal}(\overline F/E) \tag{14.1.1.1}
$$
where $E/F$ is a general finite separable extension. In the special case $E/F$ is finite Galois, then this is a group isomorphism.

The collection $\{r_E\}_E$, as $E$ varies over the finite separable extensions of $F$ contained in the chosen $\overline F$, is a family of isomorphisms of Hausdorff locally compact abelian groups:
$$
r_E:C_E\to W_E^{\mathrm{ab}} \tag{14.1.1.2}
$$
where $C_E$ is the idele class group, if $F$ is global, and $C_E=E^\times$, if $F$ is local. For each finite separable extension $E/F$ contained within $\overline F$, $W_E^{\mathrm{ab}}$ is notation for the Hausdorff locally compact abelian quotient of $W_E$ obtained as the quotient of $W_E$ by the closure $W_E^c$ of the commutator subgroup of $W_E$.

We will be referring to the isomorphisms of topological groups $r_E$ from (14.1.1.2) as *abelianization isomorphisms*.

The triple $(W_F,\varphi,\{r_E\}_E)$ is assumed to satisfy a collection of axioms, for which we refer the reader to [Tate, §1]. Most importantly, the composition of $r_E$ followed by the unique continuous group homomorphism $W_E^{\mathrm{ab}}\to\mathrm{Gal}(\overline F/E)^{\mathrm{ab}}$ induced by $\varphi$, is assumed to agree with Artin’s Reciprocity map $\mathrm{Art}_E$ from Class Field Theory.

We define, for any finite Galois extension $E/F$ contained within the chosen $\overline F$:
$$
W_{E/F}:=W_F/W_E^c \tag{14.1.1.3}
$$
equipped with the quotient topology, where $W_E^c$ again denotes the closure of the commutator subgroup of $W_E$.

## PDF page 525

**14.1. ON THE MULTIPLICITIES OF THE ZEROS** · **525**

We refer the reader to [Tate, §1,pp.3,4], to Artin and Tate’s treatise on Class Field Theory (see [AT, Ch.XV,Thm.7,p.179] and [AT, Ch.V,Thm.11,p.186]), and to Weil’s own work on the Explicit Formulas (see [Weil-e, §1,6] (where Weil groups are termed $W$-groups) and [Weil-f, §II,V]) where Weil groups are constructed and introduces a generalization of Artin $L$-functions associated to continuous finite dimensional complex representations of $W_F$, for $F$ a global field.

We further refer the reader to Langlands’ notes on Artin $L$-functions (see [Langlands, Ch.20]), where Weil’s generalization of Artin $L$-functions is defined and their basic properties summarized.

The construction of the Weil group $W_F$ is carried out in [AT, Ch.XV] and rests upon the formalism of (topological class formations). The group $W_{E/F}$ is a topological extension of $\mathrm{Gal}(E/F)$ by $C_E$, classified by a class $\alpha_{E/F}\in \mathrm{H}^2(\mathrm{Gal}(E/F),C_E)$, which turns out to agree (granting the existence of a Weil group for the topological class formation [AT, Ch.XV,Def.3,p.175]) with the fundamental class of Class Field Theory, or can be defined to be such fundamental class, for then deducing the existence of a Weil group as a projective limit topological group of the extensions classified by $\alpha_{E/F}$, whose properties and functorialities follow from the cohomological formalism discussed in [AT, Ch.XIII,XIV].

We collect the most important facts about Weil groups throughout the Proposition below:

PROPOSITION 14.1.1.1. *Let $F$ be either a global field, or a local field. We fix a separable closure $\overline F$ of $F$. Let $(W_F,\varphi,\{r_E\}_E)$ be a Weil group for $F$. Then:*

*(1) For every finite Galois extension $E/F$ contained in $\overline F$, the topological group $W_{E/F}$ is a central extension:*
$$
1\to C_E\to W_{E/F}\to\mathrm{Gal}(E/F)\to 1 \tag{14.1.1.4}
$$
*the leftmost group homomorphism being continuous and with closed image, and the rightmost being continuous and open upon endowing $\mathrm{Gal}(E/F)$ with the discrete topology.*

*(2) There is a canonical continuous homomorphism:*
$$
W_F\to\varprojlim_{E/F}W_{E/F} \tag{14.1.1.5}
$$
*as $E$ varies over the finite separable sub-extensions of $F$ contained within $\overline F$, which is an isomorphism of topological groups.*

*(3) If $F$ is global, for any place $v$ of $F$, upon denoting $\overline F_v$ a choice of separable closure of the local field $F_v$, and for any $F$-homomorphism $i_v:\overline F\to\overline F_v$, we define, for each finite extension $E/F$ contained within $\overline F$, $E_v:=i(E)F_v$. There exists a continuous injective homomorphism:*
$$
\theta_v:W_{F_v}\to W_F \tag{14.1.1.6}
$$
*compatible with reciprocity homomorphisms and abelianization isomorphisms.*

*(4) Let $\rho:W_F\to\mathrm{GL}(V)$ be a finite dimensional continuous complex representation of $W_F$. Then there exists a large enough finite Galois extension $E/F$ contained within $\overline F$ such that $\rho$ factors through a unique continuous representation $\rho_E:W_{E/F}\to\mathrm{GL}(V)$.*

*(5) Let $\rho:W_F\to\mathrm{GL}(V)$ be a finite dimensional continuous complex representation of $W_F$. Assume $\rho$ is irreducible. Then:*

*(a) If $V$ is not induced by a proper subgroup of $W_F$, then there exists a continuous quasi-character $c\in\Omega(C_F)$ and a continuous representation $\rho_0:\mathrm{Gal}(\overline F/F)\to\mathrm{GL}(V)$ such that $\rho=(\rho_0\circ\varphi)\otimes c$.*

*(b) For any finite separable extension $E/F$ contained within $\overline F$, the induced representation $\mathrm{Ind}_{W_E}^{W_F}(\rho)$ is semisimple.*

*(c) If $\rho$ is one-dimensional, then for any finite separable extension $E/F$ contained within $\overline F$, the induced representation $\rho':=\mathrm{Ind}_{W_E}^{W_F}(\rho)$ satisfies the following property: for every element $g\in W_F$, $\rho'(g)$ is semisimple.*

## PDF page 526

**526** · **CHAPTER 14. COMPLEMENTS**

PROOF. (1) : This is a consequence of [AT, Ch.XV,Thm.7,p.179] and [AT, Ch.XV,Def.3,(W3),p.176].

(2) : This is a consequence of [AT, Ch.XV,Thm.7,p.179] and [AT, Ch.XV,Def.3,(W4),p.176].

(3) : This is [Tate, §1.6,Prop.1.6.1,p.8].

(4) : Let $U\subset\mathrm{GL}(V)$ be an open unit-neighborhood, small enough so as to have that no non-trivial subgroup of $\mathrm{GL}(V)$ is contained in $U$. Then $\rho^{-1}(U)$ is open and by (2) it contains $W_E$ for a large enough finite Galois extension $E/F$ contained within the chosen $\overline F$. It follows that $\rho(W_E^c)$ is trivial, and hence $\rho$ factors through $W_{E/F}$.

(5) : We let $E/F$ be a large enough finite Galois extension contained within $\overline F$, such that $\rho$ factors through $W_{E/F}$. By [Weil-e, Lemma 1], there exists a finite group $\Gamma$ which is a central extension of $\mathrm{Gal}(E/F)$ by a cyclic group, and a representation $\rho_0:\Gamma\to\mathrm{GL}(V)$, such that $\rho(W_F)\subset\rho_0(\Gamma)\cdot Z$, for $Z$ the center of $\mathrm{GL}(V)$. It follows that we have $\rho(W_E^{\mathrm{ab}})\subset Z$. Since $\rho(W_E^c)=1$ and $\rho(W_E^{\mathrm{ab}})\subset Z$, we deduce that we have $\rho(W_E)\subset Z$, and hence the composition of $\rho$ followed by the quotient $\mathrm{GL}(V)\to\mathrm{PGL}(V)$ annihilates $W_E$. The remainder of the argument in [Tate, §2,(2.2.3),p.10] applies and proves (a).

Upon calling $E'$ the Galois closure in $\overline F$ of the finite separable extension $E/F$ from (b), then $E'/F$ is finite Galois, and $W_{E'}\subset W_E$, with $W_{E'}\subset W_F$ a normal subgroup of finite index. $\mathrm{Ind}_{W_E}^{W_F}(\rho)$ is a $W_F$-submodule of $\mathrm{Ind}_{W_{E'}}^{W_F}(\rho)$. We rename $E'$ as $E$ and assume $E$ is a finite Galois extension of $F$ contained in $\overline F$.

Under this additional assumption, $W_E\subset W_F$ is normal, and hence $\mathrm{Ind}_{W_E}^{W_F}(\rho)$ is semisimple since $\rho$ is irreducible. Part (c) follows from [Langlands, Ch.1,Lemma 1.1,p.5] applied to $G=W_F$, $H=W_E$ and $\sigma=\rho'$.

$\square$

We now review Weil’s generalization of Artin $L$-functions, and recall their main properties. We will then be using them to illustrate how the multiplicity bound obtained in Theorem 13.3.1.1 from the Trace Formula (see Theorem 13.3.1.2) relates to expectations from the literature, with particular emphasis on Global Langlands, as well as heuristics around pair correlation conjectures and the Grand Simplicity Hypothesis.

Let $F$ be a global field, and $E/F$ a finite Galois extension.

We fix a choice $\overline F$ of separable closure, and for each finite place $v$ of $E$, $\overline E_v$ a choice of separable closure of the non-Archimedean local field $E_v$.

We denote by $v_0$ the unique finite place of $F$ of which $v$ is an extension to $E$. Then $E_v$ is a finite Galois extension of $F_{v_0}$ contained in $\overline E_v$.

The local Weil group $W_{E_v/F_{v_0}}$ is equipped with a ramification filtration inherited from the local Galois group. We refer the reader to [Langlands, Ch.6,p.23], where the upper-numbering filtration is defined, resting on the upper-numbering ramification filtration on $G_{E_v/F_{v_0}}:=\mathrm{Gal}(E_v/F_{v_0})$ from [Se, Ch.IV,§2,3].

We refer the reader to [Langlands, Ch.6] for the definition and properties of $W_{E_v/F_{v_0}}^u$, for each real number $u\ge -1$, a closed normal subgroup (by [Langlands, §6,Lemma 6.11], [Langlands, §6,Lemma 6.12] and [Langlands, Ch.6,Lemma 6.13], which establishes stability under the group operation and normality, while $W_{E_v/F_{v_0}}^u$ being closed follows from the definition of the function $v_{E_v/F_{v_0}}$ from the discussion preceding [Langlands, Ch.6,Lemma 6.11]).

Since $E_v^\times\subset W_{E_v/F_{v_0}}$ is a normal subgroup of finite index, then if $\rho:W_{E_v/F_{v_0}}\to\mathrm{GL}(V)$ is a finite dimensional continuous complex representation of $W_{E_v/F_{v_0}}$ such that every element of $W_{E_v/F_{v_0}}$ maps to a semisimple element of $\mathrm{GL}(V)$, it is semisimple.

It is a finite direct sum of $1$-dimensional continuous representations of $W_{E_v/F_{v_0}}$, since it is a continuous $W_{E_v/F_{v_0}}$-submodule of the induced representation $\mathrm{Ind}_{E_v^\times}^{W_{E_v/F_{v_0}}}(V_0)$, where $V_0$ is the restriction to $E_v^\times$ of the continuous representation $V$ of $W_{E_v/F_{v_0}}$. We further refer the reader to [Langlands, Ch.1,Lemma 1.1,p.5].

We will, throughout the rest of this subsection and following both [Langlands, Ch.1] and [Weil-f, §VI,p.31], be assuming that continuous finite dimensional complex representations $V$ of local and global Weil groups map each element to a semisimple element of $\mathrm{GL}(V)$.

## PDF page 527

**14.1. ON THE MULTIPLICITIES OF THE ZEROS** · **527**

Upon denoting by $V^0$ the linear subspace of those elements of $V$ fixed by the normal closed subgroup $W_{E_v/F_{v_0}}^0\subset W_{E_v/F_{v_0}}$ (which, in case $\rho$ factors through $\mathrm{Gal}(E_v/F_{v_0})$, recovers the subspace of inertial invariants), $V^0$ inherits a structure of continuous finite dimensional complex representation $\rho_0$ of $W_{E_v/F_{v_0}}$ from $V$. It is therefore itself a finite direct sum of $1$-dimensional continuous complex representations of $W_{E_v/F_{v_0}}$, i.e., by (14.1.1.2), we have:
$$
r_E^*\rho_0\simeq\bigoplus_{1\le k\le\dim(V)}c_{v,k}
$$
for continuous quasi-characters $c_{v,k}$ of $E_v^\times$. By design of $V^0$, all such quasi-characters are unramified.

We define the *local Artin-Weil $L$-function* to be the meromorphic function:
$$
L_v(s,\rho):=\prod_{1\le k\le\dim(V)}\frac{1}{1-c_{v,k}(\pi_v)|\pi_v|_v^s} \tag{14.1.1.7}
$$
holomorphic for $\mathrm{Re}(s)>0$.

If $v$ is an Archimedean place of $E$, then, upon denoting by $v_0$ the unique Archimedean place of $F$ of which $v$ is an extension to $E$, and $E_v$, $F_{v_0}$ the respective completions, then $W_{E_v/F_v}$ is isomorphic, as a Hausdorff locally compact topological group, to either $\mathbf C^\times$, or a central extension of $\mu_2$ by $\mathbf C^\times$.

In either case, finite dimensional continuous representations of $W_{E_v/F_v}$ and their local Artin-Weil $L$-functions are defined explicitly (we refer the reader to [Langlands, Ch.20,p.212]).

Global Artin-Weil $L$-functions are then defined as follows. Let $\rho:W_{E/F}\to\mathrm{GL}(V)$ be a finite dimensional continuous complex representation. We denote by $\rho_v$ the continuous finite dimensional complex representation of $W_{E_v/F_{v_0}}$ for each place $v$ of $E$, obtained by composition with $\theta_v$ from (14.1.1.6) of Proposition 14.1.1.1(3).

Over the half-plane $\mathbf C_{>A}$ for large enough $A>1$, the product:
$$
L(s,\rho):=\prod_{v\in\Sigma_E}L_v(s,\rho_v) \tag{14.1.1.8}
$$
converges absolutely and uniformly (see [Langlands, Ch.20,p.213]).

If $\rho:W_F\to\mathrm{GL}(V)$ is a continuous finite dimensional representation of $W_F$, there exists, in light of Proposition 14.1.1.1(4), a large enough finite Galois extension $E/F$ contained within $\overline F$, such that $\rho$ factors through $\rho_E:W_{E/F}\to\mathrm{GL}(V)$. We define
$$
L(s,\rho):=L(s,\rho_E) \tag{14.1.1.9}
$$
and observe that this definition is independent of the choice of such $E$ (i.e. formation of $L(s,\rho_E)$, for $E/F$ finite Galois, is stable under inflation).

For $\rho^\vee$ the contragradient representation on $V^*=V'$, the global Artin-Weil $L$-function $L(s,\rho)$ satisfies the functional equation:
$$
L(s,\rho)=\epsilon(s,\rho)L(1-s,\rho^\vee). \tag{14.1.1.10}
$$
This is proved in [Langlands, Ch.21] (see [Langlands, Introduction,Thm.B,p.vii], where (14.1.1.10) is stated, after automorphic normalization); see also [Tate, §3,Thm.3.4.1,p.14] for the existence of the $\epsilon$-factors, and [Tate, §3,Thm.3.5.3,p.16] for the functional equation.

The function $\epsilon(s,\rho)$ is an inexplicit nowhere vanishing entire function on the complex $s$-plane, defined as the product:
$$
\epsilon(s,\rho):=\prod_{v\in\Sigma_F}\epsilon_v(s,\rho_v)
$$
where each $\epsilon_v(s,\rho_v)$ is $1$ with the exception of at most finitely many places $v$ of $F$, and further depends on a choice of local additive character $\psi_v$ of $F_v$. The existence, uniqueness and properties of each $\epsilon_v(s,\rho_v)$ is recalled in [Langlands, Introduction,Thm.A,p.vii].

## PDF page 528

**528** · **CHAPTER 14. COMPLEMENTS**

The functional equation in (14.1.1.10) implies that $L(s,\rho)$ extends to a meromorphic function on the complex $s$-plane.

If $\rho$ is $1$-dimensional, then $\rho$ factors through $W_F^{\mathrm{ab}}$, and hence $r_F^*\rho$ is a continuous quasi-character $c_\rho$ of $C_F$. We have:
$$
L(s,\rho)=L(c_\rho|\cdot|_F^s) \tag{14.1.1.11}
$$
as meromorphic functions on the complex $s$-plane.

For $\rho=\rho_1\oplus\rho_2$, with $\rho_1$, $\rho_2$ two continuous finite dimensional complex representations of $W_F$, we have:
$$
L(s,\rho)=L(s,\rho_1)L(s,\rho_2) \tag{14.1.1.12}
$$
as meromorphic functions on the complex $s$-plane.

If $F'/E/F$ are two finite separable extensions contained within $\overline F$, with $F'/E$ and $F'/F$ Galois, then we may induce a continuous finite dimensional complex representation $\rho:W_{F'/E}\to\mathrm{GL}(V)$ to $\mathrm{Ind}_{W_{F'/E}}^{W_{F'/F}}(\rho):W_{F'/F}\to\mathrm{GL}(V)$, and we have:
$$
L(s,\rho)=L(s,\mathrm{Ind}_{W_{F'/E}}^{W_{F'/F}}(\rho)) \tag{14.1.1.13}
$$
as meromorphic functions on the complex $s$-plane, i.e. formation of global Artin-Weil $L$-functions is inductive (the same property holds for local Artin-Weil $L$-functions, and implies (14.1.1.13)).

We refer the reader to [Weil-f, §VI,p.32].

In the special case of $\rho$ is Galois type, i.e. of the form $|\cdot|_F^z\rho_0$ for some $z\in\mathbf C$ and for $\rho_0:W_F\to\mathrm{GL}(V)$ of the form $\rho_1\circ\varphi$ with $\rho_1$ a finite dimensional complex Galois representation, i.e. an Artin representation, then $L(s,\rho)=L(s+z,\rho_1)$ where $L(s,\rho_1)$ is the Artin $L$-function of $\rho_0$, and the properties recalled in (14.1.1.11), (14.1.1.12) and (14.1.1.13), including the functional equation from (14.1.1.10), extend those of the Artin $L$-function $L(\rho_1,s)$ (we further refer the reader to [Art-2], and to [Murty, §1] for more on such properties of Artin $L$-functions).

We further refer the reader to [Tate, §3] for a discussion of Artin-Weil $L$-functions, and to [Tate, §3,Thm.3.5.3,p.16] for the meromorphic continuation and functional equation of Artin-Weil $L$-functions, for a discussion of Artin-Weil $L$-functions. Specifically, to [Tate, §3,(3.6),p.17] for the difference between Langlands’ $\epsilon$-factors and Deligne’s (see [Del]).

The $L$-functions defined in this subsection agree with the generalized Artin $L$-functions defined by Weil, for whose properties we further refer the reader to [Weil-f, §VI,p.25].

**14.1.2. Expected Multiplicity Bound.** Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character.$^1$

The Trace Formula (Theorem 13.3.1.1) reveals constraints on the multiplicity of the non-trivial zeros of the Hecke $L$-function $L(s,\chi)$, although not all of them. Indeed, Theorem 13.3.1.2, a consequence of the Trace Formula combined with the Positivity Criterion (in its form from Theorem ??), asserts that if $\rho\in\mathbf C$ is a non-trivial zero of $L(s,\chi)$, then $\rho\in 1/2+i\mathbf R$, and if, in addition, $\rho\notin\mathbf R$, i.e. $\rho\ne 1/2$, then
$$
N(\rho)\le [F:\mathbf Q]
$$
where $N:\mathbf C\to\mathbf N$ is the multiplicity function of the divisor of $L(s,\chi)$.

In particular, no information is provided on the value of $N(c)$ when $c$ is the central zero. This is due to the assumption on the test functions $\varphi\in\mathcal D(C_F)$ on which the Trace Formula holds, that they should vanish, together with their holomorphic derivatives of order up to $[F:\mathbf Q]-1$, at all the central zeros.

Recall that by *central zero* we mean the unique point of each connected component of the Riemann surface $\Omega(C_F)$, that is of the form $|\cdot|_F^{1/2}c_0$, where $c_0$ is the unique point of each connected component allowed to

$^1$Correct this subsection.

## PDF page 529

**14.1. ON THE MULTIPLICITIES OF THE ZEROS** · **529**

occur as a pole of multiplicity higher than $1$ of the partial Euler products $\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)$ for any finite set $S$ of places of $F$ containing all the Archimedean places.

Upon fixing a continuous homomorphic section $\tau$ to the idelic norm, and calling $x_0\in\mathbf R$ the unique real number such that $\chi(\tau(t))=t^{ix_0}$ as smooth functions on $\mathbf R_{>0}$, then the central zero in the connected component $\Omega(C_F)(\chi|_{C_F^1})$ parametrized according to the holomorphic parametrization
$$
\chi|\cdot|_F^s,\quad s\in\mathbf C
$$
is parametrized by the complex number $s=1/2-ix_0$.

We could of course renormalize our very definition of Hecke $L$-function $L(s,\chi)$ to ensure that this point is located at $s=1/2$, which we have not done throughout this work (such normalization is a generalization of the normalization customarily in force in discussions from the literature concerning Dirichlet $L$-functions and, more generally, the $L$-functions associated to cuspidal automorphic representations of $\mathrm{GL}_n(\mathbf A_{\mathbf Q})$. It is referred to as unitary normalization).

This one point of each connected component of $\Omega(C_F)$ therefore remains mysterious: understanding its multiplicity is beyond the reach of the methods of this work.

We will show in this subsection by means of examples, that in fact it does not obey the multiplicity bound of $[F:\mathbf Q]$ which applies to the other non-trivial zeros. As we do so, we will also show how the multiplicity bound of $[F:\mathbf Q]$ on the non-central non-trivial zeros, is compatible with expectations from Global Langlands and the Grand Simplicity Hypothesis, i.e. it follows as a consequence of a combination of conjectures on automorphic $L$-functions for $\mathrm{GL}_n(\mathbf A_{\mathbf Q})$ for $n\ge 1$.

The following two conjectures can be found in the existing literature on automorphic $L$-functions. We write $L(s,\pi)$ for the completed and unitarily normalized $L$-function of a cuspidal automorphic representation $\pi$ of $\mathrm{GL}_n(\mathbf A_{\mathbf Q})$. In particular, the line of symmetry of the functional equation for $L(s,\pi)$ is $\mathrm{Re}(s)=1/2$, and the central zero of $L(s,\pi)$ is $s=1/2$, with multiplicity $N\ge 0$.

CONJECTURE 14.1.2.1 (GRH and GSH). Let $n\ge 1$ be an integer, and $\pi$ a cuspidal automorphic representation of $\mathrm{GL}_n(\mathbf A_{\mathbf Q})$.

*Then:*

(1) (GRH - Grand Riemann Hypothesis) All the zeros of the $L$-function $L(s,\pi)$ are located on $1/2+i\mathbf R$.

(2) (GSH - Grand Simplicity Hypothesis) With the sole possible exception of $s=1/2$, all the zeros of $L(s,\pi)$ are simple.

Our main references on the Grand Simplicity Hypothesis are the papers by Rudnick-Sarnak and Rubinstein-Sarnak (see [Rud-Sa] and [Ru-Sa, §5,p.195]). The methods contained in the former lead to the observation that the zeros of pairs of (unitarily normalized) completed $L$-functions of cuspidal automorphic representations of $\mathrm{GL}_n(\mathbf A_{\mathbf Q})$ (for possibly distinct integers $n\ge 1$) are, in a precise sense, uncorrelated, with the possible exception of central zeros, if any.

In the latter (see [Ru-Sa, §5,p.195]) expectations on the non existence of relations of algebraic origin on the ordinates of the zeros of the $L$-functions of cuspidal automorphic representations of $\mathrm{GL}_n(\mathbf A_{\mathbf Q})$ are discussed, with the exception of those concerning the existence of central zeros.

To illustrate the phenomenon concerning central zeros, we refer the reader to [Arm], where an example is constructed of an Artin representation $\rho$ of $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$ whose Artin $L$-function $L(s,\rho)$ vanishes at $s=1/2$, leading to an example of a number field $F$ whose Dedekind zeta function $\zeta_F(s)$ vanishes at $s=1/2$ with multiplicity higher than $1$. The existence of the central zero at $s=1/2$ is caused by the sign of the root number in the functional equation for the Artin $L$-functions in the Artin-Takagi factorization of $\zeta_F(s)$.

Serre produced an example of another number field, a quaternionic Galois extension of $\mathbf Q$, with $\zeta_F(1/2)=0$ (see [Ng, Ch.2,§2.5,p.23]).

## PDF page 530

**530** · **CHAPTER 14. COMPLEMENTS**

Central zeros with high multiplicity are, however, expected to not exceed the multiplicity bound of Theorem 13.3.1.2, even though the multiplicity bound of Theorem 13.3.1.2 does not apply to them.

A conjecture of Serre in fact predicts that the Artin $L$-functions of irreducible representations of the Galois group of $\mathbf Q$ have only simple zeros (central zeros being no exception), and expects that a central zero exist if and only if the character of the Artin representation is real and the root number is $-1$. We refer the reader to [Goss, Ch.8,§8.24,Conjecture 8.24.1,p.324] for the statement of Serre’s conjecture.

Some evidence in support of such conjecture of Serre can be found in [Omar, §6].

The question of whether Hecke $L$-functions $L(s,\chi)$ with a central zero whose multiplicity is higher than the degree of the number field, exist, has an affirmative answer. Before exhibiting explicit examples from the theory of CM elliptic curves, we will be showing that the multiplicity bound obtained in Theorem 13.3.1.2 and which applies to all other non-trivial zeros of Hecke $L$-functions apart from central zeros, is compatible with expectations from the literature, and specifically with Conjecture 14.1.2.1, and the Langlands Program.

Let now $\overline{\mathbf Q}$ be a fixed choice of separable closure of $\mathbf Q$. We choose, up to isomorphism, a Weil group $W_{\mathbf Q}$ for $\mathbf Q$ relative to the choice $\overline{\mathbf Q}$, and refer to it as *the* Weil group of $\mathbf Q$.

We further record here a form of Global Langlands for continuous finite dimensional complex representations of the Weil group $W_{\mathbf Q}$ of the field of rational numbers.

CONJECTURE 14.1.2.2 (Global Langlands for $\mathrm{GL}_n(\mathbf A_{\mathbf Q})$ - Weil representations). Let $n\ge 1$ be an integer. Let $\rho:W_{\mathbf Q}\to\mathrm{GL}_n(\mathbf C)$ be a continuous finite dimensional complex representation of the Weil group $W_{\mathbf Q}$. Assume:

*(1) $\rho$ is irreducible.*

(2) For each $g\in W_{\mathbf Q}$, $\rho(g)$ is semisimple.

Then there exists a cuspidal automorphic representation $\pi$ of $\mathrm{GL}_n(\mathbf A_{\mathbf Q})$ such that:
$$
L(s,\rho)=L(s,\pi) \tag{14.1.2.1}
$$
where $L(s,\rho)$ is the Artin-Weil $L$-function of $\rho$, normalized as in the discussion between [Langlands, Introduction,Thm.A,p.vii] and [Langlands, Introduction,Thm.B,p.vii], and $L(s,\pi)$ is the completed and unitarily normalized automorphic $L$-function of $\pi$.

We recall from the previous subsection that Artin-Weil $L$-functions are not assumed to be unitarily normalized throughout this work.

The $L$-functions arising from the Hasse-Weil $L$-functions of elliptic curves will instead have $\mathrm{Re}(s)=1$ as the line of symmetry of their functional equations, as opposed to $\mathrm{Re}(s)=1/2$, in order for this work to adhere with conventions from the literature on Hasse-Weil $L$-functions of elliptic curves (which will serve as our source of examples at the end of this subsection).

We will therefore be mentioning explicitly when such Hasse-Weil $L$-functions are being unitarily normalized.

Both Conjecture 14.1.2.1 and Conjecture 14.1.2.2 serve the sole purpose of instructing us on the expectations from the literature concerning the multiplicity of the zeros of Artin-Weil $L$-functions, for the purposes of testing the multiplicity bound obtained in Theorem 13.3.1.2: such multiplicities are unaffected by unitary normalization.

We will now perform the desired test on the multiplicity bound obtained in Theorem 13.3.1.2.

Assuming Conjecture 14.1.2.1 and Conjecture 14.1.2.2, we will be proving that indeed the bound obtained in Theorem 13.3.1.2 holds as stated, for all non-trivial zeros of Hecke $L$-functions of the number field $F$, with the sole possible exception of the central zero.

We will then be showing by means of examples, constructed using the theory of CM elliptic curves, that the central zero indeed does not obey such bound.

## PDF page 531

**14.1. ON THE MULTIPLICITIES OF THE ZEROS** · **531**

PROPOSITION 14.1.2.3 (Multiplicity Bound, on Global Langlands, GRH and GSH). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character.*

*Assume that Conjecture 14.1.2.1 and Conjecture 14.1.2.2 hold. Let $\rho\in\mathbf C$ be a zero of $L(s,\chi)$, of multiplicity $N(\rho)$.*

*Then:*

*(1) $\rho\in 1/2+i\mathbf R$.*

*(2) If $\rho$ is not the central zero, then $N(\rho)\le [F:\mathbf Q]$.*

REMARK 14.1.2.4. Proposition 14.1.2.3 shows that the Multiplicity Bound obtained in Theorem 13.3.1.2 for the non-central non-trivial zeros of Hecke $L$-functions, is consistent with known expectations from the literature: specifically, the combination of expectations from Global Langlands, and the Grand Simplicity Hypothesis.

PROOF. We choose a separable closure $\overline F$ of $F$, and call $F'$ the Galois closure of $F$ in $\overline F$. $\chi\in\widehat{C_F}$ inflates to a continuous character of $C_{F'}$ by composition with the continuous group homomorphism $i:C_{F'}\to C_F$.

Since $F'/F$ is a finite Galois extension, we have $L(s,\chi)=L(s,\chi')$ for $\chi'=\chi\circ i$ (see [Weil-f, §VI,p.32] applied to $K=k=F$, and $K'=F'$, with $\varphi=\chi$, $\varphi'=\chi'$).

In particular, $\chi'$ as a continuous one-dimensional complex representation of $W_F$, factors through $W_{F'/F}$. We will omit reference to this fact from the notation below.

We have, by (14.1.1.13):
$$
L(s,\chi)=L(s,\chi')=L(s,\mathrm{Ind}_{W_{F'/F}}^{W_{F'/{\mathbf Q}}}(\chi')). \tag{14.1.2.2}
$$

By Proposition 14.1.1.1(5) parts (b) and (c) combined with (14.1.1.12), we have:
$$
L(s,\chi)=\prod_{\lambda}L(s,\lambda)^{n_\lambda} \tag{14.1.2.3}
$$
as $\lambda$ varies over the irreducible sub-representations of $W_{\mathbf Q}$ in $V:=\mathrm{Ind}_{W_{F'/F}}^{W_{F'/{\mathbf Q}}}(\chi')$, and $n_\lambda$ is the multiplicity of $\lambda$ in $V$ (we further refer the reader to Remark 7.1.2.4).

By Conjecture 14.1.2.2, there exists, for each such $\lambda$, and upon denoting by $d_\lambda$ the dimension of $\lambda$, a cuspidal automorphic representation $\pi_\lambda$ of $\mathrm{GL}_{d_\lambda}(\mathbf A_{\mathbf Q})$ such that $L(s,\lambda)=L(s,\pi_\lambda)$ as meromorphic functions on the complex $s$-plane.

By Conjecture 14.1.2.1, the zeros of $L(s,\pi_\lambda)$, with the sole possible exception of the central zero, are simple and located on $1/2+i\mathbf R$.

Since $\chi'$ is one-dimensional, then:
$$
\dim\mathrm{Ind}_{W_{F'/F}}^{W_{F'/{\mathbf Q}}}(\chi')=[F:\mathbf Q]
$$
being the finite homogeneous space $W_{F'/{\mathbf Q}}/W_{F'/F}$ bijective to $\mathrm{Gal}(F'/{\mathbf Q})/\mathrm{Gal}(F'/F)$, which is in turn a finite set of $[F:\mathbf Q]$ elements (see (14.1.1.1)).

It follows that, with the sole possible exception of the central zero, the zeros $\rho$ of $L(s,\chi)$ are also located on $1/2+i\mathbf R$, and satisfy the multiplicity bound $N(\rho)\le [F:\mathbf Q]$.

$\square$

We will now prove the following:

PROPOSITION 14.1.2.5 (Abelian central zeros with high multiplicity). *Assume that for $E_d$ the Mordell curve of affine equation $Y^2=X^3+d$ over $\mathbf Q$, we have:*
$$
\mathrm{rk}\,E_d(F)\le\mathrm{ord}_{s=1}L(E_F/F,s) \tag{14.1.2.4}
$$
*where $F:=\mathbf Q(\sqrt{-3})=\mathbf Q(\zeta_3)$, $L(E_F/F,s)$ is the uncompleted, non-normalized, Hasse-Weil $L$-function of $E_F$, the base change of $E$ to $F$.*

## PDF page 532

**532** · **CHAPTER 14. COMPLEMENTS**

*Then there exists an example of:*

*(1) A continuous character $\chi\in\widehat{C_F}$, algebraic and of infinite order.*

*(2) A cuspidal automorphic representation $\pi$ of $\mathrm{GL}_2(\mathbf A_{\mathbf Q})$.*

*such that $\rho:=\mathrm{Ind}_{W_F}^{W_{\mathbf Q}}(\chi)$ is an irreducible continuous $2$-dimensional complex representation of $W_{\mathbf Q}$, satisfying:*
$$
L(s,\chi)=L(s,\rho)=L(s,\pi) \tag{14.1.2.5}
$$
*the automorphic $L$-function being unitarily normalized, and such that the order of vanishing of $L(s,\chi)$ at $s=1/2$ exceeds $2=[F:\mathbf Q]$.*

REMARK 14.1.2.6. The assumption in (14.1.2.4) follows from the BSD Conjecture for $E_d$. The existence of the examples provided by Proposition 14.1.2.5 is therefore reliant on the BSD Conjecture, or at least on the inequality from (14.1.2.4), for the Mordell curve $E_{16D_1}$ with $D_1$ as defined in [Quer, §1,p.215].

PROOF. Let $E_d$ be the Mordell curve over $\mathbf Q$ given by the affine equation $f(X,Y)=0$ for $f\in\mathbf Z[X,Y]$ defined as:
$$
f(X,Y):=Y^2-X^3-d. \tag{14.1.2.6}
$$
By [Quer, §2,Thm.2,p.216], there exists $d\in\mathbf Z$, $d<0$, such that $\mathrm{rk}\,E_d(\mathbf Q)=12$. By (14.1.2.4), the order of vanishing of $L(E_F/F,s)$ at $s=1$ is at least $\mathrm{rk}\,E_d(F)\ge\mathrm{rk}\,E_d(\mathbf Q)=12$.

We choose $d:=16D_1$, for $D_1$ defined in [Quer, §1,p.215].

The elliptic curve $E:=E_d$ acquires complex multiplication over the imaginary quadratic extension $F:=\mathbf Q(\sqrt{-3})=\mathbf Q(\zeta_3)$, by the ring of integers $\mathcal O_F=\mathbf Z[\zeta_3]$.

By Deuring’s Theorem (see [Silverman, Ch.10,Thm.10.5,p.175]), there exists an algebraic Hecke character $\psi\in\widehat{C_F}$ of exponent $-1/2$, such that:
$$
L(E_F/F,s)=L_f(\psi|\cdot|_F^s)L_f(\overline\psi|\cdot|_F^s) \tag{14.1.2.7}
$$
where $L(E/F,s)$ is the (uncompleted and non-normalized) Hasse-Weil $L$-function of the elliptic curve $E_F$ obtained from $E$ by base change to $F$, and where $L_f(\psi|\cdot|_F^s)$ is the finite Hecke $L$-function $L_f(s-1/2,|\cdot|_F^{1/2}\psi)$, and similarly for $L_f(\overline\psi|\cdot|_F^s)$.

We define $\chi:=|\cdot|_F^{1/2}\psi$, a continuous character of $C_F$. $\chi$ is a unitary algebraic Hecke character of $F$ of infinite order, and the Hecke $L$-function $L(s,\chi)$ vanishes at $s=1/2$ if and only if $L_f(\psi|\cdot|_F)=0$, with matching orders of vanishing at $s=1/2$, respectively $s=1$.

Since $\dim\mathrm{Ind}_{W_F}^{W_{\mathbf Q}}(\chi)=\dim\mathrm{Ind}_{W_F}^{W_{\mathbf Q}}(\overline\chi)=2$, then either $L(s,\chi)$ or $L(s,\overline\chi)$ vanishes at $s=1/2$ with order of vanishing exceeding $2$, since the sum of the respective orders of vanishing must be at least $12$.

Without loss of generality, we assume that this is so for $L(s,\chi)$. We call $\rho:=\mathrm{Ind}_{W_F}^{W_{\mathbf Q}}(\chi)$. This is a continuous irreducible $2$-dimensional complex representation of $W_{\mathbf Q}$. The desired automorphic representation $\pi$ of $\mathrm{GL}_2(\mathbf A_{\mathbf Q})$ is given by the automorphic induction of $\chi$ (see [JL, §12,Thm.12.2,p.197]), and it is cuspidal since $\chi\ne\overline\chi$ (see [JL, §12,Prop.12.1,p.197]).

$\square$

REMARK 14.1.2.7. An example of a Mordell curve $E_d$, for $d\in\mathbf Z$, $d<0$, of Mordell-Weil rank at least $17$, was announced by Elkies in February 2016.

REMARK 14.1.2.8. We note that, under the assumption of (14.1.2.4), itself a consequence of the BSD Conjecture for Mordell elliptic curves over $\mathbf Q$, Proposition 14.1.2.5 implies that if we replace the Galois group of $\mathbf Q$ with the Weil group $W_{\mathbf Q}$, the analog of Serre’s Conjecture from [Goss, Ch.8,§8.24,Conjecture 8.24.1,p.324] does not hold.

Let $F$ be a number field, and $\overline F$ a fixed choice of separable closure.

The reader will note that the Multiplicity Bound from Theorem 13.3.1.2 obtained on the generic zeros of Hecke $L$-functions, is a priori not sharp.

## PDF page 533

**14.1. ON THE MULTIPLICITIES OF THE ZEROS** · **533**

Indeed, instead of $[F:\mathbf Q]$, the method behind the trace calculation leading to Theorem 13.3.1.1 and hence to Theorem 13.3.1.2 through the Positivity Criterion of Weil, in its form of Theorem ??, it should rather be $m_F(\chi)$ supremum of the integers $m_p(\chi)$, as $p$ varies over all prime numbers, and where $m_p$ is the highest multiplicity of the poles of the meromorphic functions:
$$
\prod_{v\in S_p}L_v(\chi_v|\cdot|_v^s)
$$
as $\chi\in\widehat{C_F}$ is a fixed continuous character, and $L_v(\chi_v|\cdot|_v^s)$ is the local Euler factor at the non-Archimedean place $v$. Recall that $S_p$ is the finite set of finite places of $F$ extending the $p$-adic absolute value on $\mathbf Q$.

The integer $m_F(\chi)$ satisfies $m_F(\chi)\le [F:\mathbf Q]$ by Theorem 7.1.3.2, but it may be strictly smaller.

In fact, it likely is, since, proceeding heuristically by comparison with a form of Chebotarev (for which we refer the reader to [Moroz, Appendix 1,Thm.2,p.68] and [KleMo, Thm.4]), a reasonable expectation, under the assumption of the holomorphy of the Artin-Weil $L$-functions of non-trivial irreducible finite dimensional continuous complex representations of $W_{\mathbf Q}$, for the probability that a prime number $p$ below $x>0$ will be such that $m_p$ attains the maximum allowed value of $[F:\mathbf Q]$, is:
$$
\frac{\mu_{S_\infty,1}(U)}{[F:\mathbf Q]}\int_2^x\frac{\mathrm{d}y}{\log(y)}
$$
where $U\subset\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1/\mathcal O_F^\times$ is the image in $\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1/\mathcal O_F^\times$ of the maximal closed subset of $\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1$ on which the restriction of $\chi$ to $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ is trivial, and $\mu_{S_\infty}$ is the multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$, with $\mu_{S_\infty,1}$ the Haar measure on the closed subgroup $\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1$ obtained by choosing a continuous homomorphic section to the $S_\infty$-idelic norm.

However, $\mu_{S_\infty,1}(U)=0$ for most Hecke characters $\chi$. $U$ will have non-empty interior for $\chi$ of finite order, and more generally for Hecke characters of Galois type (i.e. of the form $\chi|\cdot|_F^{ix_0}$ for some $x_0\in\mathbf R$, possibly nonzero, and $\chi$ of finite order). I know of no other example where $\mu_{S_\infty,1}(U)$ is nonzero.

For Hecke characters $\chi$ of Galois type, indeed $m_F(\chi)=[F:\mathbf Q]$, and so the choice of Sobolev degree $s=2[F:\mathbf Q]$ made to perform the trace calculation leading to Theorem 13.3.1.1, is forced.

A similar argument as in Proposition 14.1.2.3, using the proof of Proposition 14.1.1.1(5.a), shows that $m_F(\chi)$ will always be larger than the maximum of the dimensions of the irreducible sub-representations of $W_{\mathbf Q}$ occurring as the irreducible constituents of $\mathrm{Ind}_{W_{F'/F}}^{W_{F'/{\mathbf Q}}}(\chi')$, for $\chi'$ the inflation of $\chi$ to the Galois closure of $F'$ in $\overline F$, multiplied by the multiplicity with which such irreducible constituent occurs.

This is also compatible with heuristics on the non-correlation of the zeros of the Artin-Weil $L$-functions of such constituents, with the possible exception of central zeros (we refer the reader to [Ru-Sa, §5]). If we are to trust the Grand Simplicity Hypothesis, then the multiplicity of the zeros of $L(s,\chi)$, with the exception of a possible central zero, should be bounded above by the maximum of the multiplicities of the irreducible constituents of $\mathrm{Ind}_{W_{F'/F}}^{W_{F'/{\mathbf Q}}}(\chi')$, for $\chi'$ the inflation of $\chi$ to the Galois closure of $F'$ in $\overline F$, and this integer is therefore lower than $m_F(\chi)$.

Computing $m_F(\chi)$ explicitly appears to be arduous, and choosing the Sobolev degree $s=2[F:\mathbf Q]$ for the purposes of performing the trace calculation leading to Theorem 13.3.1.1, done for simplicity and practicality, appears to be a natural course of action, and leads to the Multiplicity Bound of $[F:\mathbf Q]$ on generic zeros (i.e. non-central zeros).

The question of whether the multiplicity bound of $[F:\mathbf Q]$ on generic zeros can be improved to an explicit bound that is lower than $[F:\mathbf Q]$, is an important one. It appears to remain at a strictly deeper level than the methods of this work, and of its higher rank analogs, which also lead to weaker bounds than those predicted by the Grand Simplicity Hypothesis.

## PDF page 534

**534** · **CHAPTER 14. COMPLEMENTS**

**14.2. The case of global function fields of positive characteristic**

In this subsection, we answer the question of whether the Trace Formula from Theorem 13.3.1.1 holds when $F$ is a global function field of positive prime characteristic $p$, and whether it leads to a novel approach to GRH for the Hecke $L$-functions of global fields of positive characteristic.

The short answer is “no” to both parts of the question.

The trace calculation cannot be performed within the Sobolev ambient that is responsible for the constraints on the zeros contributing to the spectral side (on their location and multiplicity).

Let $p$ be a prime number, and $q$ a positive integer power of $p$, i.e. $q = p^d$ for some integer $d \geq 1$. Let $X$ be a smooth projective geometrically connected curve over $k := \mathbf{F}_q$, and $F$ its function field, $F := k(X)$.

We will be referring to $F$ as a *global function field*.

While the methods from Chapters 2,3,4 and 5 adapt to the case of such $F$, as do the main results from [**CF**, Ch.XV], instrumental to these Chapters (see [**RV**, Ch.7,§7.2,p.264]), it is Chapter 6 and Chapter 7 that are unavailable for such $F$. It is not possible to perform the necessary trace calculations and within a Sobolev ambient, as is done for $F$ a number field.

The reason can be traced directly to the Euler product of the zeta function of $X$:

$$
\zeta(X, s) = \prod_{x \in |X|} \frac{1}{1 - |k(x)|^{-s}} \tag{14.2.0.1}
$$

where the product is indexed by the closed points of $X$, and $k(x)$ is the residue field of $X$ at the closed point $x \in X$, itself a finite field of size $|k(x)|$.

The size $|k(x)|$ of the residue field $k(x)$ is an integer divisible by $q$ for *all* closed points $x \in X$, and hence the Euler factors of $\zeta(X, s)$ have infinitely many poles in common. This is the key difference with the case of $F$ a number field: for any closed point $x \in \mathrm{Spec}(\mathcal{O}_F)$, only finitely many closed points $y \in \mathrm{Spec}(\mathcal{O}_F)$ have the same residue characteristic, i.e. are in the same fibre over $x_p : \mathrm{Spec}(\mathbf{F}_p) \to \mathrm{Spec}(\mathbf{Z})$.

Let $f : X \to \mathbf{P}^1_{\mathbf{F}_q}$ be a non constant morphism, hence finite flat surjective.

This amounts to choosing a structure on $F$ of finite field extension of $\mathbf{F}_q(t)$, i.e. a field embedding $\iota = f^* : \mathbf{F}_q(t) \subset F$.

Since $f$ is finite, it has finite fibres. However, correcting the superposition of the poles of the Euler factors of $\zeta(X, s)$ as is done for Euler factors over distinct prime numbers in the number field case, by assuming the vanishing of the test function along with finitely many of its derivatives, cannot be done for $F$ a global function field, since such vanishing condition would have to hold for the holomorphic derivatives of arbitrarily high order of the Mellin transform of the test function, an entire function on the Riemann surface $\Omega(C_F)$ (whose connected components are, for $F$ a global function field, non simply connected).

Such correction enables the deconstruction of the global geometric kernel, and it is at this early stage that the trace calculation cannot be carried out any further: only finitely many of the infinitely many functionals (obtained as derivatives of point-evaluation functionals supported at points of $\Omega(C_F)$, with unbounded order) required for the method to adapt, remain continuous on $W^{s,2}(C_F)$, shifting the burden of correcting the discrepancy between the $S_1$- and $S_2$-limits of the analogs of the finite rank operators from Theorem 11.2.2.1, onto the test function, forcing the necessity of vanishing conditions to hold for its Mellin transform and its derivatives of unbounded order. A necessity that cannot be fulfilled, since no nonzero holomorphic function exists on any connected non-empty complex domain, which vanishes at a point, with infinite order of vanishing.

In short, the Theorem on Polar Multiplicities (see Theorem 7.1.3.2) does not hold, when $F$ is a global function field.

What is more, is that not only Euler factors have infinitely many poles in common, but they repeat themselves as Euler factors infinitely many times. As many as the number of closed points $x \in X$ whose residue field has fixed degree $m \geq 0$ over $\mathbf{F}_q$.

## PDF page 535

**14.2. THE CASE OF GLOBAL FUNCTION FIELDS OF POSITIVE CHARACTERISTIC** · **535**

This number is estimated from the Weil bound and it is:

$$
\frac{q^m}{m} + O_X(q^{m/2}/m)
$$

as $m \to +\infty$ (see [**TsV**, Ch.2.3,(2.3.2),p.177] combined with the inequality $mB_m \leq N_m - N_1$, with $B_m$ the number of closed points of $X$ of degree $m$, and $N_m := |X(\mathbf{F}_{q^m})|$).

The implied constant depends on the curve through its genus.

An analog of the trace calculation underlying Theorem 13.3.1.2 can indeed be made, although the topology on $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}_0(\mathbf{A}_F))$ and $\mathcal{S}_{\mathrm{E}}(C_F)$ that serves the desired purpose is non-normable, rendering the kernels of the continuous operators on each Hausdorff locally convex topological $\mathbf{C}$-vector space only *generalized* functions, as opposed to measurable functions on the idele classes.

This in turn leads us to employing topologies that are fine enough to render infinite compositions of the Principal Value Operators of Weil (see (5.3.1.5)), i.e. indexed by infinitely many places of $F$, convergent with respect to the topology of uniform convergence on bounded subsets. These serve as a replacement the operation of multiplying a measurable kernel function $k(x, y)$ on $\mathrm{GL}_1(\mathbf{A}_F) \times C_F$ by an indicator function supported over $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \prod_{v \notin S} \mathcal{O}_{F_v}) \times C_F$ to restrict $k(x, y)$ to smaller loci of the product.

The desired convergence of such countably infinite compositions only holds with respect to topologies that are fine enough to promote multiplication by $|\cdot|^a_F$ for $a \in [0, 1 + \varepsilon]$ to a continuous and continously invertible endomorphism on the resulting completion of $\mathcal{S}_{\mathrm{E}}(C_F)$ for all small enough $\varepsilon > 0$, to access the absolute convergence of the Euler product of Hecke $L$-functions over the half plane of absolute convergence. We refer the reader to the proof of [**Me**, §5,Lemma 5.3,p.39,40], for a similar assertion and connection to convergence of operator-theoretic Euler products.

We are lead to a trace formula where the spectral side involves no non-trivial constraints on the non-trivial zeros of $\zeta(X, s)$: if we did not know GRH for $\zeta(X, s)$ as an input.

In other words, the resulting trace formula by itself would not inform us on the location nor on the multiplicity of such zeros. It would recover Weil's own Explicit Formulas only.

This has been accomplished by R. Meyer in [**Me**, §5], and a trace calculation along the lines being alluded to in the foregoing would be close to the one performed in [**Me**, §5,Thm.5.8,p.43], leading to a representation-theoretic proof of the Explicit Formulas only.

Not only does the method of trace calculation not adapt, for $F$ a global function field, but the Multiplicity Bound obtained in Theorem 11.2.2.1 for $F$ a number field, does not hold in its analogous formulation.

Indeed, if it did, then it would be so for any choice of non-constant morphism $f : X \to \mathbf{P}^1_{\mathbf{F}_q}$, and hence it would imply that the multiplicity of the Frobenius eigenvalues on $\mathrm{H}^1_{\mathrm{\acute{e}t}}(X_{k^{\mathrm{sep}}}, \overline{\mathbf{Q}}_{\ell})$, the geometric $\ell$-adic cohomology of $X$, for $\ell$ a prime invertible on $k^{\mathrm{sep}}$, a separable closure of $k = \mathbf{F}_q$ would be bounded above by the gonality of the curve $X$. This is most definitely not the case, due to additional symmetries of $X$ that may arise in positive characteristic: maximal curves provide counterexamples to this assertion.

Maximal curves over $k = \mathbf{F}_{q^2}$ are such that the characteristic polynomial of geometric Frobenius on $\mathrm{H}^1_{\mathrm{\acute{e}t}}(X_{k^{\mathrm{sep}}}, \overline{\mathbf{Q}}_{\ell})$ is $P_1(X) \in \mathbf{Z}[X]$, with:

$$
P_1(X) = (X + q)^{2g}
$$

a consequence of the relative Frobenius acting on the geometric Jacobian

$$
J(X) = \mathrm{Pic}^0_{X_{k^{\mathrm{sep}}}/k^{\mathrm{sep}}}
$$

of $X$ as multiplication by $-q$.

It follows that while the multiplicity of each Frobenius eigenvalue is $2g$, the gonality of the curve is strictly lower, being equal to $g + 1$ (for $g$ the genus of $X$). We refer the reader to [**FGT**], for more on maximal curves (including examples and a partial classification in terms of Hermitian curves).

## PDF page 536

**536** · **CHAPTER . COMPLEMENTS**

We further note that already over $\mathbf{F}_q(t)$, the analog of Serre's conjecture from [**Goss**, Ch.8,§8.24,Conjecture 8.24.1] on simplicity of the zeros of Artin $L$-functions of irreducible representations of $\mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ does not hold.

Indeed, for $q = p^2$, we let $E$ be a supersingular elliptic curve over $\mathbf{F}_q$, a double cover $f : E \to \mathbf{P}^1_{\mathbf{F}_q}$ of the projective line. By Geometric Class Field Theory, the associated quadratic character $\chi_f$ of $\mathbf{F}_q(t)$ is such that $L(s, \chi_f)$ has a double zero.

**14.3. The higher rank case**

For $\pi$ a cuspidal automorphic representation of $\mathrm{GL}_n(\mathbf{A}_F)$, the bound on generic zeros to which we are led by the $n > 1$ version of these methods is:

$$
n[F : \mathbf{Q}].
$$

In particular, for $F = \mathbf{Q}$, the bound is the rank $n$ itself, which shows how the Grand Simplicity Hypothesis remains beyond the reach of the methods developed throughout this work, and its version $\mathrm{GL}_n$.

We will now share a few elements of the version of these methods for $\mathrm{GL}_n(\mathbf{A}_F)$, i.e. to analyze the divisor of the completed, unitarily normalized, $L$-function of a cuspidal automorphic representation $\pi$ of $\mathrm{GL}_n(\mathbf{A}_F)$, to highlight what changes from the case $n = 1$.

$^{2}$

$^2$Say a few words on $\mathrm{GL}_n$. Add that the version for $\mathrm{GL}_n$ is the subject of ongoing work with Brian Conrad.
