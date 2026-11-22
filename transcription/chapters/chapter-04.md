## PDF page 155

CHAPTER 4

**Periodic Schauder Bases on modulated groups**

4.1. Schauder bases 155

4.1.1. Basic concepts and properties 156

4.1.2. On Absolute Schauder Bases and duality 158

4.1.2.1. Schauder bases in the presence of nuclearity 159

4.2. Bases of exponentially decaying Schwartz-Bruhat functions: the case $G=\mathbf{R}_{>0}$ 161

4.2.1. The exponential system on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ 161

4.2.1.1. Recollections on the two strong topologies on orthogonals and the bounded lifting property 163

4.2.1.2. Monogenic periodization on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ and absolute bases of point-evaluation functionals 165

4.2.2. Schauder bases on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ with a support condition 170

4.3. Preparations on isotypic projectors 174

4.3.1. Strong continuity and unitarity. 174

4.3.1.1. Left-regular representation of $G$ on $L^2(G,\nu)$ 175

4.3.2. Orthogonal decomposition into $G^1$-isotypes. 177

4.3.3. $G$-invariants in a quasi-complete Hausdorff locally convex topological vector space. 180

4.3.3.1. Hilbertian and locally convex isotypic projectors 184

4.3.3.2. Averaging over relatively compact locally closed subsets of a Hausdorff locally compact abelian group 185

4.4. Exponential system on monogenic quotients of $\mathbf{R}_{>0}$-modulated groups 188

4.4.1. Complements on the Mellin transform on $\mathcal{S}_I(G)$ 188

4.4.2. The exponential system on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ 191

4.4.2.1. The exponential system on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ 192

4.5. Periodic Schauder Bases in the absence of multiplicity 197

4.5.1. Periodic Schauder Bases: the monogenic case 197

4.5.1.1. Monogenic periodization on $\mathbf{R}_{>0}$-modulated groups 197

4.5.1.2. Exponential system on $\mathcal{S}_{\mathrm{E}}(G)/\ker(\Phi_{\chi,\gamma})$ 204

4.5.2. Periodic Schauder Bases: support conditions in the monogenic case 205

4.5.3. Monogenic periodization of $I$-exponentially decaying Schwartz-Bruhat functions 208

4.6. Periodic Schauder Bases in the presence of multiplicity 209

4.6.1. Bases in the presence of multiplicity 209

4.6.1.1. Polygenic periodization and absolute bases in the presence of multiplicity 210

4.6.2. Support conditions in the presence of multiplicity 218

4.6.3. The case of $\mathcal{S}_I(G)$ 219

**4.1. Schauder bases**

In this section we briefly discuss basic facts about Schauder bases in Hausdorff locally convex topological $\mathbf{C}$-vector spaces, providing references to the literature and recording some foundational results for later use.

**155**

## PDF page 156

**156** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

**4.1.1. Basic concepts and properties.** Finite dimensional $\mathbf{C}$-vector spaces admit finite basic frames (i.e. $\mathbf{C}$-linear bases), and several invariants of linear endomorphisms of a finite dimensional $\mathbf{C}$-vector spaces, while intrinsic, can be computed upon making a choice of basic coordinate frame, i.e. a $\mathbf{C}$-linear isomorphism to $\mathbf{C}^N$ for some integer $N\ge 0$.

The theory of complex Hilbert spaces is another source of example where bases provide a robust tool to make calculations. If the Hilbert space $E$ is infinite dimensional, not all linear endomorphsms of $E$ can be understood in terms of their effect on a basis of $E$, and not all types of bases of $E$ offer robust control over meaningful classes of linear endomorphisms of $E$.

The Hilbertian normed topology on $E$ makes orthonormal frames particularly well suited to understand important classes of *continuous* $\mathbf{C}$-linear endomorphsims of $E$.

We refer the reader to §C.3, and particularly to §C.3.6, for a discussion of Hilbert-Schmidt and nuclear (equivalently, by [Kub, Thm.6.1], trace class) operators, and more generally on the Schatten-von Neumann classes $S_p(E)$ for every real number $p\ge 1$ (nuclear operators being the class $S_1(E)$, and Hilbert-Schmidt operators being the class $S_2(E)$).

See also Lemma C.3.4.1, for more on how these classes of operators can be understood from their effects on an orthonormal frame for $E$ (i.e. an orthonormal basis).

Even in Hilbert spaces, orthonormal frames are not the only type of bases available, and capable of offering control over classes of continuous operators. Riesz bases are images of orthonormal frames under linear topological automorphisms. In particular, they are not necessarily orthonormal. Orthonormal bases and more generally Riesz bases are examples of Schauder bases in Hilbert spaces.

Weaker types of bases are also available on Hilbert, and, more generally, Banach spaces: Markushevich bases. We will be discussing a few in the later Chapters of this work, and solely in the special cases of interest. They are often obtained as images of a Schauder basis under a continuous injective linear operator with dense range, whose target is a Banach space originating as the normed completion of a locally convex source. These conditions are not sufficient for such image to be a Markushevich basis, but often times such is the origin of Markushevich bases in Banach spaces. We refer the reader to [Jar, Part II,Ch.14,§14.1,p.289].

We further refer to [BJL, Ch.IV,§7] for criteria to detect “completeness” of a basic system of holomorphic functions on non-empty domains of the complex plane with respect to the topology of uniform convergence on compact subsets, criteria to which we shall return throughout this Chapter.

An example to bear in mind is that of the exponential system on $C^{\infty}(\mathbf{T})$, where $\mathbf{T}:=\mathbf{R}/\mathbf{Z}$ is the 1-dimensional real torus, which we equip with the volume-1 Haar measure, and $C^{\infty}(\mathbf{T})$ is topologized with the Fréchet topology on uniform convergence on functions and their derivatives of arbitrary order.

Thus topologized, $C^{\infty}(\mathbf{T})$ is a nuclear Fréchet space (see [Tre, Part III,Ch.51,Thm.51.3,p.528] combined with [Tre, Part III,Ch.51,Thm.51.5,p.529]).

We refer to the complete metrizable topology on $C^{\infty}(\mathbf{T})$ as the *smooth topology*.

The 1-periodic smooth functions:

$$
e_m(x):=e^{2\pi i m x},\; x\in\mathbf{R},\, m\in\mathbf{Z}
$$

uniquely determine smooth functions on $\mathbf{T}$, which we also denote by $e_m$, and the countable collection $\{e_m\}_{m\in\mathbf{Z}}$ is an orthonormal basis for the $L^2$-norm completion of $C^{\infty}(\mathbf{T})$, i.e. $L^2(\mathbf{T})$.

The continuous dual $C^{\infty}(\mathbf{T})'$ contains the continuous functionals $a_m:C^{\infty}(\mathbf{T})\to\mathbf{C}$ obtained by sending a smooth 1-periodic function on $\mathbf{R}$, equivalently a smooth function on $\mathbf{T}$, to its $m$th Fourier coefficient, for $m\in\mathbf{Z}$.

Every element $\phi\in C^{\infty}(\mathbf{T})$ has a unique Fourier series expansion:

$$
\phi(x)=\sum_{m\in\mathbf{Z}}a_m(\phi)e^{2\pi i m x} \tag{4.1.1.1}
$$

## PDF page 157

**4.1. SCHAUDER BASES** · **157**

where the series converges with respect to the smooth topology on $C^{\infty}(\mathbf{T})$ (a consequence of [Fol-2, Ch.2,§2.3,Thm.2.6,p.41]).

For any $\phi\in L^2(\mathbf{T})$, the Fourier series expansion $\phi(x)=\sum_{m\in\mathbf{Z}}a_m(\phi)e^{2\pi i m x}$ still converges, pointwise almost everywhere over $\mathbf{T}$, and with respect to the $L^2$-norm topology (this latter is a consequence of [Fol-2, Ch.3,§3.3,Thm.3.5,p.78]. The convergence almost everywhere is a Theorem of Carlson, for which we refer the reader to [Carleson, Thm.(c)]).

Both in $C^{\infty}(\mathbf{T})$ and in $L^2(\mathbf{T})$, the datum

$$
\{(e_m,a_m)\}_{m\in\mathbf{Z}}\in E\times E'
$$

with $E=C^{\infty}(\mathbf{T}),L^2(\mathbf{T})$, is an example of a Schauder basis.

The defining property of a Schauder basis is extrapolated from this example: it is the existence of a series expansion as in (4.1.1.1), convergent with respect to the intrinsic Hausdorff locally convex topology on $E$, together with continuity of the coefficient functionals (without this latter condition, the resulting basis is termed a *topological basis*. We refer the reader to [Jar, Part II,Ch.14,§14.2,p.292]).

We further refer the reader to [Jar, Part II,Ch.14,§14.2,p.292], for the definition of Schauder basis in a Hausdorff locally convex topological $\mathbf{C}$-vector space $E$, which we record here below for ease of access:

DEFINITION 4.1.1.1. Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $\{(x_m,f_m)\}_{m\ge 0}$ a bi-orthogonal sequence in $E\times E^*$, i.e. $f_m(x_n)=\delta_{m,n}$ for all $m,n\ge 0$.

(1) $\{x_m\}_{m\ge 0}$ is a *topological basis for $E$*, if and only if for every $u\in E$, the series:

$$
\sum_{m\ge 0}f_m(u)x_m \tag{4.1.1.2}
$$

converges in $E$, and its limit is $u$.

(2) Assume $\{x_m\}_{m\ge 0}$ is a topological basis for $E$. We say $\{x_m\}_{m\ge 0}$ is a *Schauder basis*, if and only if we have $\{f_m\}_{m\ge 0}\subset E'$.

We refer to the sequence $\{f_m\}_{m\ge 0}\subset E^*$ as the sequence of *coefficient functionals* of $\{x_m\}_{m\ge 0}$.

The Schauder basis $\{(e_m,a_m)\}_{m\in\mathbf{Z}}$ in $C^{\infty}(\mathbf{T})$ is termed the *exponential system*, and it is the aim of this Chapter to generalize it to the case of $\mathbf{R}_{>0}$-modulated abelian groups $G$ (see Definition D.2.1.1), recording the growth properties of the basis elements with respect to the generic continuous seminorm on the Schwartz-Bruhat space of certain compact quotients of $G$ by closed monogenic discrete subgroups.

To clarify what is meant by “growth properties” of the basis elements, we consider the continuous seminorm:

$$
p_N(\phi):=\sup_{x\in[0,1)}\lvert\partial_x^N\phi(x)\rvert
$$

for $\phi\in C^{\infty}(\mathbf{T})$, composed with the quotient homomorphism $\mathbf{R}\to\mathbf{T}$, and $N\ge 0$ an integer.

Then

$$
p_N(e_m)=(2\pi\lvert m\rvert)^N
$$

which, as a function of $m\in\mathbf{Z}$, grows polynomially.

Examples of normed completion $E$ of $C^{\infty}(\mathbf{T})$ such that the exponential system maps to a sequence in $E$ which is *not* a Schauder basis, even though the coefficient functionals $\{a_m\}_{m\ge 0}$ remain continuous functionals on $E$, are $E=C(\mathbf{T})$, equipped with the uniform norm, and $E=L^1(\mathbf{T})$, both Banach spaces.

The exponential system remains a Schauder basis in $L^p(\mathbf{T})$ for all real numbers $1<p<\infty$ (see [Katzn, Ch.II,§1.5,Theorem,p.59]), and the convergence of (4.1.1.1) is not only with respect to the normed topology, but almost everywhere (a generalization of Carleson’s result; see [Hunt]).

These examples amount to the well known phenomenon that continuous, respectively absolutely integrable, functions on $\mathbf{T}$ do not generally have a uniformly convergent Fourier series, respectively convergent with

## PDF page 158

**158** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

respect to the $L^1$-norm; see [Katzn, Ch.II,§1.3,p.57], resting on the Uniform Boundedness Principle, for the former, and Kolmogorov’s famous example (for which we refer the reader to [Kol]), for the latter.

Much as finite basic frames on finite dimensional $\mathbf{C}$-linear spaces, and orthonormal or Riesz frames on complex Hilbert spaces, are useful to understand classes of operators and compute some of their invariants, to Schauder bases goes the same role, on more general Hausdorff locally convex topological $\mathbf{C}$-vector spaces $E$.

Depending on robustness of properties of the topology on $E$, Schauder bases in $E$ will enjoy stronger stability properties, such as absolute summability of their basic series expansions (as for (4.1.1.1) with respect to the smooth topology on $C^{\infty}(\mathbf{T})$, which promotes the exponential system to an *absolute* Schauder basis).

These will be recalled throughout this Chapter and the subsequent ones, as the need arises.

We will be using Schauder bases on countable strict inductive limits of nuclear Fréchet spaces, and with the specific aim of recognizing certain nuclear operators, and computing their nuclear traces.

It is the content of [Lit-II, §4,Cor.2], that Schauder bases can be used to compute nuclear traces of nuclear operators, under reasonable assumptions on the Hausdorff locally convex topology on $E$ (i.e. $E$ has the approximation property and admits a Schauder basis; see [Lit-I]).

**4.1.2. On Absolute Schauder Bases and duality.** With a view towards the following discussion, we refer the reader to [Jar, Part II,Ch.14,§14.6,p.305] for the concept of *unconditionally summable* sequences within Hausdorff locally convex topological $\mathbf{C}$-vector spaces.

For a sequence $\{x_m\}_{m\ge 0}\subset E$ in a Hausdorff locally convex topological $\mathbf{C}$-vector space $E$, $\{x_m\}_{m\ge 0}$ is unconditionally summable if and only if for any countable collection of mutually disjoint finite subsets $\{\Sigma_k\}_{k\ge 0}$ with $\Sigma_k\subset\mathbf{N}$ for all $k\ge 0$, and $\bigcup_{k\ge 0}\Sigma_k=\mathbf{N}$, we have that the sequence $\{s_k\}_{k\ge 0}$, with $s_k:=\sum_{m\in\Sigma_k}x_m$, converges in $E$.

Equivalently, for any bijection $\sigma:\mathbf{N}\to\mathbf{N}$, the sequence $\{\sum_{0\le m\le N}x_{\sigma(m)}\}_{N\ge 0}$ converges in $E$.

We further refer the reader to [Jar, Part II,Ch.14,§14.7,p.314] for the concept of *absolute* Schauder basis, which will be the most discussed throughout this Chapter, and for the following properties of Schauder bases: equicontinuous (see [Jar, Part II,Ch.14,§14.2,p.296]), unconditional (see [Jar, Part II,Ch.14,§14.7,p.309], boundedly complete, respectively shrinking (see [Jar, Part II,Ch.14,§14.5,p.302]), regular (see [Kal, §1,Def.1.1]) and normalized (see [Kal, §1,Def.1.2]), all of which we recall below for ease of access.

DEFINITION 4.1.2.1 (Properties of Schauder bases). Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $\{x_m\}_{m\ge 0}\subset E$ a Schauder basis, $\{f_m\}_{m\ge 0}\subset E'$ its sequence of coefficient functionals. We say $\{x_m\}_{m\ge 0}$ is:

(1) *equicontinuous*, if and only if the basic projections $P_k:=\sum_{0\le m\le k}f_m\cdot x_m$ are such that the sequence $\{P_k\}_{k\ge 0}\subset\mathscr{L}(E)$ is equicontinuous.

(2) *unconditional*, if and only if for every $u\in E$, the sequence $\{f_m(u)x_m\}_{m\ge 0}$ is unconditionally summable.

(3) *absolute*, if and only if for any continuous seminorm $q$ on $E$, there exists a continuous seminorm $q'$ on $E$ satisfying:

$$
\sum_{m\ge 0}q(f_m(u)x_m)\le q'(u). \tag{4.1.2.1}
$$

(4) *boundedly complete*, if and only if for every sequence $\{\alpha_m\}_{m\ge 0}\subset\mathbf{C}$ such that the sequence $\{\sum_{0\le m\le k}\alpha_m x_m\}_{k\ge 0}\subset E$ is bounded, then $\sum_{m\ge 0}\alpha_m x_m$ converges in $E$.

(5) *shrinking*, if and only if $\{f_m\}_{m\ge 0}\subset E'$ is a Schauder basis for $E'_{\beta}$.

(6) *regular*, if and only if there exists a 0-neighborhood $U$ such that $x_m\notin U$ for all integers $m\ge 0$. It is *normalized*, if and only if it is regular and bounded.

REMARK 4.1.2.2. Note that in (4.1.2.1), we have $\sum_{m\ge 0}q(f_m(u)x_m)=\sum_{m\ge 0}\lvert f_m(u)\rvert q(x_m)$ by absolute homogeneity of $q$. We further note that even if the Schauder basis $\{x_m\}_{m\ge 0}\subset E$ is equicontinuous, this

## PDF page 159

**4.1. SCHAUDER BASES** · **159**

does not make the sequence of coefficient functionals $\{f_m\}_{m\ge 0}\subset E'$ an equicontinuous subset; see [Jar, Part II,Ch.14,§14.3,No.7,Remarks,p.299]. We further refer the reader to [Kal, §2,Prop.2.1,p.92], where it is shown that if $\{f_m\}_{m\ge 0}$ is equicontinuous (as a subset of $E'$, i.e. without necessarily being itself a Schauder basis for $E'$ with respect to any polar topology), then $\{x_m\}_{m\ge 0}$ is regular. The converse also holds if $E$ carries the Mackey topology and $\tau(E',E)$ is sequentially complete.

REMARK 4.1.2.3 (On regular Schauder bases and continuous norms). Let $E$ be a Fréchet space. Then by [Kal, §2,Thm.2.3,p.93], if $E$ has a regular Schauder basis, then $E$ has a continuous norm, and admits no complemented closed subspace linearly and topologically isomorphic to $\prod_{m\in\mathbf{N}}\mathbf{C}$.

We will be using this observation to run a few sanity checks, as we construct Schauder bases on certain nuclear Fréchet spaces arising as subquotients of the strict LF-spaces $\mathcal{S}_I(G)$ of $I$-exponentially decaying Schwartz-Bruhat functions on a second-countable Hausdorff locally compact abelian group $G$.

4.1.2.1. *Schauder bases in the presence of nuclearity.* Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space. We let $\{x_m\}_{m\ge 0}$ be an absolute Schauder basis, and write $\{f_m\}_{m\ge 0}\subset E'_{\beta}$ for its sequence coefficient functionals. In particular, $\{(x_m,f_m)\}_{m\ge 0}$ is a bi-orthogonal sequence in $E\times E'$.

Under assumptions on $E$, $\{f_m\}_{m\ge 0}\subset E'_{\beta}$ is itself a Schauder basis, i.e. $\{x_m\}_{m\ge 0}$ is shrinking.

Let $\iota_E:E\to E''=(E'_{\beta})'$ be the evaluation map sending $u$ to the continuous functional $\iota_E(u):=\langle u,\cdot\rangle_{E,E'}$ (see (C.4.1.1) and Lemma C.4.1.1(1)).

Lemma 4.1.2.4 below provides a criterion to detect Schauder bases in $E'_{\beta}$ provided $\{x_m\}_{m\ge 0}$ is an absolute Schauder basis.

LEMMA 4.1.2.4 (On absolute and unconditional Schauder bases). *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space. Assume $E$ is complete, barrelled and reflexive.*

*Let $\{x_m\}_{m\ge 0}\subset E$ be an absolute Schauder basis, and $\{f_m\}_{m\ge 0}$ its sequence of coefficient functionals. Then $\{x_m\}_{m\ge 0}$ is shrinking and boundedly complete, and $\{f_m\}_{m\ge 0}$ is an unconditional, boundedly complete Schauder basis for $E'_{\beta}$.*

*If $E$ is, in addition, nuclear, then $\{f_m\}_{m\ge 0}$ too is shrinking.*

PROOF. For any continuous seminorm $q$ on $E$, there exists a continuous seminorm $q'$ on $E$ such that, for any $u\in E$:

$$
\sum_{m\ge 0}|f_m(u)|q(x_m)\le q'(u). \tag{4.1.2.2}
$$

The evaluation map $\iota_E$ is a linear topological isomorphism, and (4.1.2.2) then reads:

$$
\sum_{m\ge 0}|f_m(\iota_E^{-1}\iota_E(u))|((\iota_E)_*q(\iota_E(x_m))\le (\iota_E)_*(q')(\iota_E(u)) \tag{4.1.2.3}
$$

where for any continuous seminorm $q$ on $E$, we define $(\iota_E)_*q$ to be the continuous seminorm on $E''$ assigned by $\varphi\mapsto((\iota_E)_*q)(\varphi)=q(\iota_E^{-1}(\varphi))$ for any $\varphi\in E''$. All continuous seminorms on $E''$ are obtained in this manner, being $\iota_E$ a linear topological isomorphism.

We may therefore rewrite (4.1.2.3) as:

$$
\sum_{m\ge 0}|(f_m\circ\iota_E^{-1})(\varphi)|q(\iota_E(x_m))\le q'(\varphi) \tag{4.1.2.4}
$$

for all $\varphi\in E''$, for $q,q'$ as in the foregoing, but as continuous seminorms on $E''$.

To see that indeed this makes sense and the sum in (4.1.2.4) converges, we observe that the inequality in (4.1.2.4) holds for all the partial sums.

## PDF page 160

**160** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

Note that, for any $\varphi\in E''$ and for $u:=\iota_E^{-1}(\varphi)$, we have:

$$
(f_m\circ\iota_E^{-1})(\iota_E(u))=\langle u,f_m\rangle_{E,E'}=\langle\iota_E(u),f_m\rangle_{E'',E'}=\langle\varphi,f_m\rangle_{E'',E'}. \tag{4.1.2.5}
$$

In particular, we have $(f_m\circ\iota_E^{-1})(\varphi)=\langle\varphi,f_m\rangle_{E'',E'}$, which we denote $\varphi(f_m)$, for each integer $m\ge 0$. By (4.1.2.4) and since $E''$ is complete by reflexivity, since $E$ is complete, we deduce that the sum $\sum_{m\ge 0}\varphi(f_m)\iota_E(x_m)$ converges in $E''$ (i.e. with respect to the strong topology on the continuous dual of the strong dual $E'_{\beta}$; see [Jar, Part II,Ch.11,§11.2]), and we have $\varphi=\sum_{m\ge 0}\varphi(f_m)\iota_E(x_m)$.

This implies that $\{f_m\}_{m\ge 0}$ is a Schauder basis in $E'_{\beta}$ (alternatively, by [Jar, Part II,Ch.14,§14.5,Thm.1(a),p.302], $\{x_m\}_{m\ge 0}$ is shrinking, since $E$ is reflexive).

By (4.1.2.4), the sum $\sum_{m\ge 0}\varphi(f_m)\iota_E(x_m)$ is unconditionally convergent, and hence the Schauder basis $\{f_m\}_{m\ge 0}$ is unconditional.

If $E$ is nuclear, then it is Montel, since it is barrelled, complete and reflexive (see [Tre, Part III,Ch.50,Cor.1,p.520]). By [Jar, Part II,Ch.11,§11.5,Prop.4(f),p.230], $E'_{\beta}$ is also reflexive, and hence by [Jar, Part II,Ch.14,§14.5,Thm.1(a),p.302] the Schauder basis $\{f_m\}_{m\ge 0}$ is shrinking. $\square$

We record here below the following Theorem of Dynin-Mityagin, providing a criterion to detect absolute Schauder bases. Often times, we will be showing the absoluteness of the Schauder basis under consideration directly, to describe finer information, such as growth conditions on its elements with respect to the generic continuous seminorm.

We refer the reader to [Jar, Part III,Ch.21,§21.10,Thm.1,p.510], and to [McAr, §9,Thm.9.1,p.900] and [DyM].

REMARK 4.1.2.5 (Cautionary remark on the concept of absolute Schauder basis). In [McAr, §9,p.900], a Schauder basis $\{(x_m,f_m)\}_{m\ge 0}$ in a Hausdorff locally convex topological $\mathbf{C}$-vector space $E$, is termed *absolute* if and only if for every continuous seminorm $p$ on $E$, the following series:

$$
\sum_{m\ge 0}p(f_m(u)x_m)
$$

converges for every $u\in E$.

If $E$ is a Fréchet space, this concept of absolute basis, which, a priori, differs from that defined in [Jar, Part II,Ch.14,§14.7,(\*),p.314], which is the one we adopt throughout this work, agrees with it, by the Closed Graph Theorem (see [Jar, Part I,Ch.5,Cor.3,p.94]), since absolute summability of the sequence $\{f_m(u)x_m\}_{m\ge 0}\subset E$ for each $u\in E$ implies closedness of the induced linear operator $E\to\ell^1\{E\}$, and since $E$ is Fréchet, so is $\ell^1\{E\}$, the space of absolute Cauchy sequences in $E$ (see [Jar, Part II,Ch.15,§15.6]. Note that for $E=\mathbf{C}$, we obtain $\ell^1\{E\}=\ell^1$, the Banach space of absolutely summable sequences of complex numbers).

Similarly, if $E$ is a strict LF-space, it is strictly webbed (see [Jar, Part I,Ch.5,§5.6,Thm.2,p.97]), and so [Jar, Part I,Ch.5,§5.4,Thm.1,p.92] applies, so long as we show that $\ell^1\{E\}$ is webbed.

This is indeed the case, if $E$ is a strict inductive limit of a sequence of nuclear Fréchet spaces. To see this, we proceed as follows. Let $\{E_m\}_{m\ge 0}$ be a defining sequence of Fréchet spaces.

By [Jar, Part II,Ch.15,§15.8,Cor.6,p.341], we have a linear topological isomorphism $\ell^1\widehat{\otimes}_{\pi}E\to\ell^1\{E\}$. Since $\ell^1$ is a Banach space, then by [Jar, Part II,Ch.15,§15.5,Cor.4(a),p.334], the continuous linear map $\varinjlim_{m\ge 0}\ell^1\otimes_{\pi}E_m\to\ell^1\otimes_{\pi}E$ is a linear topological isomorphism.

Corollary C.2.3.12 applies to $\ell^1\otimes_{\iota}E_m\to\ell^1\otimes_{\pi}E_m$, and hence the continuous linear operator $\ell^1\otimes_{\iota}E_m\to\ell^1\otimes_{\pi}E_m$ is a linear topological isomorphism for each integer $m\ge 0$.

We refer the reader to the discussion following (C.2.3.22) and to Proposition C.2.3.13 of §C.2.3, for more on inductive tensor products.

## PDF page 161

**4.2. BASES OF EXPONENTIALLY DECAYING SCHWARTZ-BRUHAT FUNCTIONS: THE CASE $G=\mathbf{R}_{>0}$** · **161**

By Proposition C.2.3.13(2), $\ell^1\bar{\otimes}E$ is therefore the strict inductive limit of a countable sequence of Fréchet spaces (using nuclearity of the members of the defining sequence for $E$, to deduce strictness from [Jar, Part III,Ch.16,§16.2,Cor.3,p.348]). In particular, $\ell^1\bar{\otimes}E$ is webbed and strictly webbed.

The foregoing further shows that $\ell^1\bar{\otimes}E\to\ell^1\widehat{\otimes}_{\pi}E$ is a linear topological isomorphism, and we deduce that $\ell^1\{E\}$ is webbed and strictly webbed.

In particular, if $E$ is either a nuclear Fréchet space, or a strict inductive limit of nuclear Fréchet spaces, the concept of absolute Schauder basis in $E$ is unambiguous: the one implicitly used in [McAr, §9] is, in these special cases, equivalent to the one defined in [Jar, Part II,Ch.14,§14.7,(\*),p.314].

THEOREM 4.1.2.6 (Dynin-Mityagin). *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space.*

*(1) If $E$ is nuclear, then every equicontinuous Schauder basis in $E$ is absolute.*

*(2) Assume $E$ is a nuclear Fréchet space. Then every Schauder basis is absolute.*

*(3) Assume $E$ is a strict inductive limit of a sequence of nuclear Fréchet spaces. Then every Schauder basis is absolute.*

PROOF. (1) : This is [Jar, Part III,Ch.21,§21.10,Thm.1,p.510].

(2) : By [Jar, Part II,Ch.14,§14.3,Thm.4,p.296], every Schauder basis in $E$ is equicontinuous, and hence by (1), it is absolute.

(3) : By [Jar, Part II,Ch.14,§14.3,Thm.4,p.296], since strict countable inductive limits of Fréchet spaces are complete, bornological and ultrabornological (see [Jar, Part II,Ch.13,§13.1,Cor.4,p.273] and [Jar, Part II,Ch.13,§13.1,Cor.5,p.273]) and strictly webbed (see [Jar, Part I,Ch.5,§5.6,Prop.1,p.96] and [Jar, Part I,Ch.5,§5.6,Thm.2,p.97]), every Schauder basis (noting that every Schauder basis is, in particular, a weak Schauder basis), is also an equicontinuous basis. By (1), it is an absolute basis; see also [Jar, Part II,Ch.14,§14.3,Cor.3,p.296], noting that strict LF-spaces are barrelled (see [Scha, Ch.II,§7.2,Cor.2,p.61]), and hence the Corollary applies. $\square$

A consequence of Theorem 4.1.2.6 is that every nuclear Fréchet space $E$ with a Schauder basis is linearly and topologically isomorphic to a Köthe sequence space (see [Jar, Part III,Ch.21,§21.6,p.496]). It does not however describe the corresponding Köthe set, which depends specifically on growth conditions satisfied by the basis elements with respect to the generic continuous seminorm on $E$.

In the special cases of interest to this work, which we discuss in this Chapter for the later purpose of identifying copies of the Schauder bases constructed herein, into subquotients of spaces of $S$-local and global adelic $\theta$-functions, it is these growth conditions that we are required to describe, which happen to exhibit the resulting sequence spaces as being linearly and topologically isomorphic to $\mathfrak{s}$, the nuclear Fréchet space of rapidly decreasing sequences (see [Tre, Part III,Ch.51,p.527]).

**4.2. Bases of exponentially decaying Schwartz-Bruhat functions: the case $G=\mathbf{R}_{>0}$**

In this section we exhibit the existence of absolute Schauder bases on subquotients of the Hausdorff locally convex space $\mathcal{S}_{\mathrm{E}}(G)$ of exponentially decaying Schwartz-Bruhat functions on an $\mathbf{R}_{>0}$-modulated group $G$ (see Definition D.2.1.1, Proposition D.3.2.5 and Theorem D.3.3.7) related from averaging operators over the action of a discrete subgroup of the form $\gamma^{\mathbf{Z}}\subset G$.

In the final subsection of this Chapter, §4.6.3, we will be propagating the existence of these Schauder bases, to subquotients of the Hausdorff locally convex topological $\mathbf{C}$-vector spaces $\mathcal{S}_I(G)$ of $I$-exponentially decaying Schwartz-Bruhat functions, with $I$ an arbitrary non-empty open interval of the real line, with a view towards applications in the later Chapters of this work.

**4.2.1. The exponential system on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$.** We begin with a first construction: a special case of the periodization operator from (D.1.7.2), associated to a Hausdorff locally compact abelian group $G$, and

## PDF page 162

**162** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

a closed subgroup $k\subset G$. We refer the reader to Theorem D.1.7.1, for more on periodization over closed subgroups of a Hausdorff locally compact abelian groups, and for a distributional version of the Poisson Summation Formula.

In this subsection, we discuss the special case $G=\mathbf{R}_{>0}$ and $k=\gamma^{\mathbf{Z}}$, for some $\gamma\in\mathbf{R}_{>0}$, $\gamma>1$. Under these assumptions, we prove the main properties of the periodization operator over $\gamma^{\mathbf{Z}}$-translates in $\mathbf{R}_{>0}$, for Schwartz-Bruhat functions on $\mathbf{R}_{>0}$, directly.

We will then discuss the case of $G$ a second-countable $\mathbf{R}_{>0}$-modulated group with module $|\cdot|_G$, and $k=\gamma^{\mathbf{Z}}$, for $\gamma\in G$ with $|\gamma|_G>1$.

DEFINITION 4.2.1.1 (Monogenic periodization over $\mathbf{R}_{>0}$). Let $\gamma\in\mathbf{R}_{>0}$ be a positive real number, such that $\gamma>1$.

We define the operator

$$
\Phi_{\gamma}:\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})=C^{\infty}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}) \tag{4.2.1.1}
$$

assigned by:

$$
\Phi_{\gamma}(\phi)(x):=\sum_{k\in\mathbf{Z}}\phi(\gamma^k x) \tag{4.2.1.2}
$$

as a function of $x\in\mathbf{R}_{>0}$. We refer to the linear operator $\Phi_{\gamma}$ as the $\gamma^{\mathbf{Z}}$-periodization operator.

We now study the operators $\Phi_{\gamma}$ in a manner that is similar to our study of the $\theta$-function operators $\Phi_{F,S}$ and $\Phi_F$ from Chapters 2 and 3.

We first prove the following well known:

LEMMA 4.2.1.2 (Exponential system in $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$). *Let $\gamma\in\mathbf{R}_{>0}$ be a real number, $\gamma>1$. The countable set of functions:*

$$
\left\{e_m:=t^{\frac{2\pi im}{\log(\gamma)}}\right\}_{m\in\mathbf{Z}} \tag{4.2.1.3}
$$

*satisfies the following properties.*

*(1) It is an absolute Schauder basis for $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$.*

*(2) Its bi-orthogonal sequence of coefficient functionals is an unconditional Schauder basis for $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})'_{\beta}$, and it is the countable set of continuous functionals $\{a_m(\cdot)\}_{m\in\mathbf{Z}}$, where, for any $\phi\in\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$:*

$$
a_m(\phi):=\frac{1}{\log(\gamma)}\int_{\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}}\phi(g)\overline{\chi_m}(g)\,\mu_{\gamma}(g) \tag{4.2.1.4}
$$

*is the $m$th Fourier coefficient functional, and where $\mu_{\gamma}$ is the unique Haar measure determined, as per Theorem D.1.2.1, by the choices of $\frac{\mathrm{d}t}{t}$ on $\mathbf{R}_{>0}$, and the counting measure on $\gamma^{\mathbf{Z}}\subset\mathbf{R}_{>0}$, and where $\chi_m$ is the unique continuous character of $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$ extending to the $\gamma^{\mathbf{Z}}$-invariant continuous character of $\mathbf{R}_{>0}$ defined by $t\mapsto t^{\frac{2\pi im}{\log(\gamma)}}$.*

*(3) For each integer $m\in\mathbf{Z}$ and every $\phi\in\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, the following formula:*

$$
a_m(\phi):=\frac{1}{\log(\gamma)}\int_1^{\gamma}\phi(t)t^{\frac{-2\pi im}{\log(\gamma)}}\frac{\mathrm{d}t}{t} \tag{4.2.1.5}
$$

*holds, where $\phi(t)$ is the smooth function of $t\in\mathbf{R}_{>0}$ obtained by composition of $\phi$ with the smooth quotient homomorphism $\mathbf{R}_{>0}\to\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$.*

PROOF. We note that indeed $a_m(e_m)=1$ and $a_m(e_k)=0$ for all integers $k\ne m$. In particular, the pair $(\{e_m\}_{m\in\mathbf{Z}},\{a_m(\cdot)\}_{m\in\mathbf{Z}})$ is a bi-orthogonal sequence with respect to the duality $\langle\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}),\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})'\rangle$.

This implies that $\{e_m\}_{m\in\mathbf{Z}}$ is a topologically free set by [Jar, Part II,Ch.14,§14.1,Prop.1,p.289]. Let $\phi\in\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ be an arbitrary smooth function.

## PDF page 163

**4.2. BASES OF EXPONENTIALLY DECAYING SCHWARTZ-BRUHAT FUNCTIONS: THE CASE $G = \mathbf{R}_{>0}$** · **163**

We denote by $t\partial_t$ the differential operator obtained as the directional derivative along the continuous, hence smooth, 1-parameter group given by the quotient homomorphism $\mathbf{R}_{>0}\to\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$.

Then the sums:

$$
\sum_{m\in\mathbf{Z}:|m|\le M} a_m(\phi)(t\partial_t)^k e_m \tag{4.2.1.6}
$$

for each integer $k\ge 0$ and each integer $M\ge 0$, converge as $M\to+\infty$ uniformly, since we have:

$$
\left\lvert\sum_{m\in\mathbf{Z}:|m|\le M} a_m(\phi)(t\partial_t)^k e_m\right\rvert\le\left(\frac{2\pi}{\log(\gamma)}\right)^k\sum_{m\in\mathbf{Z}:|m|\le M}\lvert a_m(\phi)\rvert m^k \tag{4.2.1.7}
$$

and the coefficients $a_m(\phi)$ are, for each such $\phi$, a sequence of rapid decay, i.e. an element of $\mathcal{S}(\mathbf{Z})=\mathfrak{s}$.

To see this, we observe that they are, as a function on $\frac{2\pi i\mathbf{Z}}{\log(\gamma)}\simeq\widehat{\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}}$, the Fourier transform

$$
\mathcal{F}:\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})\to\mathcal{S}\left(\widehat{\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}}\right)\simeq\mathcal{S}(\frac{2\pi i\mathbf{Z}}{\log(\gamma)})
$$

of $\phi$.

Indeed, for each integer $m\in\mathbf{Z}$, upon calling $\chi_m:=e_m$ as a continuous character $\chi_m\in\widehat{\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}}$, we have

$$
a_m(\phi)=\frac{1}{\log(\gamma)}\int_{\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}}\phi(g)\overline{\chi_m}(g)\,\mathrm{d}\mu_{\gamma}(g)=\mathcal{F}(\phi)(\chi_m)
$$

and since as $m\in\mathbf{Z}$ varies over all the integers, $m\mapsto\chi_m$ is an isomorphism of discrete finitely generated abelian groups $\mathbf{Z}\to\widehat{\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}}$, we deduce that the composition of $\mathcal{F}(\phi)$ with it, is a Schwartz-Bruhat function on $\mathbf{Z}$, hence a sequence of rapid decay, i.e. an element of $\mathfrak{s}$.

This proves that the series in (4.2.1.6) converges absolutely for each $\phi\in\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, and hence that the sequence of finite rank operators $\{\sum_{m\in\mathbf{Z}:|m|\le M}a_m(\cdot)e_m\}_{M\ge 0}$ converge absolutely with respect to the topology of simple convergence. Since $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ is a nuclear Fréchet space, the argument in Remark 4.1.2.5 implies that the sequence $\{e_m\}_{m\in\mathbf{Z}}$ is an absolute Schauder basis in $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$. Alternatively, the convergence of (4.2.1.6) for every $\phi\in\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ implies that $\{e_m\}_{m\in\mathbf{Z}}$ is a Schauder basis for $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, and since $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ is a nuclear Fréchet space, then by the Dynin-Mityagin Theorem (see Theorem 4.1.2.6) it is an absolute Schauder basis.

By reflexivity of $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, Lemma 4.1.2.4 applies, giving that the sequence $\{a_m(\cdot)\}_{m\in\mathbf{Z}}$ of coefficient functionals is an unconditional Schauder basis for the strong dual $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})'_{\beta}$. $\square$

4.2.1.1. *Recollections on the two strong topologies on orthogonals and the bounded lifting property.* We recall the following:

LEMMA 4.2.1.3 (Homomorphic weak and strong adjoints to quotient maps). *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, and $M\subset E$ a closed subspace.*

*The linear bijection:*

$$
(E/M)'\to M^{\perp} \tag{4.2.1.8}
$$

*where the orthogonal $M^{\perp}$ is formed with respect to the duality $\langle E,E'\rangle$, is a linear topological isomorphism, upon endowing the source with the weak topology, and the target with the subspace topology of the weak topology inherited from $E'_{\sigma}$.*

(1) *If $E$ is a nuclear Fréchet space, then (4.2.1.8) is a linear topological isomorphism, upon endowing the source with the strong topology, and the target with the subspace topology of the strong topology inherited from $E'_{\beta}$.*

## PDF page 164

**164** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

(2) *If $E$ is a Hilbert space, then (4.2.1.8) is a linear topological isomorphism, upon endowing the source with the strong topology, and the target with the subspace topology of the strong topology inherited from $E'_{\beta}$.*

PROOF. The linear operator $(E/M)'\to M^{\perp}$ is defined by sending a continuous functional $T$ to the composition of $T$ by the quotient $E\to E/M$. By [NB, Thm.8.12.1(a)], it is a linear bijection.

By [NB, Thm.8.13.2], which applies by [NB, Thm.8.11.3(c)], the linear operator $(E/M)'\to E'$ is a linear topological embedding with respect to the weak topology on source and target. By [NB, Thm.8.12.1(a)], its range is $M^{\perp}$, and hence the linear operator from (4.2.1.8) is a linear topological isomorphism upon endowing source and target with the weak topologies.

(1) : By [Apiola, §4,Thm.4.3], nuclear Fréchet spaces are separated quotients of Köthe Schwartz spaces, and by [MV-2, Thm.7], they are quasi-normable.

By [Jar, Part II,Ch.10,§10.7,Cor.3,p.215] and [Tre, Part III,Ch.50,Prop.50.2(50.12),p.519], nuclear Fréchet spaces are therefore Fréchet-Schwartz spaces, and by [Val-b, Thm.2.4(2)], for any closed subspace $M\subset E$ of the nuclear Fréchet space $E$, the quotient map $E\to E/M$ lifts bounded subsets.

Let $H\subset (E/M)''$ be an equicontinuous subset. Since $E/M$ is reflexive, being nuclear Fréchet (by [Scha, Ch.III,§7,Thm.7.4,p.103]), hence Montel by [Tre, Part III,Ch.50,Cor.3,p.520], hence reflexive, then by [Scha, Ch.III,§4.1,Corollary,p.83] $H$ is bounded with respect to the strong topology, and hence its pre-image under the evaluation linear topological isomorphism $\iota_{E/M}:E/M\to (E/M)''$ is bounded. There therefore exists a bounded subset $B\subset M$ whose image under the quotient map $E\to E/M$ is $\iota_{E/M}^{-1}(H)$. Under the linear topological isomorphism $\iota_E:E\to E''$, $\iota_E(B)$ is therefore a bounded subset of $E''$, hence equicontinuous by [Scha, Ch.III,Thm.4.2,p.83] combined with [Scha, Ch.III,§3.4,Corollary,p.82]. Its image under the continuous linear operator $E''\to (E/M)''$, which is the continuous adjoint of the continuous adjoint $(E/M)'_{\beta}\to E'_{\beta}$, is $H$.

By [NB, Thm.8.13.4], applied to $X=(E/M)'_{\beta}$, $Y=E'_{\beta}$, $A:X\to Y$ the continuous adjoint of the quotient map $E\to E/M$, by weak relative openness of $A$, which was shown in the foregoing, and since we have shown that every equicontinuous subset of $X'$ is the image under $A'$ of some equicontinuous subset of $Y'$, we deduce that $A$ is relatively open. Its range is $M^{\perp}$, and hence (4.2.1.8) is a linear topological isomorphism, upon topologizing the source with the strong topology, and the target with the subspace topology of the strong topology.

(2) : By [Val-b, Thm.2.4(1)] (or by direct construction), for any closed subspace $M\subset E$ of the Hilbert space $E$, the quotient map $E\to E/M$ lifts bounded subsets. By total reflexivity of Hilbert spaces (i.e. $E$ and all of its separated quotients are reflexive) and again applying [Scha, Ch.III,§4.1,Corollary,p.83], [Scha, Ch.III,Thm.4.2,p.83] and [Scha, Ch.III,§3.4,Corollary,p.82], the same argument provided for (1) shows that [NB, Thm.8.13.4] applies, and (4.2.1.8) is a linear topological isomorphism, upon topologizing the source with the strong topology, and the target with the subspace topology of the strong topology. $\square$

REMARK 4.2.1.4. We note that the same assertion as in the Lemma does not hold for the weak topology replaced by the strong topology, unless additional assumptions on $E$ and the quotient $E/M$ are in force.

Assume $E$ is a totally reflexive Fréchet space (i.e. every separated quotient of $E$ is also reflexive; see [Gro-e, §II.3,Def.2,p.99]), and $M\subset E$ is a closed subspace.

The continuous adjoint $(E/M)'_{\sigma}\to E'_{\sigma}$ is relatively open by Lemma 4.2.1.3.

Assume that $(E/M)'_{\beta}\to E'_{\beta}$ is a linear topological embedding. Then by reflexivity, [NB, Thm.8.13.4] applies to $A$ the continuous adjoint of the linear operator from (4.2.1.8), and to $X=(E/M)'_{\beta}$ and $Y=M^{\perp}$ equipped with the subspace topology of the strong topology.

It follows that the quotient map $E\to E/M$ lifts equicontinuous subsets (with respect to the $\beta(E'',E')$-topology, using reflexivity of $E$).

By [Scha, Ch.III,§4,4.1,Corollary,p.83], any equicontinuous subset of $E/M$ and $E$ is strongly bounded (each identified with the strong dual of $(E/M)'_{\beta}$, respectively $E'_{\beta}$, by reflexivity; see also [NB, Thm.11.3.5] and

## PDF page 165

**4.2. BASES OF EXPONENTIALLY DECAYING SCHWARTZ-BRUHAT FUNCTIONS: THE CASE $G = \mathbf{R}_{>0}$** · **165**

[NB, Thm.11.3.6]), and since $E$ is barrelled by [NB, Thm.11.7.2] (see also [Scha, Ch.II,§7,Thm.7.1,p.60]), the converse also holds by [Scha, Ch.III,§4,Thm.4.2,p.83].

It follows that the quotient map $E\to E/M$ would have to lift bounded subsets.

By [Val-b, Thm.2.4(2)], $E$ is either a Fréchet-Schwartz space, a Banach space, or a product of a Banach space by $\omega$.

Nuclear Fréchet spaces are totally reflexive and Fréchet-Schwartz. We further refer the reader to [FlM, §5.5,Corollary,p.110], for several sufficient conditions for a homomorphism between Hausdorff locally convex topological $\mathbf{C}$-vector spaces, to have homomorphic strong adjoint.

We refer the reader to Definition C.1.5.9 and subsequent discussion for information on the bounded lifting property for continuous linear maps between Hausdorff locally convex topological $\mathbf{C}$-vector spaces.

4.2.1.2. *Monogenic periodization on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ and absolute bases of point-evaluation functionals.* The following Lemma studies the periodization operator $\Phi_{\gamma}:\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ and its kernel.

We recall that the Mellin transform $M:\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\to A\mathcal{S}(\mathbf{C})$, where $A\mathcal{S}(\mathbf{C})$ is the *Schwartz-Bergman space* defined in Definition D.3.1.3 and studied in §D.3.1, the space of entire functions that are Schwartz uniformly over the non-empty open vertical strips of bounded width of the complex $s$-plane, topologized with the Hausdorff locally convex topology defined in Lemma D.3.1.2, promoting it to a separable nuclear Fréchet space, is a linear topological isomorphism; see Proposition D.3.2.5.

The Mellin transform is defined, on each $\phi\in\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, as:

$$
M(\phi)(s):=\int_{\mathbf{R}_{>0}}\phi(t)t^s\,\frac{\mathrm{d}t}{t}
$$

as a function of $s\in\mathbf{C}$, and it is defined and studied in §B.2.1.

LEMMA 4.2.1.5 (On the kernel of the monogenic periodization operator $\Phi_{\gamma}$). *Let $\gamma\in\mathbf{R}_{>0}$ be a positive real number, such that $\gamma>1$. Let $f\in\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ be a Schwartz-Bruhat function on $\mathbf{R}_{>0}$ of exponential decay. Then:*

(1) *$\Phi_{\gamma}(f)$ is a Schwartz-Bruhat function on the compact Hausdorff abelian group $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$.*

(2) *The linear operator $\Phi_{\gamma}$ from (4.2.1.1) is continuous, surjective and open.*

(3) *$\ker(\Phi_{\gamma})$ is the closure in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ of the linear subspace generated by the elements $\phi(x)-\phi(\gamma x)$ as functions of $x$ and as $\phi$ varies over all the elements of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$. In particular, the continuous functionals $\phi\mapsto\int_{\mathbf{R}_{>0}}\phi(t)t^{-\frac{2\pi im}{\log(\gamma)}}\frac{\mathrm{d}t}{t}$ are an unconditional Schauder basis for the orthogonal of $\ker(\Phi_{\gamma})$ with respect to the duality $\langle\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}),\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})'\rangle$, equipped with the strong topology on the dual $(\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})/\ker(\Phi_{\gamma}))'$, equivalently with the subspace topology of the strong topology on the dual $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})'$.*

REMARK 4.2.1.6. Note that for $M\subset\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ a closed subspace, the orthogonal $M^{\perp}$ of $M$ with respect to the duality $\langle\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}),\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})'\rangle$ is linearly isomorphic to the continuous dual of the quotient $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})/M$ (see [NB, Thm.8.12.1(a)]). There are therefore two “strong topologies” on $M^{\perp}$: the topology induced by the strong topology of $(\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})/M)'_{\beta}$, and the topology induced by the subspace topology of the strong topology of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})'_{\beta}$. These two topologies are equivalent, because $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ is a nuclear Fréchet space (see Lemma D.3.2.3(1) applied with $I=\mathbf{R}$), and therefore it has the bounded lifting property, i.e. for every closed subspace $M\subset\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, every bounded subset of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})/M$ is contained in the image of a bounded subset of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ under the quotient map $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\to\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})/M$.

We refer the reader to Lemma 4.2.1.3 and to [FlM, §5.5,Corollary,part (1),p.110].

The key to this fact is quasi-normability of Fréchet-Schwartz spaces, of which nuclear Fréchet spaces are an example. We further refer the reader to Valdivia's characterization of those Fréchet spaces that possess the bounded lifting property (see [Val-b, Thm.2.4(2)]).

## PDF page 166

**166** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

In particular, there is no ambiguity, throughout the statement of Lemma 4.2.1.5, as to what strong topology orthogonals of closed subspaces of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ are equipped with.

PROOF OF LEMMA 4.2.1.5. (1) and (2) : The exponential decay of $f$ ensures that formation of the derivative $(t\partial_t)^k f$ and of the $\partial_{\alpha}^k\Phi_{\gamma}(f)$, where $\alpha:\mathbf{R}_{>0}\to\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$ is the continuous 1-parameter group defined by the quotient homomorphism, commute, i.e. $\partial_{\alpha}^k\Phi_{\gamma}(f)=\Phi_{\gamma}((t\partial_t)^k f)$ as continuous functions on $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$. We will be showing this towards the end of the argument.

It follows that $\Phi_{\gamma}(f)$ is a smooth function on $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$, and hence Schwartz-Bruhat on $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$, since $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$ is a compact Hausdorff abelian group.

Let $\{f_m\}_{m\ge 0}$ be a Cauchy sequence in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ converging to $f\in\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$. Then $\{f_m\}_{m\ge 0}$ is bounded in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, and $(t\partial_t)^k f_m\to (t\partial_t)^k f$ as $m\to+\infty$ uniformly over $\mathbf{R}_{>0}$ for each integer $k\ge 0$.

For every integer $N>0$, there therefore exists $T>0$ and an integer $m_T>0$ depending on $N$, such that for all integers $m\ge m_T$, we have, for some real number $C_N>0$:

$$
\lvert (t\partial_t)^k f_m-(t\partial_t)^k f\rvert<C_N e^{-N\lvert\log(t)\rvert}
$$

for all $t\in\mathbf{R}_{>0}-(1/T,T)$.

For $t>T$, $\gamma^k t\ge T$ if and only if $\gamma^k\in t^{-1}\cdot[T,+\infty)$. There exists an integer $k_T(t)$ such that this is the case if and only if $k\ge k_T(t)$. We note that we have $k_T(t)\ge -\log_{\gamma}(t)+\log_{\gamma}(T)$, and we have, for every $t>T$:

$$
\lvert\Phi_{\gamma}((t\partial_t)^k f_m)-\Phi_{\gamma}((t\partial_t)^k f)\rvert\le C_N\sum_{k\ge k_T(t)}\lvert\gamma^k t\rvert^{-N} \tag{4.2.1.9}
$$

where the series on the right side of (4.2.1.9) converges geometrically.

Explicitly, we have:

$$
\sum_{k\ge k_T(t)}\lvert\gamma^k t\rvert^{-N}=t^{-N}\sum_{k_T(t)\le k<0}\gamma^{-k}+t^{-N}\sum_{k\ge 0}\gamma^{-k} \tag{4.2.1.10}
$$

$$
=t^{-N}\sum_{k_T(t)\le k<0}\gamma^{-k}+\frac{t^{-N}}{1-\gamma^{-1}} \tag{4.2.1.11}
$$

$$
=-t^{-N}+t^{-N}\frac{1-\gamma^{-k_T(t)+1}}{1-\gamma}+\frac{t^{-N}}{1-\gamma^{-1}} \tag{4.2.1.12}
$$

$$
\le -t^{-N}+t^{-N}\frac{\gamma t/T-1}{\gamma-1}+\frac{t^{-N}}{1-\gamma^{-1}}. \tag{4.2.1.13}
$$

Upon coosing $N>1$ from the outset, then for any $\varepsilon>0$, we may choose $T_1>T$ as large as we please so as to arrange to have:

$$
\sup_{t>T_1}C_N\sum_{k\ge k_T(t)}\lvert\gamma^k t\rvert^{-N}<\varepsilon/3. \tag{4.2.1.14}
$$

The case $t\in(0,1/T)$ is treated similarly, and we obtain that for some large enough $T'>T$ depending on $N>1$ and on $\varepsilon$, then over $(0,1/T']\cup[T',+\infty)$ we have

$$
\lvert\Phi_{\gamma}((t\partial_t)^k f_m)-\Phi_{\gamma}((t\partial_t)^k f)\rvert<(2/3)\varepsilon
$$

for all $m\ge m_T$.

Over $(1/T',T')$, the convergence of $(t\partial_t)^k f_m$ to $(t\partial_t)^k f$ is uniform, and for every $\varepsilon_0>0$, there exists an integer $m_0=m_0(\varepsilon_0)\ge m_{T'}$ such that for all $m\ge m_0$ we have:

$$
\sup_{t\in(1/T',T')}\lvert (t\partial_t)^k f_m-(t\partial_t)^k f\rvert<\varepsilon_0. \tag{4.2.1.15}
$$

## PDF page 167

**4.2. BASES OF EXPONENTIALLY DECAYING SCHWARTZ-BRUHAT FUNCTIONS: THE CASE $G=\mathbf{R}_{>0}$** · **167**

Since the subgroup $\gamma^{\mathbf{Z}}\subset\mathbf{R}_{>0}$ is discrete, by the assumption $\gamma\ne 1$, only finitely many integers $k\in\mathbf{Z}$ are such that $\gamma^k(1/T',T')\cap(1/T',T')$ is non-empty. Let $M_{T'}$ be their number.

We deduce that we have:

$$
\lvert\Phi_\gamma((t\partial_t)^kf_m)(x)-\Phi_\gamma((t\partial_t)^kf)(x)\rvert<M_{T'}\varepsilon_0 \tag{4.2.1.16}
$$

for all $x\in(1/T',T')$.

We choose $\varepsilon_0:=\varepsilon/(3M_{T'})$ and obtain that for all $m\ge m_0$, we have $\lVert\Phi_\gamma((t\partial_t)^kf_m)-\Phi_\gamma((t\partial_t)^kf)\rVert_u<\varepsilon$, and hence $\Phi_\gamma((t\partial_t)^kf_m)\to\Phi_\gamma((t\partial_t)^kf)$ uniformly.

Since this is the case for every integer $k\ge 0$, we deduce that we have $\Phi_\gamma(f_m)\to\Phi_\gamma(f)$ in $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ (whose topology is equivalent to that of $\mathcal{D}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, the $\mathbf{C}$-linear space of smooth functions on $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$ topologized with the nuclear Fréchet topology of uniform convergence of functions and their derivatives of arbitrary order), so long as we show that $\Phi_\gamma(f)$ is smooth, and that the commutation property $(t\partial_t)\Phi_\gamma(f)=\Phi_\gamma(t\partial_tf)$ holds.

If so, then $\Phi_\gamma$ is sequentially continuous by the foregoing, as an operator $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$. It is therefore continuous since both source and target are metrizable.

We now return to the proof of smoothness of $\Phi_\gamma(f)$, and we then show the commutation property $(t\partial_t)\Phi_\gamma(f)=\Phi_\gamma(t\partial_tf)$ for any $f\in\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$.

We let $f\in\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$ be arbitrary, and let $\{t_m\}_{m\ge 0}\subset\mathbf{R}_{>0}$ be an arbitrary sequence such that $\lim_{m\to+\infty}t_m=1$. We define

$$
f_m(x):=\frac{f(t_m^{-1}x)-f(x)}{t_m-1} \tag{4.2.1.17}
$$

itself a Schwartz-Bruhat function on $\mathbf{R}_{>0}$ with exponential decay, for every integer $m\ge 0$. The sequence $\{f_m\}_{m\ge 0}$ converges to $(t\partial_t)f$ uniformly over $\mathbf{R}_{>0}$ (indeed, every $f\in\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$ is, in particular, a Schwartz-Bruhat function on $\mathbf{R}_{>0}$, and hence it is uniformly differentiable over $\mathbf{R}_{>0}$).

We proved that we have $\lim_{m\to+\infty}\Phi_\gamma(f_m)=\Phi_\gamma((t\partial_t)f)$ pointwise, and uniformly on the compact subsets of $\mathbf{R}_{>0}$.

Since $\{t_m\}_{m\ge 0}$ is arbitrary, this shows that $\Phi_\gamma(f)$ is smooth, and that indeed $(t\partial_t)\Phi_\gamma(f)=\Phi_\gamma((t\partial_t)f)$ holds, as continuous functions over $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$.

We now let $u\in\mathcal{D}(\mathbf{R}_{>0})$ be a smooth function, compactly supported within an open neighborhood with compact closure of $[\gamma^N,\gamma^{N+1}]$ for a choice of integer $N\ge 0$ large enough so as to have $\gamma^N>3$.

We assume $u$ is real-valued, nonnegative, and $u=1$ on $[\gamma^N,\gamma^{N+1}]$ and $u=0$ away from $[\gamma^N-\varepsilon,\gamma^{N+1}+\varepsilon]$ for a choice of $\varepsilon>0$ so small so as to arrange $[\gamma^N-\varepsilon,\gamma^{N+1}+\varepsilon]\cap(0,2)=\varnothing$.

We call $u_0:=\Phi_\gamma(u)$ as a smooth function of $t\in\mathbf{R}_{>0}$, and define, for each $\phi\in\mathcal{D}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, $\phi_u:=(\phi\circ\pi)\cdot(u/u_0)$, for $\pi:\mathbf{R}_{>0}\to\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$ the quotient homomorphism.

Since $u_0$ does not vanish on $[\gamma^N-\varepsilon,\gamma^{N+1}+\varepsilon]$, the definition of $\phi_u$ makes sense, providing a smooth compactly supported function on $\mathbf{R}_{>0}$ such that $\Phi_\gamma(\phi_u)=\phi$ as smooth functions on $\mathbf{R}_{>0}$, invariant under the action of $\gamma^{\mathbf{Z}}$.

This proves that $\Phi_\gamma$ is surjective. By [NB, Thm.14.4.5(b)], it is open.

(3) : The kernel $\ker(\Phi_\gamma)\subset\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$, a closed subspace by (2), contains the linear subspace generated by the elements $\phi(x)-\phi(\gamma x)$.

The Mellin transform sends its closure $K_\gamma$ onto the closed subspace $(1-\gamma^{-s})A\mathcal S(\mathbf C)$ (by the Asymptotic Residue Theorem, Theorem B.3.2.1, from which it follows that it is sequentially closed, hence closed, being $A\mathcal S(\mathbf C)$ a Fréchet space by Lemma D.3.1.2).

It follows that the orthogonal to $(1-\gamma^{-s})A\mathcal S(\mathbf C)$ with respect to the duality $\langle A\mathcal S(\mathbf C),A\mathcal S(\mathbf C)'\rangle$, equipped with the strong topology on the continuous dual of the quotient $A\mathcal S(\mathbf C)/(1-\gamma^{-s})A\mathcal S(\mathbf C)$, equivalently (by Lemma 4.2.1.3(1), which applies since $A\mathcal S(\mathbf C)$ is a nuclear Fréchet space by Proposition D.3.2.5 and Lemma

## PDF page 168

**168** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

D.3.2.3(1)) with the subspace topology of the strong topology on $A\mathcal S(\mathbf C)'$, is linearly and topologically generated by the continuous point-evaluation functionals at the points of the complex $s$-plane $\left\{\frac{2\pi im}{\log(\gamma)}, m\in\mathbf{Z}\right\}$.

To see this, we proceed as follows. The linear inclusion $A\mathcal S(\mathbf C)\to\mathscr{O}(\mathbf{C})$ of the Schwartz-Bergman space $A\mathcal S(\mathbf C)$ into the linear space of holomorphic functions on the complex $s$-plane, is continuous, upon endowing the target with the complete metrizable topology of uniform convergence on compact subsets. It is injective with dense range. Since both source and target are Montel, hence reflexive, then by [NB, Thm.8.10.6(e)], the continuous adjoint to the injective continuous linear operator $A\mathcal S(\mathbf C)/(1-\gamma^{-s})A\mathcal S(\mathbf C)\to\mathscr{O}(\mathbf{C})/(1-\gamma^{-s})\mathscr{O}(\mathbf{C})$ with dense range, is itself injective and with weakly dense range.

Since such range is a linear subspace, hence, in particular, convex, it is dense by [Jar, Part I,Ch.8,§8.2,Prop.5,p.149] (see also [Scha, Ch.IV,§3,Thm.3.1,p.130]. We use reflexivity of $E:=A\mathcal S(\mathbf C)/(1-\gamma^{-s})A\mathcal S(\mathbf C)$ to identify the topologies $\sigma(E',E)$ and $\sigma(E',(E'_\beta)')=\sigma(E'_\beta,(E'_\beta)')$).

We now observe that the strong dual of $\mathscr{O}(\mathbf{C})/(1-\gamma^{-s})\mathscr{O}(\mathbf{C})$ is the linear space $\bigoplus_{z\in\mathbf{C}:1-\gamma^{-z}=0}\mathbf{C}\delta_z$, for $\delta_z$ the continuous point-evaluation functional on $\mathscr{O}(\mathbf{C})$ at $z\in\mathbf{C}$, equipped with the finest locally convex topology.

In turn, to see this, we proceed as follows.

Since the complex $s$-plane $\mathbf{C}$ is Stein, then, upon denoting by $\mathscr{J}\subset\mathscr{O}$ the ideal sheaf globally generated by $1-\gamma^{-s}$, and by $\check{\mathrm{H}}(\mathbf{C},\cdot)$ Čech cohomology (see [Gdm, Ch.I,§5.1,5.2] and [Gdm, Ch.I,§5.2,Thm.5.2.4,p.209] and its Corollary [Gdm, Ch.I,§5.2,Corollaire,p.209]), we have

$$
\check{\mathrm{H}}^1(\mathbf{C},\mathscr{O}/\mathscr{J})=\mathrm{H}^1(\mathbf{C},\mathscr{O}/\mathscr{J})=0
$$

and therefore upon choosing a locally finite countable open cover $\{B_m\}_{m\ge 0}$ of the complex $s$-plane by open balls each of which contains at most one of the zeros $z$ of $1-\gamma^{-s}$, then, upon denoting by $B_{\underline{k}}$ the intersection $\bigcap_{m\in \underline{k}}B_m$ for $\underline{k}$ varying over all non-empty finite subsets of the nonnegative integer, we deduce that $\mathrm{H}^0(B_{\underline{k}},\mathscr{O}/\mathscr{J})$ is trivial if $\underline{k}$ contains at least two elements, and it is either trivial or 1-dimensional if $\underline{k}$ contains one element exactly.

To see this, we let $z\in\mathbf{C}$ be a zero of $1-\gamma^{-s}$ contained in the open ball $B:=B_m$ only. We observe that we have $\mathscr{O}(B)/(1-\gamma^{-s})\mathscr{O}(B)=\mathscr{O}(B)/(s-z)\mathscr{O}(B)$ linearly and topologically, since $1-\gamma^{-s}$ has only simple zeros.

Since $\mathscr{O}(B)$ is $\mathbf{C}[s]$-flat as an algebra over $\mathbf{C}[s]$, and $\mathbf{C}[s]$ is dense in $\mathscr{O}(B)$ by Runge's Theorem (see [Cnw-b, Ch.VIII,Cor.1.15,p.200]), then $\mathbf{C}[s]/(s-z)=\mathbf{C}$ is mapped densely into $\mathscr{O}(B)/(s-z)\mathscr{O}(B)$. Since $\mathbf{C}[s]/(s-z)$ is 1-dimensional, it carries the subspace topology inherited from $\mathscr{O}(B)/(s-z)\mathscr{O}(B)$, which is the Euclidean topology, and by completeness and denseness, the map $\mathbf{C}[s]/(s-z)\to\mathscr{O}(B)/(s-z)\mathscr{O}(B)$ is also surjective.

This computes

$$
\mathscr{O}(\mathbf{C})/(1-\gamma^{-s})\mathscr{O}(\mathbf{C})=\check{\mathrm{H}}^0(\mathbf{C},\mathscr{O}/\mathscr{J})
$$

to be $\prod_{z:1-\gamma^{-z}=0}\mathbf{C}$. The quotient topology $\mathscr{O}(\mathbf{C})/(1-\gamma^{-s})\mathscr{O}(\mathbf{C})$ matches the product topology. Indeed, since any compact subset $K\subset\mathbf{C}$ is contained in the union of at most finitely many of the $B_m$, then the linear bijection $\mathscr{O}(\mathbf{C})/(1-\gamma^{-s})\mathscr{O}(\mathbf{C})\to\prod_{z:1-\gamma^{-z}=0}\mathbf{C}$ is continuous. Being source and target Fréchet spaces, it is a linear topological isomorphism by [NB, Thm.14.4.5(b)].

We have shown that the strong dual of $A\mathcal S(\mathbf C)/(1-\gamma^{-s})A\mathcal S(\mathbf C)$, equivalently of $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})/K_\gamma$, is linearly and topologically generated by the continuous point-evaluation functionals at the points of the complex $s$-plane $\left\{\frac{2\pi im}{\log(\gamma)}, m\in\mathbf{Z}\right\}$, equivalently their images under the continuous adjoint of the Mellin transform.

Such functionals are, each respectively, the image of the continuous linear functionals sending $\phi\in\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ to its $m$th Fourier coefficient, and hence, being the latter set of functionals a Schauder basis for

## PDF page 169

**4.2. BASES OF EXPONENTIALLY DECAYING SCHWARTZ-BRUHAT FUNCTIONS: THE CASE $G=\mathbf{R}_{>0}$** · **169**

$\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})'_\beta$ by Lemma 4.2.1.2, the continuous linear map:

$$
\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})'_\beta\to(\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})/K_\gamma)'_\beta
$$

is injective with dense range.

By [NB, Thm.8.10.6(e)] and reflexivity, the continuous linear operator $\Phi_\gamma:\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})/K_\gamma\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ is injective. However, by (2), it is also surjective, and hence it is a continuous linear bijection.

Being source and target Fréchet spaces, it is a linear topological isomorphism by [NB, Thm.14.4.5(b)]. $\square$

We recall that an equicontinuous Schauder basis may not be an equicontinuous set; see [Jar, Part II,Ch.14,§14.3,No.7,Remarks,p.299].

We now prove the following:

COROLLARY 4.2.1.7. *Let $\gamma\in\mathbf R_{>0}$ be a real number, $\gamma>1$. The unconditional Schauder basis $\{a_m(\cdot)\}_{m\in\mathbf Z}$ from (4.2.1.4) for $\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta$ is absolute, and, as a subset of $\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta$, it is bounded and equicontinuous in $\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta$.*

PROOF. Since $\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})$ is a nuclear Fréchet space, its strong dual is barrelled (see [Bou-TVS, Ch.IV,§3,No.4,Corollary,IV.24], which applies since nuclear Fréchet spaces are Montel by [Tre, Part III,Ch.50,Cor.3,p.520], hence reflexive), and hence [Jar, Part II,Ch.14,§14.3,p.296] applies, giving that the Schauder basis $\{a_m(\cdot)\}_{m\in\mathbf Z}$ for $\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta$ is equicontinuous. By the Dynin-Mityagin Theorem (see Theorem 4.1.2.6(1)), since $\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta$ is itself nuclear by [Tre, Part III,Ch.50,Prop.50.6,p.523], $\{a_m(\cdot)\}_{m\in\mathbf Z}$ is an absolute Schauder basis.

By Lemma 4.2.1.5(2), the continuous linear operator $\Phi_\gamma:\mathcal S_{\mathrm E}(\mathbf R_{>0})\to\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})$ is surjective and open. By [FlM, §5.5,Corollary,part (1),p.110], which applies since $\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})$ is nuclear Fréchet, and hence it has the Heine-Borel property (see [Tre, Part III,Ch.50,Cor.3,p.520] and [Tre, Part III,Ch.50,Prop.50.2,(50.12),p.519]), $\Phi'_\gamma:\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta\to\mathcal S(\mathbf R_{>0})'_\beta$ is a linear topological embedding (see also Lemma 4.2.1.3).

We call $B:=\{a_m(\cdot)\}_{m\in\mathbf Z}\subset\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta$ the set of continuous functionals from (4.2.1.4). To see that $B$ is bounded in $\mathcal S(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta$, it is enough to show that its image under $\Phi'_\gamma$ is bounded in $\mathcal S_{\mathrm E}(\mathbf R_{>0})'_\beta$.

To this end, we let $\phi\in\mathcal S_{\mathrm E}(\mathbf R_{>0})$ be arbitrary. By Theorem D.1.2.1, the image of $a_m(\cdot)$ under $\Phi'_\gamma$ is the unique continuous functional on $\mathcal S_{\mathrm E}(\mathbf R_{>0})$ whose image under the adjoint of the Mellin transform $M$ is the point-evaluation functional on $A\mathcal S(\mathbf C)$ supported at the point $z_m:=\frac{2\pi im}{\log(\gamma)}$, i.e.

$$
\Phi'_\gamma(a_m(\cdot))(\phi)=\int_{\mathbf R_{>0}}\phi(t)t^{\frac{2\pi im}{\log(\gamma)}}\frac{\mathrm dt}{t}=M(\phi)(z_m).
$$

For any $\sigma>0$, by the Asymptotic Residue Theorem (see Theorem B.3.2.1) we obtain, being $M(\phi)$ Schwartz uniformly over the vertical strips of bounded width of the complex $s$-plane:

$$
M(\phi)(z_m)=-\frac{1}{2\pi i}\int_{-\sigma-i\infty}^{-\sigma+i\infty}\frac{M(\phi)(z)}{z-z_m}\,\mathrm dz
+\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}\frac{M(\phi)(z)}{z-z_m}\,\mathrm dz. \tag{4.2.1.18}
$$

We deduce the estimate:

$$
|M(\phi)(z_m)|\le\frac{1}{2\pi}\left(\int_{-\infty}^{+\infty}\frac{1}{\sigma^2+|\tau-\frac{2\pi m}{\log(\gamma)}|^2}\,\mathrm d\tau\right)^{1/2}
\left\{\|M(\phi)\|_{L^2(-\sigma+i\mathbf R,\mathrm d\tau)}+\|M(\phi)\|_{L^2(\sigma+i\mathbf R,\mathrm d\tau)}\right\} \tag{4.2.1.19}
$$

and since the right side of (4.2.1.19) is independent of $m\in\mathbf Z$, we deduce that $\Phi'_\gamma(B)$ is simply bounded in $\mathcal S_{\mathrm E}(\mathbf R_{>0})'_\beta$. Since $\mathcal S_{\mathrm E}(\mathbf R_{>0})$ is a Fréchet space by Lemma D.3.1.2, hence barrelled, then by [Scha, Ch.III,§4.2,Thm.p.83] we deduce that $\Phi'_\gamma(B)$ is equicontinuous (and hence so is $B$ in $\mathcal S_{\mathrm E}(\mathbf R_{>0}/\gamma^{\mathbf Z})'_\beta$). By [Scha, Ch.III,§4.1,Corollary,p.83], it is bounded in $\mathcal S_{\mathrm E}(\mathbf R_{>0})'_\beta$, which is what we wanted to show. $\square$

## PDF page 170

**170** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

REMARK 4.2.1.8 (On the unboundedness of the exponential system). Note that throughout the proof of Lemma 4.2.1.5, we have shown that the canonical continuous linear map:

$$
\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})
$$

is a linear topological isomorphism. We will be reprising this in general in Corollary 4.5.3.1.

We have shown that the absolute Schauder basis $\{e_m\}_{m\in\mathbf{Z}}$ given by the exponential system on $E:=\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ respectively, is shrinking, i.e. its sequence of continuous coefficient functionals $\{a_m(\cdot)\}_{m\in\mathbf{Z}}\subset E'$ is itself a Schauder basis. It is also strongly bounded and an equicontinuous subset of $E'$.

By [Kal, §2,Prop.2.1,p.92], $\{e_m\}_{m\in\mathbf{Z}}$ is a regular Schauder basis (see Definition 4.1.2.1(6)), and by [Kal, §5,Thm.5.6,p.103], it cannot be bounded, otherwise it would be normalized (see Definition 4.1.2.1(6)), and hence normal, in the sense of [Kal, §1,Def.1.3,p.91]. However, since $E$ is a nuclear Fréchet space, hence Montel, this cannot be the case, given [Kal, §5,Thm.5.6,p.103].

Indeed, let $N\ge 0$ be an integer, and consider the continuous seminorm $p_N$ on $\mathcal{S}(\mathbf{R}_{>0})$ defined as

$$
p_N(\phi):=\sup_{t\in\mathbf{R}_{>0}}\lvert(t\partial_t)^N\phi(t)\rvert.
$$

Then $p_N(e_m)=\left(\frac{2\pi\lvert m\rvert}{\log(\gamma)}\right)^N$. $p_N$ induces a continuous seminorm on $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ which, evaluated on $e_m$, grows polynomially with respect to $\lvert m\rvert$ as $\lvert m\rvert\to+\infty$, showing that $\{e_m\}_{m\in\mathbf{Z}}$ is not bounded in $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, and hence in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$.

**4.2.2. Schauder bases on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ with a support condition.** Recall that for any compact subset $K\subset\mathbf{R}_{>0}$ with non-empty interior, we denote by $\mathcal{D}_K(\mathbf{R}_{>0})\subset\mathcal{D}(\mathbf{R}_{>0})$ the linear subspace of those smooth compactly supported functions on $\mathbf{R}_{>0}$ whose support is contained in $K$.

By [Sch-a, Thm.II,p.66] and [Scha, Ch.II,§6,6.4,p.58], the topology induced on $\mathcal{D}_K(\mathbf{R}_{>0})$ by the locally convex inductive limit topology on $\mathcal{D}(\mathbf{R}_{>0})$ is the topology of uniform convergence on functions and their derivatives of any order, i.e. the continuous linear inclusion $\mathcal{D}_K(\mathbf{R}_{>0})\subset\mathcal{D}(\mathbf{R}_{>0})$ is a linear topological embedding.

We let $\gamma\in\mathbf{R}_{>0}$ be a real number satisfying $\gamma>1$.

We will now show that the exponential system in $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, which, so far, we have shown can be lifted to a sequence in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, can in fact be lifted to a sequence of smooth compactly supported functions all contained in $\mathcal{D}_K(\mathbf{R}_{>0})$, for a large enough compact subset $K\subset\mathbf{R}_{>0}$ with non-empty interior, depending only on $\gamma$.

This means, in particular, that all basis elements comprising the exponential system in $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ can be lifted to smooth compactly supported functions on $\mathbf{R}_{>0}$ whose support is contained within the same compact subset $K\subset\mathbf{R}_{>0}$ with non-empty interior, so long as $K$ satisfies a largeness condition dependent on $\gamma$.

The argument rests on one of the forms of the Paley-Wiener Theorem, and specifically on [Ru-2, Ch.19,Thm.19.3,p.375].

In this form, recall that the Paley-Wiener asserts the following:

THEOREM 4.2.2.1 (Paley-Wiener Theorem on compactly supported Fourier transforms). *Let $A>0$ be a real number, $f\in\mathscr{H}(\mathbf{C})$ an entire function.*

*The following conditions on $f$ are equivalent:*

(1) *There exists $F\in L^2((-A,A),\lambda)$, for $\lambda$ the normalized Lebesgue measure, such that:*

$$
f(z)=\int_{-A}^{A}F(x)e^{ixz}\,\mathrm{d}x \tag{4.2.2.1}
$$

as entire functions of $z\in\mathbf{C}$.

## PDF page 171

**4.2. BASES OF EXPONENTIALLY DECAYING SCHWARTZ-BRUHAT FUNCTIONS: THE CASE $G=\mathbf{R}_{>0}$** · **171**

(2) *There exists a real number $C>0$, such that for every $z\in\mathbf{C}$, we have $\lvert f(z)\rvert\le Ce^{A\lvert z\rvert}$, and the restriction of $f$ to the real line is in $L^2(\mathbf{R},\lambda)$.*

We refer the reader to [Ru-2, Ch.19,Thm.19.3,p.375]. Theorem 4.2.2.1 can be read through the lens of the smooth change of variables $x=-i\log(t)$: part (1) asserts the existence of $F\in L^2((1/A,A),\mathrm{d}t/t)$ such that:

$$
f(s)=\int_{1/A}^{A}F(t)t^s\,\frac{\mathrm{d}t}{t}
$$

as entire functions of $s\in\mathbf{C}$.

Part (2) asserts the existence of a real number $C>0$ such that $\lvert f(s)\rvert\le CA^{\lvert\sigma\rvert}$ for all $s\in\mathbf{C}$, with $\sigma:=\mathrm{Re}(s)$, and that the restriction of $f$ to the imaginary line is in $L^2(i\mathbf{R},\lambda)$.

PROPOSITION 4.2.2.2. Let $\gamma\in\mathbf{R}_{>0}$ be a real number, $\gamma>1$.

(1) *If $K$ has non-empty interior and the quotient $\mathbf{R}_{>0}\to\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$ maps $K$ surjectively onto $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$, then the induced continuous linear map:*

$$
\Phi_\gamma:\mathcal{D}_K(\mathbf{R}_{>0})/(\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0}))\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}) \tag{4.2.2.2}
$$

*is a linear topological isomorphism. The assumption on $K$ is satisfied by the compact subsets of the form $K=b\cdot[1/a,a]$ for $a,b>0$ real numbers, $a>1$ with $2\log(a)>\log(\gamma)$.*

(2) *Under the assumption on $K$ from (1), assume that we have $K=b\cdot[1/a,a]$ for $a,b>0$ real numbers, $a>1$. Let $\phi$ be an element in the intersection $\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0})$. Let $A_0>0$ be a real number such that $K\subset[1/A_0,A_0]$, and define $A:=\lvert-\log(\gamma)+\log(A_0)\rvert$, and $K_A:=[e^{-A},e^{A}]\subset\mathbf{R}_{>0}$.*

*There exists $\psi\in\mathcal{D}_{K_A}(\mathbf{R}_{>0})$ such that $\psi(x)-\psi(\gamma x)=\phi(x)$ as smooth compactly supported functions on $\mathbf{R}_{>0}$, the identity holding in $\mathcal{D}_{K_A\cup\gamma^{-1}K_A}(\mathbf{R}_{>0})$.*

REMARK 4.2.2.3. Note that the largeness condition on $K$ from (1) is satisfied, for instance, if $K$ contains an interval of the form $\gamma^N[1-\varepsilon,\gamma+\varepsilon]$ for some integer $N\ge 1$ and a real number $0<\varepsilon<1$.

We begin with the following:

LEMMA 4.2.2.4. *For any compact subset $K\subset\mathbf{R}_{>0}$ with non-empty interior, the linear subspace $\mathcal{D}_K(\mathbf{R}_{>0})\subset\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ is closed, and the subspace topology agrees with the topology on $\mathcal{D}_K(\mathbf{R}_{>0})$ of uniform convergence of functions and their derivatives of arbitrary order.*

PROOF. The subspace topology on $\mathcal{D}_K(\mathbf{R}_{>0})$ is stronger than the Fréchet topology of uniform convergence on functions and their derivatives of arbitrary order (because it is defined by a larger fundamental family of seminorms; see Definition D.3.3.1).

With respect to the subspace topology, $\mathcal{D}_K(\mathbf{R}_{>0})$ is a closed subspace, since such topology preserves the support condition upon formation of limits in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ of Cauchy sequences of elements in $\mathcal{D}_K(\mathbf{R}_{>0})$, and hence $\mathcal{D}_K(\mathbf{R}_{>0})$ is sequentially closed in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, hence closed, being $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ a Fréchet space by Lemma D.3.1.2.

Since $\mathcal{D}_K(\mathbf{R}_{>0})$ is a Fréchet space with respect to the topology of uniform convergence on functions and their derivatives of arbitrary order, the two topologies are equivalent by the Open Mapping Theorem (see [NB, Thm.14.4.5(b)]). $\square$

PROOF OF PROPOSITION 4.2.2.2. (1) : Under the given assumptions on $K$, the continuous linear operator $\mathcal{D}_K(\mathbf{R}_{>0})\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ is surjective, hence open by the Open Mapping Theorem (see [NB, Thm.14.4.5(b)]), being source and target Fréchet spaces. Since it induces an injective linear operator from the Hausdorff quotient $\mathcal{D}_K(\mathbf{R}_{>0})/(\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0}))$, itself a Fréchet space, to $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, the linear operator $\Phi_\gamma$ from (4.2.2.2) is therefore a linear topological isomorphism.

## PDF page 172

**172** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

We show that if $K=b\cdot[1/a,a]$ for $a,b\in\mathbf{R}_{>0}$, with $a>1$, then $K$ satisfies the surjectivity condition in (2), i.e. $\Phi_\gamma$ from (4.2.2.2) is surjective in this case.

Indeed, let $u_0\in\mathcal{D}_K(\mathbf{R}_{>0})$ be a real valued nonnegative function whose support contains $b'\cdot[1,\gamma]$ in its interior for some $b'>0$. $u_0$ exists because $2\log(a)>\log(\gamma)$, and so $[1,\gamma]\subset ab\cdot(1/a,a)$, and it is enough to choose $b':=1/a$.

The compact subset $b'\cdot[1,\gamma]$ maps surjectively onto $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$ under the quotient homomorphism $\pi:\mathbf{R}_{>0}\to\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$, since $\gamma^{\mathbf{Z}}\cdot(b'\cdot[1,\gamma])=b'\cdot(\bigcup_{m\in\mathbf{Z}}\gamma^m\cdot[1,\gamma])=b'\cdot\mathbf{R}_{>0}=\mathbf{R}_{>0}$. Then $u_1:=\Phi_\gamma(u_0)$ is real valued, nonnegative, nowhere vanishing over $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$. As a function of $x\in\mathbf{R}_{>0}$, it is smooth and $\gamma^{\mathbf{Z}}$-invariant, and it is nowhere vanishing over $b'\cdot[1,\gamma]$, and hence over $\gamma^{\mathbf{Z}}\cdot(b'\cdot[1,\gamma])=\mathbf{R}_{>0}$.

Let $\phi\in\mathcal{D}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$. Then $\widetilde{\phi}:=u_0\cdot\frac{\phi\circ\pi}{u_1}$ is smooth, compactly supported with support contained within the support of $u_0$, which is in turn contained in $b\cdot[1/a,a]$, and we have

$$
\Phi_\gamma(\widetilde{\phi})=\Phi_\gamma(u_0)\cdot\frac{\phi\circ\pi}{u_1}=\Phi_\gamma(u_0)\cdot\frac{\phi\circ\pi}{\Phi_\gamma(u_0)}=\phi\circ\pi
$$

since $\frac{\phi\circ\pi}{u_1}$ is $\gamma^{\mathbf{Z}}$-invariant. As a function on $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$, this is $\phi$, which proves that $\Phi_\gamma$ is surjective in the case $K=b\cdot[1/a,a]$ with $2\log(a)>\log(\gamma)$.

We further refer the reader to the argument in [Bou-II, Ch.VII,§2,no.2,Remark 1,INT VII.30].

(2) : We let $K\subset\mathbf{R}_{>0}$ be a compact subset of the form $K=b\cdot[1/a,a]$ for $a,b>0$ real numbers, $a>1$. If the assertion holds for $K'=[1/a,a]$, then it holds for $K$. Indeed, $\phi\in\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0})$, then the same holds for $\phi(bx)$ as a function of $x\in\mathbf{R}$, and if $\psi_0$ satisfies conditions (a) and (b) for $\phi(bx)$, then $K_0\subset[e^{-A},e^{A}]$ with $A:=\lvert-\log(\gamma)+\log(a)\rvert$. Then upon choosing $A_0:=\max\{ab,a/b\}$, we have $b\cdot[1/a,a]\subset[1/A_0,A_0]$, and $\psi(b^{-1}x)$ is supported over a compact subset of $[e^{-A'},e^{A'}]$ for $A':=\lvert-\log(\gamma)+\log(A_0)\rvert$.

It is therefore enough to treat the case $b=1$, and that the assertion holds in the special case $K=[1/a,a]$ for any real number $a>1$ satisfying the largeness condition for (2). In particular, $a$ satisfies $2\log(a)\ge\log(\gamma)$.

Let $\phi\in\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0})$ be the arbitrary element. Then $M(\phi)(s)$ is an entire function on the complex $s$-plane, Schwartz uniformly over the open vertical strips of bounded width, and, by the Paley-Wiener Theorem (see [Ru-2, Ch.19,Thm.19.3,p.375] which applies since we have in particular $\phi\in L^2((1/a,a),\mathrm{d}t/t)$), it satisfies the estimate:

$$
M(\phi)(s)=O(a^{\lvert\mathrm{Re}(s)\rvert}) \tag{4.2.2.3}
$$

as $\lvert\mathrm{Re}(s)\rvert\to+\infty$. The function:

$$
u(s):=\frac{1}{1-\gamma^{-s}}M(\phi)(s) \tag{4.2.2.4}
$$

is meromorphic, with poles located at the countable discrete subset of $i\mathbf{R}$ comprised by the points

$$
\left\{z_m:=\frac{2\pi im}{\log(\gamma)},m\in\mathbf{Z}\right\}.
$$

Since the function $1-\gamma^{-s}$ is periodic, so is its reciprocal as a meromorphic function on the complex $s$-plane, and hence it has slow growth near its poles in the sense of Definition B.3.1.1. The Asymptotic Residue Theorem therefore applies (see Theorem B.3.2.1). Since $\phi\in\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0})$, then, by Proposition 4.2.1.5, $u$ has only removable singularities. The Asymptotic Residue Theorem therefore gives, for any $\sigma>0$ and any integer $N\ge 0$:

$$
-\frac{1}{2\pi i}\int_{-\sigma-i\infty}^{-\sigma+i\infty}\frac{z^Nu(z)}{z-s}\,\mathrm{d}z+\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}\frac{z^Nu(z)}{z-s}\,\mathrm{d}z=\mathrm{Res}_{z=s}\frac{z^Nu(z)}{z-s}=s^Nu(s) \tag{4.2.2.5}
$$

where $u$ is redefined as its unique extension across each removable singularity $s=z_m$ for $m\in\mathbf{Z}$. Since $u$ is Schwartz on every vertical line of nonzero abscissa, the two line integrals in (4.2.2.5) are bounded uniformly with respect to $s$ varying over the vertical strip of bounded width $(-\sigma+\varepsilon,\sigma-\varepsilon)$, upon choosing $\sigma$ large

## PDF page 173

**4.2. BASES OF EXPONENTIALLY DECAYING SCHWARTZ-BRUHAT FUNCTIONS: THE CASE $G=\mathbf{R}_{>0}$** · **173**

enough, and $\varepsilon>0$ such that $\sigma-\varepsilon>0$. It follows that $u$ is also entire and Schwartz uniformly on the open vertical strips of bounded width. Moreover, since $M(\phi)$ satisfies (4.2.2.3), then $u$ satisfies:

$$
u(s)=O(e^{\lvert\mathrm{Re}(s)\rvert\cdot\lvert\log(\gamma)-\log(a)\rvert}) \tag{4.2.2.6}
$$

as $\lvert\mathrm{Re}(s)\rvert\to+\infty$.

Another application of the Paley-Wiener Theorem gives that the inverse Fourier transform $\psi\in\mathcal{S}(\mathbf{R}_{>0})$, is, in fact, compactly supported over $K_0:=[e^{-\lvert-\log(\gamma)+\log(a)\rvert},e^{\lvert-\log(\gamma)+\log(a)\rvert}]$ (see the proof of [Ru-2, Ch.19,Thm.19.3,p.375], which shows that under the stated conditions, $\psi(e^x)$ must vanish, as a function of $x\in\mathbf{R}$, over the complement of the interval $[-A,A]$, for $A:=\lvert-\log(\gamma)+\log(a)\rvert$).

We have, $\phi(x)=\psi(x)-\psi(\gamma x)$ as smooth functions of $x\in\mathbf{R}_{>0}$, since

$$
M(\phi)(s)=(1-\gamma^{-s})u(s)=(1-\gamma^{-s})M(\psi)(s).
$$

Moreover, if $\gamma>a$, $K_0$ is contained within $[a/\gamma,\gamma/a]$. If $a>\gamma$, then $K_0$ is contained within $[\gamma/a,a/\gamma]$. $\square$

As a Corollary of Lemma 4.2.1.5 and Proposition 4.2.2.2, we obtain the following:

PROPOSITION 4.2.2.5. Let $\gamma\in\mathbf{R}_{>0}$ be a real number, $\gamma>1$.

Then:

(1) *the continuous functionals $\delta_{z_m}:\phi\mapsto\int_{\mathbf{R}_{>0}}\phi(t)t^{z_m}\,\frac{\mathrm{d}t}{t}$, for $z_m:=-\frac{2\pi im}{\log(\gamma)}$ with $m\in\mathbf{Z}$, are an absolute Schauder basis for the orthogonal of $\ker(\Phi_\gamma)$ with respect to the duality $\langle\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}),\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})'\rangle$, equipped with the strong topology on the dual $(\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})/\ker(\Phi_\gamma))'$, equivalently with the subspace topology inherited from the strong topology on $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})'_\beta$.*

(2) *The exponential system in $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ can be lifted to a sequence of smooth compactly supported functions on $\mathbf{R}_{>0}$, whose support can be chosen to be contained in $\mathcal{D}_K(\mathbf{R}_{>0})$ for $K=b\cdot[1/a,a]$ and $a,b\in\mathbf{R}_{>0}$ satisfying $2\log(a)>\log(\gamma)$, and its image in the quotient Fréchet space $\mathcal{D}_K(\mathbf{R}_{>0})/(\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0}))$ is an absolute Schauder basis. Under this assumption on $a$, the image of the functionals $\delta_{z_m}$ is an absolute Schauder basis for the strong dual of $\mathcal{D}_K(\mathbf{R}_{>0})/(\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0}))$.*

PROOF. (1) is Lemma 4.2.1.5(3), and by Proposition 4.2.2.2(2) the assertion on the compact support of the bi-orthogonal sequence to $\{\delta_{z_m}\}_{m\in\mathbf{Z}}$ holds for $K=b\cdot[1/a,a]$. The assertion on the image of $\{\delta_{z_m}\}_{m\in\mathbf{Z}}$ under the continuous adjoint to the continuous linear map:

$$
\mathcal{D}_K(\mathbf{R}_{>0})/(\ker(\Phi_\gamma)\cap\mathcal{D}_K(\mathbf{R}_{>0}))\to\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})/\ker(\Phi_\gamma) \tag{4.2.2.7}
$$

follows upon observing that (4.2.2.7) is a linear topological isomorphism by Proposition 4.2.2.2(2), and hence so is its adjoint, and linear topological isomorphisms preserve the defining conditions of an absolute Schauder basis. $\square$

REMARK 4.2.2.6. We note that the proofs of Lemma 4.2.1.5 and Proposition 4.2.2.2 give the existence of continuous linear sections to the $\gamma^{\mathbf{Z}}$-periodization operators $\Phi_\gamma:\mathcal{S}(\mathbf{R}_{>0})\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ and $\Phi_\gamma:\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\to\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, associated to a choice of smooth compactly supported function $u_1$ identically equal to $1$ over a compact interval of the form $[1,\gamma]\subset\mathbf{R}_{>0}$, and which vanishes outside of a small open neighborhood of $[1,\gamma]$. Indeed, such section is defined as, upon denoting by $\pi:\mathbf{R}_{>0}\to\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$ the smooth quotient homomorphism, $\eta(\phi):=\frac{u_1}{\Phi_\gamma(u_1)}\cdot(\phi\circ\pi)$. Compactness of the support of $u_1$, and hence of $\frac{u_1}{\Phi_\gamma(u_1)}$, ensures the sequential continuity of $\eta$, and since both $\mathcal{S}(\mathbf{R}_{>0})$ and $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ are metrizable, $\eta$ is continuous.

We note that since $\mathbf{R}_{>0}/\gamma^{\mathbf{Z}}$, $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ is linearly and topologically isomorphic to the nuclear Fréchet space $\mathfrak{s}$ of rapidly decreasing sequences. Hermite functions, moreover, provide a Schauder basis for $\mathcal{S}(\mathbf{R}_{>0})$ identifying, linearly and topologically, $\mathcal{S}(\mathbf{R}_{>0})$ with the nuclear Fréchet space of rapidly decreasing sequences $\mathfrak{s}$ itself (see [Simon, §1,Thm.1,p.140]).

## PDF page 174

**174** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

The kernel of $\Phi_{\gamma}$ in $\mathcal{S}(\mathbf{R}_{>0})$ is a copy of $\mathcal{S}(\mathbf{R}_{>0})$ itself, and so, up to linear topological isomorphism, $\mathcal{S}(\mathbf{R}_{>0})$ is realized as being isomorphic to a split linear topological extension of $\mathfrak{s}$ by $\mathfrak{s}$.

This is, of course, well known, since we have a linear topological isomorphism $\mathfrak{s}\times\mathfrak{s}\simeq\mathfrak{s}$.

**4.3. Preparations on isotypic projectors**

In this section, we study the continuous action of a compact Hausdorff abelian group $k$ on a Hausdorff locally convex topological $\mathbf{C}$-vector space $E$, and discuss assumptions on $E$ and on the action of $k$ on $E$, so that $E$ splits, linearly and topologically as a continuous $\mathbf{C}$-linear representation of $k$, into a (completed, under suitable completeness conditions on $E$) topological direct sum of generalized eigenspaces for the continuous action of $k$ on $E$.

We will be first discussing the special case of $E$ a separable Hilbert space and $k:=G^1$ the compact Hausdorff closed subgroup of elements of module-$1$ in an $\mathbf{R}_{>0}$-modulated group $G$. We recall from Definition D.2.1.1 that we term $\mathbf{R}_{>0}$-modulated those Hausdorff locally compact abelian groups $G$ equipped with a continuous proper surjective homomorphism $\lvert\cdot\rvert_G$ to $\mathbf{R}_{>0}$, i.e. $G^1:=\ker(\lvert\cdot\rvert_G)$.

We further refer the reader to §D.3.3 for more on modulated groups, and to Theorem D.3.3.7 for the structure of their Schwartz-Bruhat spaces (of $I$-exponential decaying Schwartz-Bruhat functions).

SITUATION 4.3.0.1 (Isotypic projectors - preparatory notation). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

(1) We denote by $G$ either the Hausdorff locally compact abelian group $C_F$, or $J_{F,S}$.

(2) We denote $\nu$ the Haar measure $\bar{\mu}$ on $C_F$, respectively $\bar{\mu}_S$ on $J_{F,S}$.

(3) We write $G^1$ for the closed subgroups $C_F^1$ of $C_F$, respectively $J_{F,S}^1$ of $J_{F,S}$, and we denote by $\nu_1$ the Haar measure $\bar{\mu}_1$ on $C_F^1$, respectively $\bar{\mu}_{S,1}$ on $J_{F,S}^1$, obtained upon choosing a continuous homomorphic section $\tau$ to the idelic norm, respectively to the $S$-idelic norm.

In practice, $G$ will be often assumed to satisfy the conditions from Situation 4.3.0.1.

Throughout this section and this Chapter, unless otherwise stated, it will be assumed to be a second-countable $\mathbf{R}_{>0}$-modulated group with closed subgroup of module-$1$ elements $G^1$. We will denote by $\lvert\cdot\rvert_G$ the module of $G$, i.e. the continuous proper surjective homomorphism to $\mathbf{R}_{>0}$ promoting $G$ to an $\mathbf{R}_{>0}$-modulated group.

**4.3.1. Strong continuity and unitarity.** We let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group with module $\lvert\cdot\rvert_G$. We denote by $G^1$ the kernel of $\lvert\cdot\rvert_G$. We let $\nu$ a choice of Haar measure on $G$. We further choose a Haar measure $\nu_1$ on the compact Hausdorff abelian group $G^1$.

In this subsection we record some results on $G^1$-isotypes within the left-regular representation

$$
R(G):=L^2(G,\nu)
$$

of $G$.

By this we mean, for each continuous character $\omega$ of $G^1$, the closed subspace

$$
R(G)(\omega):=\{\phi\in R(G):\rho_G(g,\phi)=\omega(g)\phi\text{ for all }g\in G^1\}
$$

where we denote by $\rho_G$ the left-translation action by $G^1$ on $R(G)$ induced by that of $G$.

The closed subspaces $R(G)\omega)$ are simpler to study since they are separable Hilbert spaces, being $R(G)$ a separable (since $G$ is second-countable; see [Fol, Prop.6.7]) Hilbert space. We will be recalling some important facts about them, for later use in the early arguments of this Chapter, throughout this subsection.

We will later introduce a locally convex analog of the spaces $R(G)(\omega)$, which will require more work to describe.

## PDF page 175

**4.3. PREPARATIONS ON ISOTYPIC PROJECTORS** · **175**

4.3.1.1. *Left-regular representation of $G$ on $L^2(G,\nu)$.* Before we arrive at the main construction, we need information on the left-regular representation of $G$ on $L^2(G,\nu)$.

DEFINITION 4.3.1.1. Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group, with module $\lvert\cdot\rvert_G$, closed subgroup of module-$1$ elements $G^1$. Let $\nu$ be a choice of Haar measure on $G$, and $\nu_1$ a choice of Haar measure on $G^1$.

We define the Hilbert space

$$
R(G):=L^2(G,\nu) \tag{4.3.1.1}
$$

to be the space of $\nu$-square-integrable complex-valued functions on $G$ with respect to the Haar measure $\nu$.

We write

$$
\langle\phi_1,\phi_2\rangle_{R(G)}:=\int_G\phi_1(g)\,\overline{\phi_2(g)}\,\mathrm{d}\nu(g) \tag{4.3.1.2}
$$

for the Hermitian inner product on $R(G)$, and $\lVert\cdot\rVert_{R(G)}$ for its $L^2$-norm $\langle\cdot,\cdot\rangle_{R(G)}^{1/2}$.

REMARK 4.3.1.2. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

Recall that the idelic “norm” $\lvert\cdot\rvert_F:\mathrm{GL}_1(\mathbf{A}_F)\to\mathbf{R}_{>0}$ is defined as the product $\prod_v\lvert\cdot\rvert_v$ of all $v$-adic absolute values on each $F_v$; see (A.1.3.2). $\lvert\cdot\rvert_F$ is not a norm and it is only referred to as such, by convention. Rather, it is only a continuous homomorphism of Hausdorff locally compact abelian topological groups. Moreoever, recall that by Artin’s product formula, we have $\lvert F^{\times}\rvert_F=1$. We will denote by $\mathrm{GL}_1(\mathbf{A}_F)^1$ the closed subgroup of “norm-one” elements in $\mathrm{GL}_1(\mathbf{A}_F)$, i.e. the kernel of $\lvert\cdot\rvert_F$. Its topology is the subspace topology. Similar assertions hold for the $S$-idelic norm $\lvert\cdot\rvert_{F,S}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and its class group $J_{F,S}:=\mathrm{GL}_1(\mathbf{A}_{F,S})/\mathcal{O}_{F,S}^{\times}$.

The reader may assume that the $\mathbf{R}_{>0}$-modulated group $G$ satisfies the assumptions from Situation 4.3.0.1, i.e. it is either $C_F$ or $J_{F,S}$.

As for $G=C_F,J_{F,S}$, a general $\mathbf{R}_{>0}$-modulated group admits continuous homomorphic sections to the module $\lvert\cdot\rvert_G$; see Remark D.2.1.2.

We recall the following facts about the Haar measure $\nu$ on $G$.

LEMMA 4.3.1.3. *The measure $\nu$ on $G$ is regular, Radon and $\sigma$-finite.*

PROOF. Since $\nu$ is Radon as a Borel measure on $G$, as any Haar measure on a locally compact Hausdorff abelian group, $\nu$ is finite on compact subsets (see [DE, Thm.1.3.5]). It is therefore regular Radon by [Fol, Thm.7.8]. Since $G$ is second-countable, then it is $\sigma$-compact, and hence $\nu$ is $\sigma$-finite. $\square$

REMARK 4.3.1.4. One important consequence of Lemma 4.3.1.3 is that $C_c(G)$, the complex vector space of complex valued continuous compactly supported functions on $G$, is contained in $L^2(G,\nu)=R(G)$ and it is dense in the $L^2$-norm topology. This is [Fol, Prop.7.9] or [DE, Prop.1.3.3], applied to $X=G$, $\mu$ in either Theorem is the Haar measure $\nu$, and $p=2$.

We note that $R(G)$ carries an action of $G$ by left-translation on functions through its continuous left-translation action on itself.

It is defined as follows: on continuous compactly supported functions, we define

$$
\rho_G:G\times C_c(G)\to C_c(G) \tag{4.3.1.3}
$$

by the assignment, for any $\phi\in C_c(G)$, and any $(g,x)\in G\times G$

$$
\rho_G(g,\phi)(x):=\phi(g^{-1}x) \tag{4.3.1.4}
$$

We will recall below that $\rho_G$ extends uniquely to $R(G)$ as a continuous representation of $G$.

## PDF page 176

**176** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

LEMMA 4.3.1.5 (Basic properties of the left-regular representation $R(G)$). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group. Let $\tau$ be a choice of continuous homomorphic section to the module $\lvert\cdot\rvert_G$. The Hilbert space $R(G)$ satisfies the following conditions:*

(1) $R(G)$ is separable.

(2) *$\rho_G$ from (4.3.1.4) uniquely extends to a continuous unitary representation of $G$ on $R(G)$. For every $\phi_1,\phi_2\in R(G)$ and every $g\in G$, we have*

$$
\langle\rho_G(g,\phi_1),\rho_G(g,\phi_2)\rangle_{R(G)}=\langle\phi_1,\phi_2\rangle_{R(G)}. \tag{4.3.1.5}
$$

(3) Upon defining the assignment

$$
U_{G,\tau}:\mathbf{R}_{>0}\times R(G)\to R(G) \tag{4.3.1.6}
$$

*as $U_{G,\tau}(t)(\phi):=\rho_G(\tau(t),\phi)$ for every $\phi\in R(G)$, then $U_{G,\tau}$ is a strongly continuous one-parameter group of unitary operators on $R(G)$.*

On the concept of continuity for $\rho_G$ being used, we devote a few words.

REMARK 4.3.1.6 (Strong continuity of the left-translation action of $G$ on $R(G)$). We note that continuity of $\rho_G$ from (4.3.1.4) is often referred to as strong continuity, usually in the context of one-parameter groups or semi-groups of unitary operators. It means that the map

$$
\rho_G:G\to\mathrm{GL}(R(G)) \tag{4.3.1.7}
$$

sending $g$ to $\rho_G(g,\cdot)$ is a continuous map with respect to the topology on the Hausdorff locally compact abelian group $G$ on the source, and the subspace topology of the strong operator topology on the target, $\mathrm{GL}(R(G))$ being the group of invertible continuous $\mathbf{C}$-linear endomorphisms of the Hilbert space $R(G)$.

That $\mathrm{GL}(R(G))$ is indeed a group, is a consequence of the Open Mapping Theorem (see [Cnw-a, Ch.III,Thm.12.1]).

The strong operator topology on $\mathscr{B}(R(G))$, the $\mathbf{C}$-vector space of bounded $\mathbf{C}$-linear endomorphisms of $R(G)$, is the Hausdorff locally convex topology defined by the separating family of seminorms $\{q_{\phi}\}_{\phi\in R(G)}$ with $q_{\phi}(T):=\lVert T(\phi)\rVert_{R(G)}$.

The group $\mathrm{GL}(R(G))$ is not a topological group with respect to the strong operator topology, if $R(G)$ is infinite dimensional (equivalently, if $G$ is not a finite abelian group).

The Lemma however says that $\rho_G$ factors through $\mathrm{U}(R(G))$, the unitary group of $R(G)$. The subgroup $\mathrm{U}(R(G))$ of $\mathrm{GL}(R(G))$ is a topological group with respect to the strong operator topology (because all subsets of $\mathrm{U}(R(G))$ are strongly bounded, hence equicontinuous by the Uniform Boundedness Principle (see [Scha, Ch.III,§4,Thm.4.2,p.83]; see also [Cnw-a, Ch.IX,§1,Prop.1.3(d),p.256]). It is Hausdorff, complete (by another application of the Uniform Boundedness Principle) but not locally compact, unless $R(G)$ is finite dimensional, equivalently if $G$ is a finite abelian group. It is second-countable, metrizable (see [EU, Lemma 1.6]) and hence paracompact.

We further note that by the Spectral Theorem for normal operators (see [Cnw-a, Ch.IX,§2,Thm.2.2,p.263]), $\mathrm{U}(R(G))$ is connected and path-connected, since for each $A\in\mathrm{U}(R(G))$, there exists a bounded, self-adjoint endomorphism $\phi(A)\in\mathscr{B}(R(G))$, for $\phi(z):=\theta$, $z=e^{i\theta}$ for $\theta\in[0,2\pi)$, a bounded Borel-measurable function $\phi:\mathrm{U}(1)\to[0,2\pi)\subset\mathbf{R}$, and since the spectrum $\sigma(A)$ is contained in $\mathrm{U}(1)$ (see [Cnw-a, Ch.IX,§2,Thm.2.3,p.264]), and the strongly continuous (by [Cnw-a, Ch.X,§5,Thm.5.1,p.327]) path $\gamma(t):=\exp(it\phi(A))$ connects $A=\gamma(1)$ to the identity $\mathrm{Id}=\gamma(0)$.

Note that indeed $\phi(A)$ is self-adjoint, since the image of $\phi$ is contained in $[0,+\infty)$, and hence, by [Cnw-a, Ch.IX,§2,(2.4),p.264] and [Cnw-a, Ch.IX,§1,Lemma 1.9,p.257] (noting that orthogonal projectors are positive operators), [Cnw-a, Ch.II,§2,Prop.2.12,p.33] applies.

## PDF page 177

**4.3. PREPARATIONS ON ISOTYPIC PROJECTORS** · **177**

Strong continuity of $\rho_G$ amounts to the homomorphism:

$$
\rho_G:G\to\mathrm{U}(R(G)) \tag{4.3.1.8}
$$

being a continuous homomorphism of Hausdorff topological groups.

We refer the reader to [Cnw-a, Ch.IX,Def.1.2], and to [Cnw-a, Ch.X,Def.5.3]. In Lemma 4.3.1.5(3), continuous unitary actions of $\mathbf{R}_{>0}$ on $R(G)$ are studied, induced by the action $\rho_G$ of $G$. Continuity of $\mathbf{R}_{>0}$ is intended with respect to the strong operator topology.

We refer to [HP, Ch.II,§2.16,p.51] for more on the strong operator topology, and to [Cnw-a, Ch.X,Thm.5.4] and to [HP, Ch.X] for comparisons among various notions of topologies on linear operators, for one-parameter unitary groups. Note that the strong operator topology on $\mathrm{U}(R(G))$ is equivalent to the weak operator topology (see [EU, Lemma 1.5]), while the norm-topology is generally strictly finer (see [EU, pp.50-51]). We further note that the strong operator topology on $\mathrm{U}(R(G))$ is equivalent to the topology of pre-compact convergence, by Uniform Boundedness and [Scha, Ch.III,§4,Thm.4.5,p.85]. In particular, $\mathrm{U}(R(G))$ is contractible, by [AS, Appendix 2,Prop.A2.1].

We further refer the reader to §C.3.3 and §C.3.4 in Appendix C, for more on the strong operator topology on separable Hilbert spaces and its properties.

PROOF OF LEMMA 4.3.1.5. (1) : Since the space $G$ is second-countable, hence separable (see Remark A.5.2.9, and, for the special case in which $G$ satisfies the assumptions from Situation 4.3.0.1, see Proposition A.2.3.10), and the measure $\nu$ is Radon and $\sigma$-finite by Lemma 4.3.1.3, $R(G)$ is a separable metric space by [Coh, Prop.3.4.5], hence separable as a Hilbert space.

(2) : For any $g\in G$, we have

$$
\int_G\phi_1(g^{-1}x)\,\overline{\phi_2(g^{-1}x)}\,\mathrm{d}\nu(x)=\int_G\phi_1(x)\,\overline{\phi_2(x)}\,\mathrm{d}\nu(gx) \tag{4.3.1.9}
$$

$$
=\int_G\phi_1(x)\,\overline{\phi_2(x)}\,\mathrm{d}\nu(x) \tag{4.3.1.10}
$$

$$
=\langle\phi_1,\phi_2\rangle_{R(G)} \tag{4.3.1.11}
$$

where we used $\mathrm{d}\nu(gx)=\mathrm{d}\nu(x)$, which is left invariance of the Haar measure $\nu$, along with [Bog, Thm.3.6.1] applied to $\nu(g^{-1}\cdot)=\nu$.

This proves (4.3.1.5). This proves in particular that $\lVert\rho_G(g,\phi)\rVert_{R(G)}=\lVert\phi\rVert_{R(G)}$ and continuity with respect to the strong operator topology on $\mathrm{GL}(R(G))$ follows from the definition. Note that in particular the operator $\rho_G(g,\cdot)$ has bounded operator norm (by $1$) for all $g\in G$.

Continuity follows from [DE, Lemma 6.1] too. Each $\rho_G(g,\cdot)$ on $C_c(G)$ therefore extends uniquely to $R(G)$ for every $g\in G$.

Stability of the operators $\rho_G(g,\cdot)$ under compositions in $g$ on $C_c(G)$ propagates the same property to all elements of $G$, providing the existence of the desired extension to a strongly continuous $\mathbf{C}$-linear action on $R(G)$. Uniqueness is ensured by denseness of $C_c(G)$ within $R(G)$, which holds by Lemma 4.3.1.3 (see Remark 4.3.1.4).

(3) : Since the section $\tau$ to the module $\lvert\cdot\rvert_G$ is continuous, composing $\rho_G$ with $(\tau,\mathrm{Id}_{R(G)})$ gives a continuous action $U_{G,\tau}:\mathbf{R}_{>0}\times R(G)\to R(G)$. We need only check that it is unitary.

This follows from the fact that $\lvert\tau(t)\rvert=\lvert t\rvert_{\mathbf{R}}$, where $\lvert t\rvert_{\mathbf{R}}$ is the Euclidean absolute value on $\mathbf{R}_{>0}$, and so unitarity of $U_{G,\tau}$ follows from (4.3.1.5). $\square$

**4.3.2. Orthogonal decomposition into $G^1$-isotypes.** We continue to assume that the Hausdorff locally compact abelian group $G$ is a second-countable $\mathbf{R}_{>0}$-modulated group, whose module (a given proper surjective continuous homomorphism onto $\mathbf{R}_{>0}$) we denote by $\lvert\cdot\rvert_G$, and we write $G^1$ for the compact Hausdorff closed subgroup of module-$1$ elements, i.e. $G^1:=\ker(\lvert\cdot\rvert_G)$.

## PDF page 178

**178** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

We further refer the reader to §D.2.1, for more on modulated groups.

We will be applying the contents of this subsection to the case $G$ satisfies the assumptions from Situation 4.3.0.1, and hence is, in particular, either $C_F$, or $J_{F,S}$, equipped with the module given by the idelic norm $|\cdot|_F$, respectively the $S$-idelic norm $|\cdot|_{F,S}$.

That, under these assumptions, $G^1$ is compact Hausdorff (and hence $G$ is $\mathbf{R}_{>0}$-modulated) is a consequence of Theorem A.1.4.3(1).

For any continuous character $\omega$ of $G^1$, we have a continuous linear map:

$$
\Pi_{G,\omega}(\phi)(x) := \int_{G^1} \overline{\omega(g)}\phi(g^{-1}x)\,\mathrm{d}\nu_1(g) = \int_{G^1} \omega(g)\phi(gx)\,\mathrm{d}\nu_1(g) \tag{4.3.2.1}
$$

defined for $\nu$-almost all $x \in G$, where $\nu_1$ is, recall, a choice of Haar measure on $G^1$.

In the special case $G$ satisfies the assumptions from Situation 4.3.0.1, then $\nu$ is the Tamagawa measure $\bar\mu$ on $C_F$, respectively $\bar\mu_S$ on $J_{F,S}$, i.e. the Haar measures from Definition ?? on $G$, and $\nu_1$ is uniquely determined as per Theorem D.1.2.1 by requiring compatibility with $\nu$ and $\mathrm{d}t/t$ on $\mathbf{R}_{>0} \simeq G/G^1$ (explicitly, uniquely determined by requiring that, upon choosing a continuous homomorphic section $\tau$ to the module $|\cdot|_G$, i.e. to the idelic, respectively $S$-idelic, norm, then $\nu$ satisfies $\nu = \nu_1 \otimes \tau_*(\mathrm{d}t/t)$, for $\mathrm{d}t/t$ the canonical Haar measure on $\mathbf{R}_{>0}$. See Definition D.2.1.1(2), Remark D.2.1.3 and Remark D.2.1.4).

We choose a continuous homomorphic section $\tau$ to the module $|\cdot|_G$.

The operator $\Pi_{G,\omega}$ is defined on $R(G) := L^2(G,\nu)$ and its composition with the pull-back along $\tau$ is valued in $L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t)$, where we define the action of $G$ on $L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t)$ as:

$$
\bar\rho_{G,\omega} : G \times L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t) \to L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t) \tag{4.3.2.2}
$$

on $\phi \in C_c(\mathbf{R}_{>0})$, by:

$$
\bar\rho_{G,\omega}(g,\phi)(x) := \omega(g)\phi(|g|_G^{-1}x) \tag{4.3.2.3}
$$

and extending $\bar\rho_{G,\omega}$ to $L^2(\mathbf{R}_{>0},\mathrm{d}t/t)$ by continuity and denseness of $C_c(\mathbf{R}_{>0})$ in $L^2(\mathbf{R}_{>0},\mathrm{d}t/t)$.

The composition of $\Pi_{G,\omega}$ with the pull-back along $\tau$, which we denote by $\Pi_{G,\omega,\tau}$, is therefore promoted to a continuous operator:

$$
\Pi_{G,\omega,\tau} : L^2(G,\nu) \to L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t) \tag{4.3.2.4}
$$

equivariant with respect to the action of $G^1$ obtained by restriction of $\rho_G$ to $G^1$, on the source and the action of $G^1$ obtained by restriction of the action $\bar\rho_{G,\omega}$ to $G^1$, on the target.

On $\phi \in C_c(G)$, we see that we have

$$
\|\Pi_{G,\omega,\tau}(\phi)\|_{L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t)} \le \|\phi\|_{L^2(G,\nu)} \tag{4.3.2.5}
$$

and so this remains true on all $\phi \in L^2(\Gamma,\nu)$ by continuity.

In particular, the unique continuous operator:

$$
\Pi_\tau : L^2(G,\nu) \to \prod_{\omega \in \widehat{G^1}} L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t) \tag{4.3.2.6}
$$

to the Hausdorff locally convex product factors through a continuous operator valued into the linear subspace

$$
\Pi_\tau : L^2(G,\nu) \to \widehat{\bigoplus}_{\omega \in \widehat{G^1}} L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t) \tag{4.3.2.7}
$$

the Hilbert sum of the Hilbert spaces $L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t)$.

This is the linear subspace

$$
\{(\phi_\omega)_{\omega \in \widehat{C_F^1}} : \phi_\omega \in L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t) \text{ for all } \omega \in \widehat{C_F^1},\ \sum_{\omega \in \widehat{C_F^1}} \|\phi_\omega\|^2_{L^2(\mathbf{R}_{>0},\mathrm{d}t/t)} < \infty\}
$$

## PDF page 179

**4.3. PREPARATIONS ON ISOTYPIC PROJECTORS** · **179**

for which we refer the reader to [Cnw-a, Ch.I,Prop.6.2,p.24].

Remark 4.3.2.1. Note that the metric topology on the Hilbert sum is finer than the subspace topology inherited from the locally convex product topology. Also note that by compactness of $G^1$ (which, in the case $G = C_F$, is a consequence of Theorem A.1.4.3(1), and for $G = J_{F,S}$, is a consequence of Theorem A.1.5.2(1), since $J^1_{F,S}$ is a quotient of $C^1_{F,S}$) the dual group $\widehat{G^1}$ is discrete, and since $G$ is second-countable, so is $G^1$, and hence $\widehat{G^1}$ is countable.

Countability of $\widehat{G^1}$ ensures that [Cnw-a, Ch.I,Prop.6.2,p.24] applies.

Note that in the special cases of interest, $G = C_F$ and $G = J_{F,S}$, the dual group of $G^1$ can be described explicitly enough to infer its countability directly. For instance, in the case $G = C_F$, the description of the connected component of the identity given in [AT, Ch.IX,Thm.3], provides a description of $\widehat{C_F^1}$, and we proceed as follows.

An application of [DE, Cor.3.6.2] reduces the proof of countability of $\widehat{C_F^1}$ to that of the dual of the connected component $(C_F^1)^0$ of the identity of $C_F^1$, and of the dual of $\mathrm{Gal}(F^{\mathrm{ab}}/F)$. The connected component $(C_F^1)^0$ is isomorphic as a compact Hausdorff topological abelian group, to $(\mathbf{A}_{\mathbf{Q}}/\mathbf{Q})^{r_1+r_2-1} \times (\mathbf{R}/\mathbf{Z})^{r_2}$, by [AT, Ch.IX,Thm.3], and its dual group $\widehat{(C_F^1)^0}$ is isomorphic as a discrete abelian group to $\mathbf{Q}^{r_1+r_2-1} \times \mathbf{Z}^{r_2}$, which is countable.

The dual group of $\mathrm{Gal}(F^{\mathrm{ab}}/F)$ is also countable, since $\mathrm{Gal}(F^{\mathrm{ab}}/F)$ has a countable neighborhood base at the identity comprising of open subgroups of finite index, and hence its dual group injects into a countable product of finite groups and it is therefore countable.

For any finite set $S$ of places of $F$ containing all the Archimedean places, the dual group of $C^1_{F,S}$ is a quotient of the dual group of $C^1_F$, and it is therefore also countable. The dual group of $J^1_{F,S}$ is a closed subgroup of the dual group of $C^1_{F,S}$, and it is therefore also countable.

Lemma 4.3.2.2 (Orthogonal decomposition into $G^1$-isotypes). *The operator $\Pi_\tau$ from (4.3.2.7) is a surjective isometry.*

Proof. By a consequence of the Peter-Weyl Theorem (see [Kn, Thm.1.12]), we have an isometry of complex Hilbert spaces, compatible with the structures of continuous unitary representations of $G^1$ on source and target:

$$
L^2(G,\nu) \simeq \widehat{\bigoplus}_{i\in I} H_i \tag{4.3.2.8}
$$

where $I$ is a set, and each $H_i$ is in turn a Hilbert space, isometric to a completed direct sum of one-dimensional continuous unitary representations of $G^1$ whose character is $\omega_i$, for a unique continuous character $\omega_i$ of $G^1$ such that $\rho_G(g,\phi_{i,n_i}) = \omega_i(g)\phi_{i,n_i}$, and for every pair of indeces $i_1,i_2 \in I$ with $i_1 \ne i_2$, $\omega_1 \ne \omega_2$.

For every nonzero $\phi \in L^2(G,\nu)$ there exists $i \in I$ such that the image $\phi_i$ of $\phi$ under the isomorphism of Hilbert spaces from (4.3.2.8), is nonzero. $G^1$ acts on $\phi_i$ by multiplication by the continuous unitary character $\omega_i$, since the isomorphism of Hilbert spaces in (4.3.2.8) is compatible with the continuous representation of $G^1$ structure on source and target.

Each $H_i$ is isometric under $\Pi_{G,\omega_i,\tau}$ to $L^2_{\omega_i}(\mathbf{R}_{>0},\mathrm{d}t/t)$. We further deduce that the map $i \mapsto \omega_i$ is an injective map $I \to \widehat{G^1}$. On the other hand, for each continuous character $\omega \in \widehat{G^1}$, the closed subspace $H_\omega \subset L^2(G,\nu)$ defined as:

$$
H_\omega := \{\phi \in L^2(G,\nu) : \rho_G(g,\phi) = \omega(g)\phi,\ g \in G^1\} \subset L^2(G,\nu)
$$

is such that $H_{\omega_i} = H_i$ for each $i \in I$.

If $\omega \in \widehat{G^1}$ exists which is not in the image of the injective map $I \to \widehat{G^1}$ from the foregoing, then $H_\omega$ maps to the trivial subspace of the Hilbert sum $\widehat{\bigoplus}_{i\in I} H_i$, and hence $H_\omega = 0$, since the continuous linear operator from (4.3.2.8) is a surjective isometry.

## PDF page 180

**180** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

This gives a contradiction (since $\varphi \otimes \overline{\omega}$ for any nonzero continuous compactly supported function $\varphi$ on $\mathbf{R}_{>0}$ induces a continuous compactly supported function on $G$ which is a nonzero element of $H_\omega$). We deduce that we have $I = \widehat{G^1}$. $\square$

We introduce the following:

Terminology 4.3.2.1 ($G^1$-isotypes on the regular representation $R(G)$ of an $\mathbf{R}_{>0}$-modulated group). Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group, with module $|\cdot|_G$. Let $\nu$ a choice of Haar measure on $G$, and $R(G) = L^2(G,\nu)$ its left-regular representation. Let $\nu_1$ be a choice of Haar measure on $G^1 := \ker(|\cdot|_G)$. Let $\omega \in \widehat{G^1}$ be a continuous character.

We denote by $R(G)(\omega)$ the closed linear subspace of the Hilbert space $R(G)$, of those elements that are $\omega$-homogeneous with respect to the continuous left-translation action by $G^1$ on $R(G)$ obtained by restriction to $G^1$ of the continuous left-translation action of $G$ on $R(G)$:

$$
R(G)(\omega) := \{\phi \in R(G) : \rho_G(g,\phi) = \omega(g)\phi,\ \text{for all } g \in G^1\} \subset R(G).
$$

We refer to $R(G)(\omega)$ as the $\omega$-isotype of $R(G)$, and to the orthogonal projector $\nu_1(G^1)^{-1}\Pi_{G^1,\omega}$ as the projection onto the $\omega$-isotype.

We note that for each $\omega \in \widehat{G^1}$, the closed subspace $R(G)(\omega)$ is isometric to $L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t)$ under the operator $\Pi_{G,\omega,\tau}$ of (4.3.2.7): the operator $\Pi_{G,\omega,\tau}$ factors through an isometry $R(G)(\omega) \to L^2_\omega(\mathbf{R}_{>0},\mathrm{d}t/t)$, and the kernel of $\Pi_{G,\omega,\tau}$ is linearly and topologically generated within $R(G)$ by the elements of the form $\phi - \overline{\omega}(g)\rho_G(g,\phi)$ as $(\phi,g)$ varies over $R(G) \times G^1$.

4.3.3. $G$-invariants in a quasi-complete Hausdorff locally convex topological vector space. Using the results on integration in the sense of Pettis from §C.4), the following Lemma 4.3.3.1 studies formation of continuous invariants and co-invariants under the continuous action of a compact Hausdorff abelian group $G$, on a quasi-complete Hausdorff locally convex topological $\mathbf{C}$-vector space $E$.

The Lemma will be used systematically throughout this Chapter in the presence of a continuous left-translation action by a compact Hausdorff abelian group, and we record it here for convenience.

Throughout the remainder of this subsection, $G$ will denote a compact Hausdorff abelian group, as opposed to a Hausdorff locally compact $\mathbf{R}_{>0}$-modulated group.

We recall that a Hausdorff locally convex topological $\mathbf{C}$-vector space $E$ is quasi-complete if and only if every bounded Cauchy net in $E$ converges in $E$ (see also Remark C.4.3.4).

Quasi-completeness is also termed, in light of the definition, bounded completeness, and a quasi-complete $E$ is also termed boundedly complete. We further refer the reader to §C.4.3 for more on quasi-completeness, a condition that, combined with the Bipolar Theorem (see [Bou-TVS, Ch.II,§6,No.3,Thm.1,TVS II.44]), ensures that the closed convex circled hull of a precompact subset of $E$ is contained in $E$ (see Lemma C.4.1.2(1)).

This leads to $E$-valued integration, for $E$ quasi-complete, to exist and be well behaved, as discussed in §C.4.3 (see Theorem C.4.3.5).

We refer the reader to §C.2, §C.5.1 and §C.3.3 for classes of examples of quasi-complete Hausdorff locally convex topological $\mathbf{C}$-vector spaces.

Lemma 4.3.3.1 (Norm isomorphism of continuous representations of compact Hausdorff abelian groups). *Let $G$ be a compact Hausdorff abelian group, $E$ a Hausdorff locally convex topological $\mathbf{C}$-vector space equipped with a continuous $\mathbf{C}$-linear action $\rho_G$ of $G$ by linear topological automorphisms. Let $\mu_G$ be a choice of Haar measure on $G$. Assume that $E$ is quasi-complete and that either one of the following two conditions is satisfied:
(a) the action $\rho_G$ is uniformly continuous, i.e. for every $u \in E$ and for every net $\{u_i\}_{i\in I} \subset E$ converging to $u$, we have $\rho_G(g,u_i) \to \rho_G(g,u)$ uniformly as $g \in G$.*

## PDF page 181

**4.3. PREPARATIONS ON ISOTYPIC PROJECTORS** · **181**

(b) *$E$ is bornological, and condition (a) is satisfied for every $u \in E$ and for every sequence $\{u_m\}_{m\ge 0} \subset E$ converging to $u \in E$.*

*Then:
(1) For every $u \in E$, the $\mathbf{C}$-linear form on $E'$:*

$$
\Phi_G(u) : \varphi \mapsto \int_G \langle\rho_G(g,u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g) \tag{4.3.3.1}
$$

*is in the image of the canonical continuous linear operator $\iota_E : E \to (E')^{\ast}$, i.e. $\Phi_G(u)$ is the evaluation functional on $E'$ on a unique element of $E$. Equivalently, the linear operator $\Phi_G : E \to (E')^{\ast}$ assigned by $u \mapsto \Phi_G(u)$, factors through $\iota_E$.*

*Its formation is continuous with respect to the intrinsic topology on $E$, i.e. $\Phi_G : E \to E$ is a continuous linear operator.*

(2) *$\Phi_G$ surjects onto the closed subspace $\mathrm{H}^0(G,E)$ of $G$-invariant elements of $E$, and $\mu_G(G)^{-1}\Phi_G$ is idempotent.*

*Upon denoting by $\mathrm{H}_{0,\mathrm{cont}}(G,E)$ the quotient of $E$ by the kernel of $\Phi_G$, then $\Phi_G$ factors through a linear topological isomorphism:*

$$
N_G : \mathrm{H}_{0,\mathrm{cont}}(G,E) \to \mathrm{H}^0(G,E) \tag{4.3.3.2}
$$

*with respect to the quotient topology on the source and the subspace topology on the target.*

(3) *The closed subspace $\ker(\Phi_G) \subset E$ is the closure of the $\mathbf{C}$-linear subspace $V_E$ generated by the elements $\{u - \rho_G(g,u),\ u \in E,\ g \in G\}$ as $u$ varies over $E$.*

Remark 4.3.3.2 (On $E$-valued integration). The reader may think of the operator $\Phi_G$ as an $E$-valued integral:

$$
\Phi_G = \int_G \rho_G(g,\cdot)\,\mathrm{d}\mu_G(g)
$$

in the sense of Pettis, for which we refer to Appendix C, and specifically to §C.4.

We highlight for the reader that the theory of $E$-valued integration is indeed needed for the purposes of this work beyond the case of Banach spaces, for multiple reasons, all related to the following fact.

Let $G$ be a Hausdorff locally compact abelian group, assume $G$ is compactly generated, and let $k \subset G$ be a compact subgroup with compactly generated orthogonal $k^\perp$. Then $\mathcal{S}(k,G)$, the closed subspace of $k$-invariant Schwartz-Bruhat functions on $G$, is a nuclear Fréchet space, and hence it is, in particular, never a Banach space, unless $G/k$ is finite.

Vector-valued integrals will often be, throughout this work, valued in $\mathcal{S}(G)$ or quotients of $\mathcal{S}(G)$, or in closed subspaces of $\mathcal{S}(k,G)$ and their quotients. This leads us to the necessity of vector-valued integration beyond the case of the Banach-valued integral of Bochner. We will be using continuity properties of the integral in the sense of Pettis, and the reader familiar with the Banach-valued theory of integration will recognize extensions of the known results on the Bochner integral, which is recovered as a spacial case, in §C.4.

Terminology 4.3.3.1 (Norm isomorphisms). We refer to the linear topological isomorphism $N_G$ from (4.3.3.2) as the norm isomorphism of $\rho_G$ on $E$.

Proof of Lemma 4.3.3.1. (1) : By Theorem C.4.3.5, applied to $X = G$, $\mu = \mu_G$, $f : X \to E$ defined as $f(g) := \rho_G(g,u)$ for each $u \in E$ fixed, we see that $f$ is $\mu$-integrable in the sense of Pettis, which implies that $\Phi_G(u)$, a priori only an element of $(E')^{\ast}$, is contained in $\iota_E(E)$. In particular, the assignment $u \mapsto \Phi_G(u)$ is $\iota_E(E)$-valued and linear, and hence it factors through $\iota_E$ as a $\mathbf{C}$-linear operator on $E \to (E')^{\ast}$. We denote by $\Phi_G$ the resulting unique linear operator $\Phi_G : E \to E$ such that its composition with $\iota_E$ is $\Phi_G : E \to (E')^{\ast}$.

By Lemma C.4.3.12, $\Phi_G : E \to E$ is continuous with respect to the intrinsic topology on $E$, if condition (a) is satisfied.

## PDF page 182

**182** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

If condition (b) is satisfied, instead, then Lemma C.4.3.12 implies that $\Phi_G$ is sequentially continuous. By [NB, Thm.13.2.7(a)], which applies to $X = Y = E$ since $E$ is bornological, then $\Phi_G$ is continuous (since a sequentially continuous linear map $f : X \to Y$ is, in the terminology of [NB, Ch.6,§6.4,p.163], locally bounded, i.e. it maps bounded subsets to bounded subsets, by [NB, Thm.6.1.4(a)], and hence [NB, Thm.13.2.7(a)] applies. We further refer the reader to Remark C.4.3.4, noting that convergent sequences are bounded in any topological $\mathbf{C}$-vector space, while Cauchy nets may not be).

(2) : Since $\mathrm{H}^0(G,E)$ is the intersection of the linear subspaces $\ker(\mathrm{Id}_E - \rho_G(g,\cdot))$ as $g$ varies over $G$, each of which is closed, it is itself a closed subspace of $E$.

We have, for every $u \in E$ and every continuous functional $\varphi \in E'$:

$$
\langle\rho_G(g,\Phi_G(u)),\varphi\rangle_{E,E'} = \langle\Phi_G(u),\rho'_G(g,\varphi)\rangle_{E,E'} \tag{4.3.3.3}
$$

where $\rho'_G$ is the adjoint action on the continuous dual $E'$ of $E$. We have, from (4.3.3.3):

$$
\langle\Phi_G(u),\rho'_G(g,\varphi)\rangle_{E,E'} = \int_G \langle\rho_G(g',u),\rho'_G(g,\varphi)\rangle_{E,E'}\,\mathrm{d}\mu_G(g') = \int_G \langle\rho_G(g,\rho_G(g',u)),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g') \tag{4.3.3.4}
$$

By $G$-invariance of the Haar measure $\mu_G$, the righmost side of (4.3.3.4) reads:

$$
\int_G \langle\rho_G(g'',u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g'') = \langle\Phi_G(u),\varphi\rangle_{E,E'}.
$$

We deduce that $\Phi_G$ is valued in the closed subspace $\mathrm{H}^0(G,E)$. To see that it surjects onto it, we observe that we have, for any $u \in \mathrm{H}^0(G,E)$, for every $\varphi \in E'$:

$$
\Phi_G(u)(\varphi) = \int_G \langle\rho_G(g,u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g) = \mu_G(G)\langle u,\varphi\rangle_{E,E'} \tag{4.3.3.5}
$$

which reads $\Phi_G(u) = \mu_G(G)u$, and hence $u$ is in the image of $\Phi_G$.

$N_G$ therefore admits a continuous right-inverse, given by the composition of the linear topological embedding with closed range $\mathrm{H}^0(G,E) \subset E$, followed by multiplication by $1/\mu_G(G)$, and by the quotient $E \to E/\ker(\Phi_G)$. By [Bou-GT, Ch.I,§3.5,Prop.9,p.41], $\Phi_G$ is open, and hence a linear topological isomorphism, since it is a continuous linear bijection.

(3) : The kernel of $\Phi_G$ is annihilated by all continuous linear functionals on $E$ invariant under the adjoint action of $G$ on $E'$, since $N_G$ surjects onto $\mathrm{H}^0(G,E)$, and these are the only continuous functionals on $E$ with this property. Indeed, let $\varphi \in E'$ be such that $\langle u,\varphi\rangle_{E,E'} = 0$ for all $u \in \ker(\Phi_G)$. Then $\varphi$ is in the image of the linear inclusion $\mathrm{H}_{0,\mathrm{cont}}(G,E)' \to E'$ by (2) and [NB, Thm.8.12.1(a)].

We have, for every $u \in E$:

$$
\langle\Phi_G(u),\varphi\rangle_{E,E'} = \langle u,\varphi\rangle_{E,E'}
$$

since we may write $u = \Phi_G(u) + u_0$ for some $u_0 \in \ker(\Phi_G)$, being, by (4.3.3.5), the continuous linear endomorphism $\mu_G(G)^{-1}\Phi_G$ of $E$, idempotent, and hence with linearly and topologically complemented range and kernel.

This identifies the image of the linear inclusion $\mathrm{H}_{0,\mathrm{cont}}(G,E)' \to E'$ with the linear subspace of $E'$ of those continuous functionals that are in the range of the continuous adjoint $\Phi'_G$.

A continuous functional $\varphi \in E'$ is in the image of $\Phi'_G$ if and only if for every $u \in E$, we have:

$$
\langle u,\varphi\rangle_{E,E'} = \langle\Phi_G(u),\varphi\rangle_{E,E'}
$$

which implies:

$$
\langle\rho_G(g,u),\varphi\rangle_{E,E'} = \langle\Phi_G(\rho_G(g,u)),\varphi\rangle_{E,E'} = \langle\Phi_G(u),\varphi\rangle_{E,E'} = \langle u,\varphi\rangle_{E,E'}
$$

which reads:

$$
\langle u,\rho'_G(g,\varphi)\rangle_{E,E'} = \langle u,\varphi\rangle_{E,E'}
$$

## PDF page 183

**4.3. PREPARATIONS ON ISOTYPIC PROJECTORS** · **183**

for every $u \in E$, and hence $\varphi$ is invariant under the adjoint action $\rho'_G$, since $E$ separates the points of $E'$. Conversely, if $\varphi \in E'$ is invariant under the adjoint $G$-action, then we have, for every $u \in \ker(\Phi_G)$:

$$
\langle u,\rho'_G(g,\varphi)\rangle_{E,E'} = \langle\rho_G(g,u),\varphi\rangle_{E,E'}
$$

for every $g \in G$, and upon integrating over $G$ we obtain:

$$
\Phi_G(u)(\varphi) = \int_G \langle\rho_G(g,u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g) = 0 \tag{4.3.3.6}
$$

since $u \in \ker(\Phi_G)$. By $G$-invariance of $\varphi$, (4.3.3.6) reads:

$$
\mu_G(G)\langle u,\varphi\rangle_{E,E'} = 0 \tag{4.3.3.7}
$$

and hence $\langle u,\varphi\rangle_{E,E'} = 0$ for all $u \in \ker(\Phi_G)$. This shows that the orthogonal $\ker(\Phi_G)^\perp$ with respect to the duality $\langle E,E'\rangle$ is the closed linear subspace of $E'$ of all continuous functionals on $E$ invariant under the adjoint $G$-action, which we shall denote by $\mathrm{H}^0(G,E')$.

We now note that the subspace $V_E$ also satisfies $V_E^\perp = \mathrm{H}^0(G,E')$. Indeed, let $\varphi \in E'$ be such that $\langle\varphi,u - \rho_G(g,u)\rangle_{E,E'} = 0$ for all $(g,u) \in G \times E$. This is equivalent to the vanishing condition:

$$
\langle u,\varphi - \rho'_G(g,\varphi)\rangle_{E,E'} = 0
$$

for all $(g,u) \in G \times E$, where $\rho'_G$ is the adjoint action of $G$ on $E'$. Since $E$ separates the points of $E'$, we deduce that we have $\varphi - \rho'_G(g,\varphi) = 0$ for all $g \in G$, which is equivalent to the condition $\varphi \in \mathrm{H}^0(G,E')$.

By [NB, Thm.8.9.2], it follows that the $\sigma(E,E')$-closure of $V_E$ is the $\sigma(E,E')$-closure of $\ker(\Phi_G)$. We now use [Jar, Part II,Ch.8,§8.2,Prop.5,p.149], to deduce that the weak closure of $V_E$, respectively of $\ker(\Phi_G)$, agree with their closures with respect to the initial topology on $E$. $\square$

We record here for later use, a consequence of Lemma 4.3.3.1:

Corollary 4.3.3.3 (Isotypes of the continuous action of a compact Hausdorff abelian group). *Let $G$ be a compact Hausdorff abelian group, $E$ a Hausdorff locally convex topological $\mathbf{C}$-vector space equipped with a continuous $\mathbf{C}$-linear action $\rho_G$ of $G$ by linear topological automorphisms. Let $\mu_G$ be a choice of Haar measure on $G$. Assume that $E$ is quasi-complete and bornological, and that $\rho_G$ is sequentially uniformly continuous. Let $\omega \in \widehat{G}$ be a continuous character.*

Then:
(1) the $\mathbf{C}$-linear form on $E'$:

$$
\Phi_{G,\omega}(u) : \varphi \mapsto \int_G \langle\overline{\omega}(g)\rho_G(g,u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g) \tag{4.3.3.8}
$$

*defines a linear operator $\Phi_{G,\omega} : E \to (E')^{\ast}$ which factors uniquely through $\iota_E : E \to (E')^{\ast}$, and the resulting unique linear operator $\Phi_{G,\omega} : E \to E$ is continuous.*

(2) *$\Phi_{G,\omega}$ surjects onto the closed subspace $\mathrm{H}^0(\omega,E)$ of $\omega$-homogeneous elements, i.e. $\mathrm{H}^0(\omega,E) := \{u \in E : \rho_G(g,u) = \omega(g)u\}$, and $\mu_G(G)^{-1}\Phi_{G,\omega}$ is idempotent.*

*Upon denoting by $\mathrm{H}_{0,\mathrm{cont}}(\omega,E)$ the quotient of $E$ by $\ker(\Phi_{G,\omega})$, then $\Phi_{G,\omega}$ factors through a linear topological isomorphism:*

$$
N_{G,\omega} : \mathrm{H}_{0,\mathrm{cont}}(\omega,E) \to \mathrm{H}^0(\omega,E) \tag{4.3.3.9}
$$

*with respect to the quotient topology on the source and the subspace topology on the target.*

(3) *The closed subspace $\ker(\Phi_{G,\omega}) \subset E$ is the closure of the $\mathbf{C}$-linear subspace $V_{E,\omega}$ generated by the elements $\{u - \overline{\omega}(g)\rho_G(g,u),\ g \in G\}$ as $u$ varies over $E$.*

## PDF page 184

**184** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

Terminology 4.3.3.2 (Locally convex isotypes). Let $G$ be a compact Hausdorff abelian group, $E$ a Hausdorff locally convex topological $\mathbf{C}$-vector space equipped with a continuous $\mathbf{C}$-linear action $\rho_G$ of $G$ on $E$ by linear topological automorphisms.

Assume $(\rho_G,E)$ satisfy either of the assumptions (a) and (b) of Corollary 4.3.3.3.

Let $\omega \in \widehat{G}$ be a continuous character.

We refer to both $\mathrm{H}_{0,\mathrm{cont}}(\omega,E)$ and $\mathrm{H}^0(\omega,E)$ as the $\omega$-isotype of $E$. As the need arises, we will refer to the former, equipped with the quotient topology, as the space of continuous $\omega$-co-invariants of $E$, and to the latter, equipped with the subspace topology, as the space of $\omega$-homogeneous elements of $E$.

Proof of Corollary 4.3.3.3. We define the continuous $\mathbf{C}$-linear action $\eta_{G,\omega} := \overline{\omega}\rho_G$ of $G$ on $E$, i.e. for every $g \in G$ and $u \in E$, $\eta_{G,\omega}(g,u) := \overline{\omega}(g)\rho_G(g,u)$.

Since $\omega$, and hence $\overline{\omega} = \omega^{-1}$, is a continuous character of the compact Hausdorff abelian group $G$, then $\eta_{G,\omega}$ is a continuous $\mathbf{C}$-linear action of $G$ on $E$, since $\rho_G$ is. For each $g \in G$, $\eta_{G,\omega}(g,\cdot)$ is a linear topological automorphism whose continuous inverse is $\eta_{G,\omega}(g^{-1},\cdot)$.

(1), (2) and (3) follow from (1), (2) and (3) of Lemma 4.3.3.1 applied to $\eta_{G,\omega}$ in place of $\rho_G$ of the Lemma, upon observing the following on the continuous action $\eta_{G,\omega}$ of $G$ on $E$.

Since $\rho_G$ is assumed to be sequentially uniformly continuous, and since the image of $\omega$, and hence of $\overline{\omega}$, is the unit circle in the complex plane, then, by absolute homogeneity of any continuous seminorm on $E$, $\eta_{G,\omega}$ is also uniformly sequentially continuous. Indeed, for any continuous seminorm $p$ on $E$, and any $u \in E$, and for any sequence $\{u_m\}_{m\ge 0} \subset E$ converging to $u$ in $E$, we have

$$
\sup_{g\in G} p(\eta_{G,\omega}(g,u_m-u)) = \sup_{g\in G} |\overline{\omega}(g)|p(\rho_G(g,u_m-u)) = \sup_{g\in G} p(\rho_G(g,u_m-u)) \to 0.
$$

Since $E$ is bornological, (1.b) of Lemma 4.3.3.1 applies.

We then observe that if $G$ acts on $E$ through $\eta_{G,\omega}$, then the resulting $\mathrm{H}^0(G,E)$ is the closed subspace of those elements $u \in E$ satisfying, for every $g \in G$:

$$
u = \eta_{G,\omega}(g,u)
$$

which reads $u = \overline{\omega}(g)\rho_G(g,u)$, equivalently $\rho_G(g,u) = \omega(g)u$. $\mu_G(G)^{-1}\Phi_{G,\omega}$ is idempotent by the same assertion from Lemma 4.3.3.1(2), applied to $\eta_{G,\omega}$ in place of $\rho_G$.

These observations having been made, Lemma 4.3.3.1 implies all the assertions of the Corollary. $\square$

4.3.3.1. *Hilbertian and locally convex isotypic projectors.* We now show how to recover the orthogonal projectors $\Pi_{G,\omega}$ from (4.3.2.1) and Lemma 4.3.2.2, using Lemma 4.3.3.1 and Corollary 4.3.3.3.

Corollary 4.3.3.4 (Hilbertian and locally convex isotypic projectors). *Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group, with module $|\cdot|_G$ and compact Hausdorff closed subgroup of module-1 elements $G^1$. Let $R(G)$ be the Hilbert space $L^2(G,\nu)$, for $\mu_G$ a choice of Haar measure on $G$. Let $\nu_1$ be a choice of Haar measure on $G^1$.*

*Then, as continuous $\mathbf{C}$-linear endomorphisms of $R(G)$, we have:*

$$
\Pi_{G^1,\omega} = \Phi_{G^1,\omega} \tag{4.3.3.10}
$$

*where $\Pi_{G^1,\omega}$ is the continuous linear endomorphism of $R(G)$ defined in (4.3.2.1), and $\Phi_{G^1,\omega}$ is the continuous linear endomorphism of $R(G)$ defined in (4.3.3.17).*

*Moreover, $\nu_1(G^1)^{-1}\Pi_{G^1,\omega}$, equivalently $\nu_1(G^1)^{-1}\Phi_{G^1,\omega}$, are orthogonal projectors, whose ranges are, for distinct continuous characters $\omega$ of $G^1$, mutually orthogonal.*

## PDF page 185

**4.3. PREPARATIONS ON ISOTYPIC PROJECTORS** · **185**

Proof. We note that the Hilbert space $E := R(G)$ is complete, hence quasi-complete. All metrizable Hausdorff locally convex topological $\mathbf{C}$-vector spaces are bornological (see [NB, Example 13.2.8(b)]), and by (4.3.2.5), $\Pi_{G^1,\omega}$ is a continuous linear operator.

The continuous left-translation action of $G$ on $E$ is unitary (see Lemma 4.3.1.5(2)) and hence uniformly continuous. Its restriction to the compact Hausdorff abelian subgroup $G^1$, therefore also is.

Lemma 4.3.3.1 therefore applies, and gives $\Phi_{G^1,\omega}$ through its Corollary 4.3.3.3.

The composition $\iota_E \circ \Pi_{G^1,\omega}$ agrees with $\iota_E \circ \Phi_{G^1,\omega}$ by the Riesz Representation Theorem (see [Fol, Ch.6,§6.2,Thm.6.15,p.190]). Since $\nu_1(G^1)^{-1}\Phi_{G^1,\omega}$ is idempotent by Corollary 4.3.3.3(2), it is an orthogonal projector by [Cnw-a, Ch.II,§3,Prop.3.3(f)], so long as we show that it is a positive operator. The linear direct sum $\bigotimes_{\omega'\in\widehat{G^1}} \mathrm{H}^0(\omega',E)$ of mutually orthogonal closed subspaces of $E$, is dense in $E$ by the Peter-Weyl Theorem (see [Kn, Thm.1.12]). By continuity of the Hermitian inner product on $E$, and continuity of $\Phi_{G,\omega}$, it is enough to check that $\Phi_{G,\omega}$ is positive on $\mathrm{H}^0(\omega,E)$ (i.e. for $\omega' = \omega$, since $\Phi_{G,\omega}$ annihilates $\mathrm{H}^0(\omega',E)$ for every continuous character $\omega'$ of $G^1$ such that $\omega' \ne \omega$). $\Phi_{G,\omega}$ is positive on $\mathrm{H}^0(\omega,E)$ since it acts as multiplication by $\nu_1(G^1)$. $\square$

Corollary 4.3.3.4 provides an alternative take on Lemma 4.3.2.2, noting that a form of the Peter-Weyl Theorem is used in the proof of both, respectively, to infer than the linear subspace linearly generated by the matrix coefficients is dense.

Example 4.3.3.5 (Finite dimensional representations of compact abelian groups). Let $G$ be a second-countable compact abelian group, and $E$ a finite dimensional $\mathbf{C}$-vector space, equipped with the Euclidean topology, i.e. the unique, up to equivalence, linear topology promoting $E$ to a Hausdorff locally convex topological $\mathbf{C}$-vector space.

Let $\rho_G : G \times E \to E$ be a continuous $\mathbf{C}$-linear action of $G$ by linear topological automorphisms, equivalently linear automorphisms.

There exists a compact subgroup $k \subset G$ with finitely generated orthogonal $k^\perp \subset \widehat{G}$, such that $\rho_G$ restricts to $k$ to the trivial action of $k$ on $E$, i.e. $\rho_G$ factors trough $G/k$, which is a compact abelian Lie group, and the resulting action of $G/k$ is faithful, i.e. $\rho_G$ induces an injective continuous homomorphism $\rho : G/k \to \mathrm{GL}(E)$. Indeed, the kernel $k$ of the continuous homomorphism $\rho : G \to \mathrm{GL}(E)$ qualifies, since $\mathrm{GL}(E)$ is itself a Lie group, and hence so is the image of $\rho(G)$ since a closed subgroup of a Lie group is an embedded Lie subgroup, since $\rho(G)$ is compact, hence closed in $\mathrm{GL}(E)$.

We may replace $G$ with $G/k$ and rename $G/k$ as $G$.

Then $G$ is a compact abelian Lie group, and it acts faithfully and semisimply on $E$. We choose a Haar measure $\mu_G$ on $G$.

The operators $\mu_G(G)^{-1}\Phi_{G,\omega}$, as $\omega$ varies over the continuous characters of $G$, are the projectors onto the $\omega$-isotypic component $E(\omega)$ of $E$. Since $E$ is finite dimensional, only finitely many continuous characters $\omega \in \widehat{G}$ exist such that $E(\omega) \ne 0$.

Example 4.3.3.6 (Finite dimensional representations of finite groups). Let $G$ be a finite group. Then upon choosing $\mu_G$ to be any Haar measure on $G$, there exists a unique positive real number $r > 0$ such that $\mu_G$ is $r\nu_G$, for $\nu_G$ the counting measure on $G$ (see [DE, Prop.1.4.4(c)]).

Let $E := \mathbf{C}[G]$, the finite dimensional regular representation of $G$, equipped with the Euclidean topology. The linear operator $\mu_G(G)^{-1}\Phi_{G,\omega}$ does not depend on the choice of Haar measure $\mu_G$, and we may therefore assume $r = 1$. The linear operator $\mu_G(G)^{-1}\Phi_{G,\omega}$ is, therefore, the isotypic projector $u \mapsto \frac{1}{\lvert G\rvert}\sum_{g\in G} \overline{\omega}(g)g.v$ where $g.v$ is the effect of the action of $G$ on $\mathbf{C}[G]$ by left-translation on itself.

4.3.3.2. *Averaging over relatively compact locally closed subsets of a Hausdorff locally compact abelian group.* We conclude this subsection by recording here below and integrability and continuity criterion for the

## PDF page 186

**186** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

vector-valued continuous functions obtained from the action of a Hausdorff locally compact abelian group $G$, acting continuously on a quasi-complete Hausdorff locally convex topological $\mathbf{C}$-vector space $E$, restricted to the compact subsets of $G$.

Lemma 4.3.3.7 (Integrability and continuity of actions of relatively compact subsets). *Let $G$ be a Hausdorff locally compact abelian group, $X \subset G$ a relatively compact locally closed subset with non-empty interior. Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, equipped with a continuous $\mathbf{C}$-linear action $\rho_G$ by linear topological automorphisms. Let $\mu_G$ be a choice of Haar measure on $G$.*

*Assume $E$ is quasi-complete, and that either of the following two conditions on $\rho_G$ and $E$ is satisfied:
(a) the action $\rho_G$ is continuous, uniformly on the compact subsets of $G$, i.e. for every $u \in E$ and for every net $\{u_i\}_{i\in I} \subset E$ converging to $u$, we have, for every compact subset $K \subset G$, $\rho_G(g,u_i) \to \rho_G(g,u)$ uniformly as $g \in K$.
(b) $E$ is bornological, and condition (a) is satisfied for every $u \in E$ and for every sequence $\{u_m\}_{m\ge 0} \subset E$ converging to $u \in E$.*

*Then:
(1) For every $u \in E$, the $\mathbf{C}$-linear form on $E'$:*

$$
\Phi_X(u) : \varphi \mapsto \int_X \langle\rho_G(g,u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g) \tag{4.3.3.11}
$$

*is in the image of the canonical continuous linear operator $\iota_E : E \to (E')^{\ast}$, i.e. $\Phi_X(u)$ is the evaluation functional on $E'$ on a unique element of $E$. Equivalently, the linear operator $\Phi_X : E \to (E')^{\ast}$ assigned by $u \mapsto \Phi_X(u)$, factors through $\iota_E$.*

*Its formation is continuous with respect to the intrinsic topology on $E$, i.e. $\Phi_X : E \to E$ is a continuous linear operator.*

(2) *$\Phi_X$ surjects onto the closed subspace $\mathrm{H}^0(X,E)$ of elements $u$ of $E$ satisfying the equations $\rho_G(g,u) = u$ for all $g \in X$, and $\mu_G(X)^{-1}\Phi_X$ is idempotent.*

(3) *The $\sigma(E,E')$-closure of the closed subspace $\ker(\Phi_X) \subset E$ is the $\sigma(E,E')$-closure of the $\mathbf{C}$-linear subspace $V_E$ generated by the elements $\{u - \rho_G(g,u),\ u \in E,\ g \in X\}$ as $u$ varies over $E$.*

Proof. (1) : By Theorem C.4.3.5, applied to $X$, $\mu = \mu_G|_X$ (the restriction of the Radon measure $\mu_G$ to $X$, itself a nonzero Radon measure, since $X$ is relatively compact and its interior is non-empty; see [Bou-I, Ch.III,§2,No.1,INT III.23] for the case $X$ is open, and [Bou-I, Ch IV,§5,No.7,Def.4,INT IV.74] for the general case $X$ is a locally compact subspace of $G$. In particular, if $X$ is locally closed), $f : X \to E$ defined as $f(g) := \rho_G(g,u)$ for each $u \in E$ fixed, we deduce that $f$ is $\mu$-integrable in the sense of Pettis, which implies that $\Phi_X(u)$, a priori only an element of $(E')^{\ast}$, is contained in $\iota_E(E)$. In particular, the assignment $u \mapsto \Phi_X(u)$ is $\iota_E(E)$-valued and linear, and hence it factors through $\iota_E$ as a $\mathbf{C}$-linear operator on $E \to (E')^{\ast}$. We denote by $\Phi_X$ the resulting unique linear operator $\Phi_X : E \to E$ such that its composition with $\iota_E$ is $\Phi_X : E \to (E')^{\ast}$.

By Lemma C.4.3.12, $\Phi_X : E \to E$ is continuous with respect to the intrinsic topology on $E$, if condition (a) is satisfied.

If condition (b) is satisfied, instead, then we proceed as in the proof of (1) from Lemma 4.3.3.1: by Lemma C.4.3.12, $\Phi_X$ is sequentially continuous. By [NB, Thm.13.2.7(a)], which applies to $X = Y = E$ (notation as in loc.cit.) since $E$ is bornological, then $\Phi_X$ is continuous.

(2) : Since $\mathrm{H}^0(X,E)$ is the intersection of the linear subspaces $\ker(\mathrm{Id}_E - \rho_G(g,\cdot))$ as $g$ varies over $X$, each of which is closed, it is itself a closed subspace of $E$.

We have, for every $u \in E$, for every continuous functional $\varphi \in E'$, and for every $g \in G$:

$$
\langle\rho_G(g,\Phi_X(u)),\varphi\rangle_{E,E'} = \langle\Phi_X(u),\rho'_G(g,\varphi)\rangle_{E,E'} \tag{4.3.3.12}
$$

## PDF page 187

**4.3. PREPARATIONS ON ISOTYPIC PROJECTORS** · **187**

where $\rho'_G$ is the adjoint action on the continuous dual $E'$ of $E$. We have, from (4.3.3.12):

$$
\langle\Phi_X(u),\rho'_G(g,\varphi)\rangle_{E,E'} = \int_X \langle\rho_G(g',u),\rho'_G(g,\varphi)\rangle_{E,E'}\,\mathrm{d}\mu_G(g') = \int_X \langle\rho_G(g,\rho_G(g',u)),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g'). \tag{4.3.3.13}
$$

By $G$-invariance of the Haar measure $\mu_G$, the righmost side of (4.3.3.13) reads:

$$
\int_X \langle\rho_G(g'',u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g'') = \langle\Phi_X(u),\varphi\rangle_{E,E'}.
$$

We deduce that $\Phi_X$ is valued in the closed subspace $\mathrm{H}^0(X,E)$. To see that it surjects onto it, we proceed as in the proof of (2) of Lemma 4.3.3.1, and we observe that we have, for any $u \in \mathrm{H}^0(X,E)$, for every $\varphi \in E'$:

$$
\Phi_G(u)(\varphi) = \int_X \langle\rho_G(g,u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g) = \mu_G(X)\langle u,\varphi\rangle_{E,E'} \tag{4.3.3.14}
$$

which reads $\Phi_X(u) = \mu_G(X)u$, and hence $u$ is in the image of $\Phi_X$.

(3) : The kernel of $\Phi_X$ is annihilated by all continuous linear functionals on $E$ invariant under the adjoint action of the elements of $G$ contained in $X$, on $E'$. Indeed, let $\varphi \in E'$ be such that $\langle u,\varphi\rangle_{E,E'} = 0$ for all $u \in \ker(\Phi_X)$.

We have, for every $u \in E$:

$$
\langle\Phi_X(u),\varphi\rangle_{E,E'} = \langle u,\varphi\rangle_{E,E'}
$$

since we may write $u = \Phi_X(u) + u_0$ for some $u_0 \in \ker(\Phi_X)$, being, by (4.3.3.14), the continuous linear endomorphism $\mu_G(X)^{-1}\Phi_X$ of $E$, idempotent, and hence with linearly and topologically complemented range and kernel.

A continuous functional $\varphi \in E'$ is in the image of $\Phi'_X$ if and only if for every $u \in E$, we have:

$$
\langle u,\varphi\rangle_{E,E'} = \langle\Phi_X(u),\varphi\rangle_{E,E'}
$$

which implies, for every $g \in X$:

$$
\langle\rho_G(g,u),\varphi\rangle_{E,E'} = \langle\Phi_X(\rho_G(g,u)),\varphi\rangle_{E,E'} = \langle\Phi_X(u),\varphi\rangle_{E,E'} = \langle u,\varphi\rangle_{E,E'}
$$

which reads:

$$
\langle u,\rho'_G(g,\varphi)\rangle_{E,E'} = \langle u,\varphi\rangle_{E,E'}
$$

for every $u \in E$, and hence $\varphi$ is invariant under the adjoint action $\rho'_G$ of every element of $G$ contained in $X$, since $E$ separates the points of $E'$. Conversely, if $\varphi \in E'$ is invariant under the adjoint $G$-action of the elements of $X$, then we have, for every $u \in \ker(\Phi_X)$:

$$
\langle u,\varphi\rangle_{E,E'} = \langle u,\rho'_G(g,\varphi)\rangle_{E,E'} = \langle\rho_G(g,u),\varphi\rangle_{E,E'}
$$

for every $g \in X$, and upon integrating over $X$ we obtain:

$$
\mu_G(X)\langle u,\varphi\rangle_{E,E'} = \Phi_X(u)(\varphi) = \int_X \langle\rho_G(g,u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g) = 0 \tag{4.3.3.15}
$$

since $u \in \ker(\Phi_X)$, which further reads:

$$
\mu_G(X)\langle u,\varphi\rangle_{E,E'} = 0 \tag{4.3.3.16}
$$

and hence $\langle u,\varphi\rangle_{E,E'} = 0$ for all $u \in \ker(\Phi_X)$. This shows that the orthogonal $\ker(\Phi_X)^\perp$ with respect to the duality $\langle E,E'\rangle$ is the closed linear subspace of $E'$ of all continuous functionals on $E$ invariant under the adjoint $G$-action of the elements of $X$, which we shall denote by $\mathrm{H}^0(X,E')$.

We now note that the subspace $V_E$ also satisfies $V_E^\perp = \mathrm{H}^0(X,E')$. Indeed, let $\varphi \in E'$ be such that $\langle u - \rho_G(g,u),\varphi\rangle_{E,E'} = 0$ for all $(g,u) \in X \times E$. This is equivalent to the vanishing condition:

$$
\langle u,\varphi - \rho'_G(g,\varphi)\rangle_{E,E'} = 0
$$

## PDF page 188

**188** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

for all $(g,u) \in X \times E$, where $\rho'_G$ is the adjoint action of $G$ on $E'$. Since $E$ separates the points of $E'$, we deduce that we have $\varphi - \rho'_G(g,\varphi) = 0$ for all $g \in X$, which is equivalent to the condition $\varphi \in \mathrm{H}^0(X,E')$.

By [NB, Thm.8.9.2], it follows that the $\sigma(E,E')$-closure of $V_E$ is the $\sigma(E,E')$-closure of $\ker(\Phi_X)$. $\square$

The following Corollary is in analogy with Corollary 4.3.3.3:

Corollary 4.3.3.8 (Isotypes of the continuous action of a relatively compact subset). *Let $G$ be a Hausdorff locally compact abelian group, $E$ a Hausdorff locally convex topological $\mathbf{C}$-vector space equipped with a continuous $\mathbf{C}$-linear action $\rho_G$ of $G$ by linear topological automorphisms.*

*Let $X \subset G$ be a relatively compact subset with non-empty interior.*

*Let $\mu_G$ be a choice of Haar measure on $G$. Assume that $E$ is quasi-complete and bornological, and that $\rho_G$ is sequentially continuous uniformly on the compact subsets of $G$.*

Let $\omega \in \widehat{G}$ be a continuous character.

Then:
(1) the $\mathbf{C}$-linear form on $E'$:

$$
\Phi_{X,\omega}(u) : \varphi \mapsto \int_X \langle\overline{\omega}(g)\rho_G(g,u),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(g) \tag{4.3.3.17}
$$

*defines a linear operator $\Phi_{X,\omega} : E \to (E')^{\ast}$ which factors uniquely through $\iota_E : E \to (E')^{\ast}$, and the resulting unique linear operator $\Phi_{X,\omega} : E \to E$ is continuous.*

(2) *$\Phi_{X,\omega}$ surjects onto the closed subspace $\mathrm{H}^0(\omega|_X,E)$ of those elements $u \in E$ satisfying the equations $\rho_G(g,u) = \omega(g)u$ for all $g \in X$, and $\mu_G(X)^{-1}\Phi_{X,\omega}$ is idempotent.*

(3) *The $\sigma(E,E')$-closure of the closed subspace $\ker(\Phi_{X,\omega}) \subset E$ is the $\sigma(E,E')$-closure of the $\mathbf{C}$-linear subspace $V_{E,\omega}$ generated by the elements $\{u - \overline{\omega}(g)\rho_G(g,u),\ g \in X\}$ as $u$ varies over $E$.*

Proof. The Corollary follows from the argument from the proof of Corollary 4.3.3.3, resting, in the role of Lemma 4.3.3.1 from therein, on Lemma 4.3.3.7. $\square$

We refer the reader to Proposition D.1.9.2, which proves that for $G$ a second-countable, compact Hausdorff abelian group, the continuous left-translation action of $G$ on $\mathcal{S}(G)$, the Schwartz-Bruhat space of $G$ (for which we refer the reader to §2.1) is uniformly continuous (hence sequentially uniformly continuous). Since $\mathcal{S}(G)$ is bornological, sequential uniform continuity already suffices, and this provides a source of examples of Hausdorff locally convex topological $\mathbf{C}$-vector spaces equipped with continuous $G$-module structures, to which Lemma 4.3.3.1, Lemma 4.3.3.7 and their corollaries, apply.

4.4. Exponential system on monogenic quotients of $\mathbf{R}_{>0}$-modulated groups

The reader may use Lemma 4.2.1.5 and Proposition 4.2.2.7 from the previous section, as guidance through the following more general analogs, which cover the case of an arbitrary $\mathbf{R}_{>0}$-modulated Hausdorff locally compact abelian group $G$ equipped with an element $\gamma \in G$ with $|\gamma|_G > 1$ (therefore) generating a free closed subgroup $\gamma^\mathbf{Z}$.

This generality is needed for the intended applications. The arguments for the respective results below, closely follow those we have just provided for the special case $G = \mathbf{R}_{>0}$, and are, for the most part, only notationally more involved.

4.4.1. Complements on the Mellin transform on $\mathcal{S}_I(G)$. We make a brief interlude on the Mellin transform on the Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}_I(G)$ of $I$-exponentially decaying Schwartz-Bruhat functions on $G$, a Hausdorff locally compact second-countable $\mathbf{R}_{>0}$-modulated abelian group.

In this subsection, we show how to reconcile all of the various instances of the Mellin transform arising throughout this work, comparing them through changes of variables and across linear topological isomorphisms.

## PDF page 189

**4.4. EXPONENTIAL SYSTEM ON MONOGENIC QUOTIENTS OF $\mathbf{R}_{>0}$-MODULATED GROUPS** · **189**

Our main references will be Proposition D.3.2.5, Theorem D.3.3.7 and Theorem D.3.3.13.
We let $G$ be an $\mathbf{R}_{>0}$-modulated group.
Recall from Definition D.2.1.1 and the subsequent discussion, that this amounts to the datum of a Hausdorff locally compact abelian group $G$, equipped with a module, i.e. a continuous homomorphism:

$$
\lvert\cdot\rvert_G\colon G\to\mathbf{R}_{>0}
$$

that is assumed to be proper (hence the closed subgroup $G^1:=\ker(\lvert\cdot\rvert_G)$ is compact Hausdorff) and surjective (hence the nomenclature $\mathbf{R}_{>0}$-modulated).
We defined in Definition D.3.3.1, the Hausdorff locally compact topological $\mathbf{C}$-vector space $\mathcal{S}_I(G)$ of $I$-exponentially decaying Schwartz-Bruhat functions o $G$, with $I\subset\mathbf{R}$ a non-empty connected interval of the real line.
Recall that this is the linear subspace of the $\mathbf{C}$-vector space of all continuous functions $\phi$ on $G$, such that $\lvert\cdot\rvert_G^a\phi\in\mathcal{S}(G)$ for every $a\in I$. The topology on $\mathcal{S}_I(G)$ is the projective topology induced by the linear operators $T_a\colon\mathcal{S}_I(G)\to\mathcal{S}(G)$, defined as $T_a(\phi):=\lvert\cdot\rvert_G^a\phi$ and by the Hausdorff locally convex topology on $\mathcal{S}(G)$.
We choose a continuous homomorphic section $\tau$ to the module $\lvert\cdot\rvert_G$ (whose existence is proved in Remark D.2.1.2), we assume $G$ is second-countable, and we choose a Haar measure $\mu_1$ on $G$ such that $\mu$ is the push-forward, under the isomorphism of Hausdorff locally compact abelian groups $\mathbf{R}_{>0}\times G^1\to G$ induced by the choice of $\tau$, of the Radon product $\frac{\mathrm{d}t}{t}\otimes\mu_1$.
We now refer the reader to Theorem D.3.3.7, where it is shown that $\mathcal{S}_I(G)$ is, thus topologized, a nuclear strict LF-space, linearly and topologically isomorphic to

$$
\mathcal{S}_I(\mathbf{R}_{>0})\bar\otimes\mathcal{S}(G^1)
$$

where the tensor product is inductive (see the discussion following (C.2.3.22)).
In other words, to understand $\mathcal{S}_I(G)$, it is enough to understand the case $G=\mathbf{R}_{>0}$ (which is studied in §B.2.1, §D.3.2 through the lens of the Mellin transform, and Lemma D.3.2.3), and the Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}(G^1)$ of Schwartz-Bruhat functions on a compact Hausdorff abelian group, together with the inductive topology on tensor products (for which we refer the reader to the discussion following (C.2.3.22), and to Proposition C.2.3.13 for basic permanence properties. We further refer the reader to [Gro-b, Ch.II,§3,no.1,p.73] in Grothendieck's AMS memoir).
Much as in the special case $G=\mathbf{R}_{>0}$ and $I$ open, where the Mellin transform on $\mathcal{S}_I(\mathbf{R}_{>0})$ is defined by $M(\phi)(s):=\int_{\mathbf{R}_{>0}}\phi(t)t^s\frac{\mathrm{d}t}{t}$, and valued in $A\mathcal{S}(\mathbf{C}_I)$, where $\mathbf{C}_I$ is the open non-empty connected vertical strip within the complex $s$-plane $\mathbf{C}$, whose intersection with the real line is the base interval of abscissas $I$, the Mellin transform is defined on $\mathcal{S}_I(G)$ too, by the following assignment:

$$
M(\phi)(c):=\int_G\phi(g)c(g)\,\mathrm{d}\mu(g) \tag{4.4.1.1}
$$

for $\mu$ a choice of Haar measure on $G$ (which can be selected to be canonical, as per Definition D.2.1.1(2); see also Remark D.2.1.3. We will not be making this assumption: we will be allowing $G^1$ to have nonzero volume different than $1$).
The Mellin transform is a function of continuous quasi-characters $c$ of $G$, the set of which can be given the structure of a Riemann surface $\Omega(G)$, fibred over the discrete set $\widehat{G^1}$. We will be assuming $G$ is second-countable, in which case $\widehat{G^1}$ is a countable discrete set.
If $\phi\in\mathcal{S}_I(G)$, for $I\subset\mathbf{R}$ an open connected interval, then $M(\phi)$ is holomorphic over the relative vertical strip $\Omega(G)_I:=\{c\in\Omega(G):\sigma(c)\in I\}$, where $\sigma(c)$ is the unique real number such that $c=\chi\lvert\cdot\rvert_G^{\sigma(c)+it}$, for some $t\in\mathbf{R}$, and for a choice of continuous character $\chi\in\widehat{G}$ such that $\chi|_{G^1}=c|_{G^1}$.

## PDF page 190

**190** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

By Theorem D.3.3.13, the Mellin transform induces a linear topological isomorphism:

$$
M\colon\mathcal{S}_I(G)\to A\mathcal{S}(\mathbf{C}_I)\overline{\otimes}\mathcal{S}(G^1) \tag{4.4.1.2}
$$

obtained by composing the linear topological isomorphism $\mathcal{S}_I(G)\to\mathcal{S}_I(\mathbf{R}_{>0})\bar\otimes\mathcal{S}(G^1)$ induced by a choice of continuous homomorphic section $\tau$ to the module $\lvert\cdot\rvert_G$ (whose existence is discussed in Remark D.2.1.2), with $M\,\overline{\otimes}\,\check{\mathcal{F}}_{\mathcal G}$, where $\check{\mathcal{F}}_{\mathcal G}$ is the composition of the Fourier transform on $\mathcal{S}(G^1)$ composed by inversion (because the Fourier transform is defined as $\mathcal{F}_{G^1}(\psi)(\chi)=\int_{G^1}\psi(g)\bar\chi(g)\,\mathrm{d}\mu_1(g)$, therefore necessitating inversion to restore the variation with respect to $\chi$ as opposed to $\bar\chi$).
Explicitly, we have, for $(t,g)\in\mathbf{R}_{>0}\times G^1$:

$$
M(\phi)(c(\tau(t)g))=\int_{\mathbf{R}_{>0}}c(\tau(t))\int_{G^1}\phi(\tau(\cdot)g)c(g)\,\mathrm{d}\mu_1(g)\frac{\mathrm{d}t}{t}=M_{\mathbf{R}_{>0}}(\mathcal{F}_{G^1}(\phi(\tau(t)g))(\bar c|_{G^1}))(c\circ\tau)
$$

where $M_{\mathbf{R}_{>0}}$ denotes the Mellin transform on $\mathcal{S}_I(\mathbf{R}_{>0})$, and where $\mathcal{F}_{G^1}$ denotes the Fourier transform on $\mathcal{S}(G^1)$, the element $\phi(\tau(t)g)$ being viewed as a function of $g\in G^1$ for each $t\in\mathbf{R}_{>0}$.
In the special case $\phi=\psi\otimes\phi_0$, with $\psi\in\mathcal{S}_I(\mathbf{R}_{>0})$ and $\phi_0\in\mathcal{S}(G^1)$, then we indeed obtain

$$
M(\phi)(c)=M_{\mathbf{R}_{>0}}(\psi)(c\circ\tau)\mathcal{F}_{G^1}(\phi_0)(\bar c|_{G^1}).
$$

We let $\gamma\in G$ be an element such that $\lvert\gamma\rvert_G>1$, and discuss an interlude on the action of the closed subgroup $\gamma^{\mathbf{Z}}\subset G$ on $\mathcal{S}_I(G)(\chi|_{G^1})$, for $\chi\in\widehat{G}$ a continuous character, seen through the lens of the Mellin transform $M\colon\mathcal{S}_I(G)(\chi|_{G^1})\to A\mathcal{S}(\mathbf{C})$ from Proposition D.3.2.5 and Theorem D.3.3.13 (applied to $I=\mathbf{R}$).

Discussion 4.4.1.1 (On the Mellin transform on $\mathcal{S}_I(G)$). We let $I$ be a non-empty open connected interval of the real line.
We let $G$ be an $\mathbf{R}_{>0}$-modulated group, and $\tau$ be a choice of continuous homomorphic section to the module $\lvert\cdot\rvert_G$.
We let $\gamma\in G$ be an element such that $\lvert\gamma\rvert_G>1$. In particular, $\gamma\notin G^1$.
We choose $\mu_1$ any Haar measure on $G^1$, and denote by $\mu$ the Haar measure on $G$ matching under push-forward along the isomorphism of Hausdorff locally compact abelian groups $G\simeq G^1\times\mathbf{R}_{>0}$ induced by the choice of $\tau$, the Radon measure $\mu_1\otimes\frac{\mathrm{d}t}{t}$.
We fix a continuous character $\chi\in\widehat{G}$ and denote by

$$
\Phi_{G,\chi}\colon\mathcal{S}_I(G)\to\mathcal{S}_I(G)(\chi|_{G^1})
$$

the continuous surjective linear operator $u\mapsto\Phi_{G,\chi}(u)(x):=\int_{G^1}\chi(g)u(gx)\,\mathrm{d}\mu_1(g)$, where, recall, $\mathcal{S}_I(G)(\chi|_{G^1})$ is the quotient of $\mathcal{S}_I(G)$ by the kernel of $\Phi_{G,\chi}$, and $\Phi_{G,\chi}$ is continuous surjective and open, making the quotient Hausdorff and complete since so is $\mathcal{S}_I(G)$, and linearly and topologically isomorphic to $\mathrm{H}^0(\chi|_{G^1},\mathcal{S}_I(G))$, the closed subspace of $\mathcal{S}_I(G)$ of the $\chi|_{G^1}$-homogeneous $I$-exponentially decaying Schwartz-Bruhat functions; see Proposition D.3.3.12 (where $\Phi_{G,\chi}$ is linearly and topologically isomorphic, under multiplication by $\mu_1(G^1)$, to $\Phi^I_{G,\omega}$, for $\omega=\chi|_{G^1}$).
We consider the following commutative diagram:

(4.4.1.3)

```latex
\begin{tikzcd}
\mathcal{S}_I(G) \arrow[r, "M(\cdot)(\chi\lvert\cdot\rvert_G^s)"] \arrow[d, "\Phi_{G,\chi}"'] & A\mathcal{S}(\mathbf{C}_I) \arrow[d, "T_{-ix_0}"] \\
\mathcal{S}_I(G)(\chi|_{G^1}) \arrow[r, "M_{\mathbf{R}_{>0}}\circ\tau"'] & A\mathcal{S}(\mathbf{C}_I)
\end{tikzcd}
```

where $M$ is the Mellin transform on $\mathcal{S}_I(G)$, hence assigned by:

$$
M(\phi)(\chi\lvert\cdot\rvert_G^s):=\int_G\phi(g)\chi(g)\lvert g\rvert_G^s\,\mathrm{d}\mu(g). \tag{4.4.1.4}
$$

## PDF page 191

**4.4. EXPONENTIAL SYSTEM ON MONOGENIC QUOTIENTS OF $\mathbf{R}_{>0}$-MODULATED GROUPS** · **191**

Upon defining $x_0\in\mathbf{R}$ to be the unique real number such that $\chi(\tau(t))=t^{ix_0}$ as smooth functions of $t\in\mathbf{R}_{>0}$, the rightmost vertical arrow is the effect of the vertical translation by $-ix_0$, i.e. $T_{-ix_0}\colon s\mapsto s-ix_0$, promoting the diagram in (4.4.1.3) to a commutative diagram of continuous linear operators.
Recall that the bottom horizontal arrow is defined as:

$$
M_{\mathbf{R}_{>0}}(\phi)(s+ix_0)=\int_{\mathbf{R}_{>0}}\phi(t)t^{s+ix_0}\frac{\mathrm{d}t}{t}
$$

and it is the Mellin transform on the $\mathbf{R}_{>0}$-modulated group $\mathbf{R}_{>0}$ itself, evaluated on the $I$-exponentially decaying Schwartz-Bruhat functions obtained as $\phi(t)=\Phi_{G,\chi}(\psi)(\tau(t))$, for $\psi\in\mathcal{S}_I(G)$.
The left-translation action by $\pi:=\gamma^{-1}\in\gamma^{\mathbf{Z}}$ has the following effect on the diagram in (4.4.1.3):

(1) It sends $\phi\in\mathcal{S}_I(G)$ to $\phi(\pi^{-1}x)$ as a function of $x\in G$.
(2) The operator $M$ is compatible with the effect described in (1) on the source, and with the multiplication operator on $A\mathcal{S}(\mathbf{C}_I)$ by $\chi(\pi)q^{-s}$, where $q:=\lvert\pi\rvert_G^{-1}$.
(3) We let $u\in G$ be the element $\tau(q)\pi\in G^1$. Upon calling $\omega\in\widehat{C^1_F}$ the continuous character $\omega:=\chi|_{C^1_F}$, we have that $\Phi$ is compatible with the effect described in (1) on the source, and with the multiplication operator by $\omega(u)$ on the target, composed with the left-translation action by $q^{-1}\in\mathbf{R}_{>0}$ on the function of $t\in\mathbf{R}_{>0}$ given by $\phi(\tau(t))$ for $\phi\in\mathcal{S}_I(G)(\chi|_{G^1})$. In particular, the left-translation action by $\pi^{\mathbf{Z}}=\gamma^{\mathbf{Z}}$ descends to a continuous action on $\mathcal{S}_I(G)(\chi|_{G^1})$: the effect of its generator $\pi$ is the one that has just been described.
(4) The operator $M_{\mathbf{R}_{>0}}\circ\tau$ is compatible with the effect described in (3) of the action of $(q^{-1},u)\in\mathbf{R}_{>0}\times G^1$ (i.e. of $\pi$ through the isomorphism of Hausdorff locally compact abelian groups $G\simeq\mathbf{R}_{>0}\times G^1$ induced by the choice of $\tau$) on the source, and the effect of the multiplication operator by $q^{-s}\omega(u)$ on the target.
(5) The rightmost vertical arrow is compatible with the multiplication operator by $\chi(\pi)q^{-s}$ on the source, and with the multiplication operator by $\omega(u)q^{-s}$ on the target, because

$$
\chi(\pi)q^{-s+ix_0}=\chi(\tau(q)\pi)\chi(\tau(q)^{-1})q^{-s+ix_0}=\omega(u)q^{-s+ix_0-ix_0}=\omega(u)q^{-s}.
$$

We will be denoting by $A\mathcal{S}(\mathbf{C}_I)(\chi)$, respectively $A\mathcal{S}(\mathbf{C}_I)(\omega)$, the top, respectively bottom copy of $A\mathcal{S}(\mathbf{C}_I)$ in the diagram from (4.4.1.3).
We further note that upon denoting by $\mathbf{C}(\omega)$ the 1-dimensional complex representation of $G^1$ through its character $\omega$, then the Mellin transform $M$ is a linear topological isomorphism $\mathcal{S}_I(G)(\omega)\to A\mathcal{S}(\mathbf{C}_I)\widehat{\otimes}_\pi\mathbf{C}(\omega)=A\mathcal{S}(\mathbf{C}_I)(\omega)$, as per Theorem D.3.3.7.

In practice, we will be choosing $\gamma$ such that $\lvert\gamma\rvert_G>1$, of the form $\gamma=\pi^{-1}$, with $\pi$ a global or $S$-local idele, or idele class, corresponding to a choice of uniformizer at a non-Archimedean place of the number field $F$. The $\mathbf{R}_{>0}$-modulated group will either be $C_F$ or $J_{F,S}$, and the module will either be the idelic norm $\lvert\cdot\rvert_F$, or the $S$-idelic norm $\lvert\cdot\rvert_{F,S}$.

4.4.2. The exponential system on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$. Reprising Discussion 4.4.1.1, we now use analogs of the periodization operators $\Phi_\gamma$ on $\mathcal{S}_\mathrm{E}(\mathbf{R}_{>0})$, and absolute Schauder bases on the quotient $\mathcal{S}(G/\gamma^{\mathbf{Z}})$, as opposed to $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, provided by analogs of Lemma 4.2.1.5 and Proposition 4.2.2.7, to exhibit absolute Schauder bases on subquotients of $\mathcal{S}_\mathrm{E}(G)$, analogous to that in (4.2.2.7), for $G$ a second-countable $\mathbf{R}_{>0}$-modulated group (which will be $J_{F,S}$ in the applications) and incorporating the effect of multiplication by a continuous character of $G^1$.

Definition 4.4.2.1 ($\gamma^{\mathbf{Z}}$-periodization operators). Let $G$ be an $\mathbf{R}_{>0}$-modulated Hausdorff locally compact abelian group. Let $\mu_1$ be a Haar measure on $G^1$.
Let $\gamma\in G$ be an element such that $\lvert\gamma\rvert_G>1$. Let $\chi\in\widehat{G}$ be a continuous character.

## PDF page 192

**192** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

We define the operators:

$$
\Phi_\gamma,\,\Phi_{\gamma,\chi}\colon\mathcal{S}_\mathrm{E}(G)\to\mathcal{S}(G/\gamma^{\mathbf{Z}})=C^\infty(G/\gamma^{\mathbf{Z}}) \tag{4.4.2.1}
$$

assigned by:

$$
\Phi_\gamma(\phi)(x):=\sum_{k\in\mathbf{Z}}\phi(\gamma^kx),\,\Phi_{\gamma,\chi}(\phi)(x):=\sum_{k\in\mathbf{Z}}\int_{G^1}\chi(g)\phi(\gamma^kgx)\,\mathrm{d}\mu_1(g) \tag{4.4.2.2}
$$

as a functions of $x\in G$ invariant under $\gamma^{\mathbf{Z}}$, respectively invariant under $\gamma^{\mathbf{Z}}$ and $\chi|_{G^1}$-homogeneous under the continuous left-translation action of $G^1$ on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$.
We refer to the operators $\Phi_\gamma$, respectively $\Phi_{\gamma,\chi}$, as the $\gamma^{\mathbf{Z}}$-periodization operator, respectively the $\chi|_{G^1}$-homogeneous $\gamma^{\mathbf{Z}}$-periodization operator, on $\mathcal{S}_\mathrm{E}(G)$.
Remark 4.4.2.2. In practice, we will be choosing a continuous homomorphic section $\tau$ to the module $\lvert\cdot\rvert_G$, and $\mu$ the unique Haar measure on $G$ determined as per Theorem D.1.2.1 by the choices $\frac{\mathrm{d}t}{t}$ and $\mu_1$ on $\mathbf{R}_{>0}$, respectively $G^1$, and by the isomorphism of Hausdorff locally compact abelian groups $G\simeq\mathbf{R}_{>0}\times G^1$ induced by the choice of $\tau$.
We note that $\Phi_{\gamma,\chi}$ does not depend on the choice of $\tau$, but only on the choice of Haar measure $\mu_1$ on $G^1$, which amounts to choosing the volume of $G^1$, since $\lvert\cdot\rvert_G$ is proper.

We will be adopting the assumptions and notation from the following:
Situation 4.4.2.3. Let $G$ be an $\mathbf{R}_{>0}$-modulated group. Assume $G$ is second-countable.
(1) Let $\tau$ be a choice of continuous homomorphic section to the module $\lvert\cdot\rvert_G$.
(2) Let $\mu_1$ be a choice of Haar measure on $G^1$, and $\mu$ the unique Haar measure on $G$ matching the Radon product $\frac{\mathrm{d}t}{t}\otimes\mu_1$ under push-forward along the isomorphism $G\simeq\mathbf{R}_{>0}\times G^1$ of Hausdorff locally compact abelian groups induced by the choice of $\tau$.
(3) Let $\gamma\in G$ be a real number such $\lvert\gamma\rvert_G>1$.
(4) We choose, for each continuous character $\omega\in\widehat{G^1}$, a continuous character $\chi\in\widehat{G}$ such that $\chi|_{G^1}$. We denote by $\widetilde{G^1}$ the subset of $\widehat{G}$ given by the chosen continuous characters $\chi$.
(5) We call, for each $\chi\in\widetilde{G^1}$, $x_0(\chi)\in\mathbf{R}$ the unique real number such that $\chi(\tau(t))=t^{ix_0(\chi)}$ as smooth functions of $t\in\mathbf{R}_{>0}$ and $t_0(\chi)\in\mathbf{R}$ the unique real number such that $\chi(\gamma)=\lvert\gamma\rvert_G^{it_0(\chi)}$, and such that $t_0(\chi)\in[0,2\pi/\log\lvert\gamma\rvert_G)$.
Remark 4.4.2.4. The choice of $\widetilde{G^1}$ amounts to choosing a holomorphic parametrization for the Riemann surface $\Omega(G)$:

$$
\chi\lvert\cdot\rvert_G^s,\,s\in\mathbf{C}. \tag{4.4.2.3}
$$

As $s$ varies over $i\mathbf{R}$, (4.4.2.3) provides a smooth parametrization for the topological space $\widehat{G}$, fibred over the discrete set $\widehat{G^1}$ (which, if we assume that $G$, and hence $G^1$, is second-countable, is a countable discrete set).
Since $G$ is $\mathbf{R}_{>0}$-modulated, it is isomorphic, as a Hausdorff locally compact abelian group, to $\mathbf{R}_{>0}\times G^1$, with $G^1$ compact Hausdorff, under the choice $\tau$ of continuous homomorphic section to the module $\lvert\cdot\rvert_G$. The dual group of $\mathbf{R}_{>0}$ is smoothly isomorphic to $\mathbf{R}$, and the continuous quasi-characters of $\mathbf{R}_{>0}$ are of the form $t\mapsto t^s$, with $\widehat{\mathbf{R}_{>0}}$ embedding as $i\mathbf{R}$ within the complex $s$-plane of all continuous quasi-characters.
Note that such section $\tau$ exists by Remark D.2.1.2.

4.4.2.1. *The exponential system on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$.* We let $G$ be an $\mathbf{R}_{>0}$-modulated group. We fix an element $\gamma\in G$ such that $\lvert\gamma\rvert_G>1$.
We begin with the following description of the orthogonal $(\gamma^{\mathbf{Z}})^\perp\subset\widehat{G}$, i.e. the subgroup:

$$
(\gamma^{\mathbf{Z}})^\perp=\{\chi\in\widehat{G}:\chi(\gamma^m)=1,\,m\in\mathbf{Z}\}.
$$

## PDF page 193

**4.4. EXPONENTIAL SYSTEM ON MONOGENIC QUOTIENTS OF $\mathbf{R}_{>0}$-MODULATED GROUPS** · **193**

This is a discrete subgroup of $\widehat{G}$, isomorphic to the dual group of the compact group $G/\gamma^{\mathbf{Z}}$ (see Lemma D.1.4.6).

Lemma 4.4.2.5 (Orthogonal of a monogenic discrete group). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. Let $\gamma\in G$ be such that $\lvert\gamma\rvert_G>1$.
We choose, for each continuous character $\omega\in\widehat{G^1}$, a continuous character $\chi\in\widehat{G}$ such that $\chi|_{G^1}=\omega$, and denote by $\widetilde{G^1}\subset\widehat{G}$ the set of the chosen representatives of the elements of $\widehat{G^1}$.
We have, as discrete subsets of $\widehat{G}$:*

$$
(\gamma^{\mathbf{Z}})^\perp=\{\bar\chi\lvert\cdot\rvert_G^{-\frac{2\pi im}{\log\lvert\gamma\rvert_G}+it_0(\chi)},\,\chi\in\widetilde{G^1},\,m\in\mathbf{Z}\} \tag{4.4.2.4}
$$

where $t_0(\chi)\in\mathbf{R}$ is, for each $\chi\in\widetilde{G^1}$, the unique real number such that $\chi(\gamma)=\lvert\gamma\rvert_G^{it_0(\chi)}$, and $t_0(\chi)\in[0,2\pi/\log\lvert\gamma\rvert_G)$.
Proof. We note that the subset of $\widehat{G}$ defined by the right side of (4.4.2.4) is contained in $(\gamma^{\mathbf{Z}})^\perp$. Let now $\chi_0\in\widehat{G}$ be an element of $(\gamma^{\mathbf{Z}})^\perp$. This means that for every $m\in\mathbf{Z}$, we have $\chi_0(\gamma^m)=1$. For the unique $\chi\in\widetilde{G^1}$ such that $\chi_0|_{G^1}=\chi|_{G^1}$, there exists a unique $s\in\mathbf{C}$ such that $\chi_0=\chi\lvert\cdot\rvert_G^s$, and since $\chi_0$ is unitary, then $s\in i\mathbf{R}$. There therefore exists $t_1\in\mathbf{R}$ such that $\chi\lvert\cdot\rvert_G^{it_1}\in(\gamma^{\mathbf{Z}})^\perp$, and since the set of all such $t_1$'s is a torsor under $\mathbf{Z}/(\frac{2\pi}{\log\lvert\gamma\rvert_G}\mathbf{Z})$, there exists a unique $t_1\in[-2\pi/\log\lvert\gamma\rvert_G,0)$ satisfying the same property. We denote by $t_1(\chi)$ this preferred $t_1$, and we deduce that every other element of $(\gamma^{\mathbf{Z}})^\perp$ is of the form $\chi\lvert\cdot\rvert_G^{it_1(\chi)+\frac{2\pi im}{\log\lvert\gamma\rvert_G}}$ for some integer $m\in\mathbf{Z}$.
We define $t_0(\chi):=-t_1(\chi)$, and deduce that we have $\chi(\gamma)=\lvert\gamma\rvert_G^{it_0(\chi)}$, and $t_0(\chi)\in[0,2\pi/\log\lvert\gamma\rvert_G)$. Since $(\gamma^{\mathbf{Z}})^\perp$ is stable under complex conjugation, we deduce that (4.4.2.4) holds.
The subspace topology on $(\gamma^{\mathbf{Z}})^\perp$ is the discrete topology by Lemma D.1.4.6, since $G/\gamma^{\mathbf{Z}}$ is compact Hausdorff. The topology on the subset $A:=\{\chi\in\widetilde{G^1}:\bar\chi\lvert\cdot\rvert_G^{-\frac{2\pi im}{\log\lvert\gamma\rvert_G}+it_0(\chi)}\}$ is the quotient topology induced by the surjective map $\widetilde{G^1}\times\mathbf{Z}\to A$ defined by $(\chi,m)\mapsto\bar\chi\lvert\cdot\rvert_G^{-\frac{2\pi im}{\log\lvert\gamma\rvert_G}+it_0(\chi)}$, with $\widetilde{G^1}$ topologized with the quotient topology induced from the discrete topology on $G^1$ by the map $\omega\mapsto\chi$ ($\chi$ being the chosen lift in $\widetilde{G^1}$ of $\omega\in\widehat{G^1}$). $\widetilde{G^1}$ is therefore a discrete subset of $\widehat{G}$, and $A$ carries the discrete topology since the fibres of the map $\widetilde{G^1}\times\mathbf{Z}\to A$ are single points. $\square$

We prove the following analog of Lemma 4.2.1.2. It will be our source of absolute Schauder bases on subquotients of $\mathcal{S}_\mathrm{E}(G)$, for $G$ a second-countable $\mathbf{R}_{>0}$-modulated group.

Lemma 4.4.2.6 (Exponential system on $\mathbf{R}_{>0}$-modulated groups). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. We adopt the conditions and choices from Situation 4.4.2.3. In particular, we assume that $G$ is second-countable.*

(1) *Any enumeration of the countable set of smooth functions:*

$$
\left\{e_{\chi,m}(t,g):=\bar\omega(g)t^{\frac{-2\pi im}{\log(\lvert\gamma\rvert_G)}+it_0(\chi)-ix_0(\chi)}=\bar\chi\lvert\cdot\rvert_G^{-\frac{2\pi im}{\log(\lvert\gamma\rvert_G)}+it_0(\chi)}\right\}_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}}=(\gamma^{\mathbf{Z}})^\perp\subset\widehat{G} \tag{4.4.2.5}
$$

*on $G$, is an absolute Schauder basis for $\mathcal{S}(G/\gamma^{\mathbf{Z}})$.
Its dual basis is the countable set of continuous functionals $\{a_{\chi,m}(\cdot)\}_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}}$, where, for any $\phi\in\mathcal{S}(G/\gamma^{\mathbf{Z}})$:*

$$
a_{\chi,m}(\phi):=\frac{1}{\log(\lvert\gamma\rvert_G)\mu_1(G^1)}\int_{G/\gamma^{\mathbf{Z}}}\phi(g)\chi(g)\lvert g\rvert_G^{\frac{2\pi im}{\log(\gamma)}-it_0(\chi)}\,\mathrm{d}\bar\mu_\gamma(g) \tag{4.4.2.6}
$$

*is the $m$th Fourier coefficient functional, and where $\bar\mu_\gamma$ is the unique Haar measure on $G/\gamma$ determined, as per Theorem D.1.2.1, by the choices of $\mu$ on $G$ and the counting measure on $\gamma^{\mathbf{Z}}\subset G$.
(2) Let $\phi\in\mathcal{S}(G/\gamma^{\mathbf{Z}})$ be the arbitrary element.*

## PDF page 194

**194** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

(a) *The countable set $\{a_{\chi,m}(\phi)\}_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}}$ uniquely determines a Schwartz-Bruhat function $v_\phi\in\mathcal{S}((\gamma^{\mathbf{Z}})^\perp)$ such that, for $\xi\in(\gamma^{\mathbf{Z}})^\perp$ the unique character corresponding to the pair $(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}$, we have*

$$
v_\phi(\xi)=a_{\chi,m}(\phi). \tag{4.4.2.7}
$$

(b) *Let $q$ be any continuous seminorm on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$. Then, for each $\chi\in\widetilde{G^1}$, we have $\{q(e_{\chi,m})\}_{m\in\mathbf{Z}}$ is an element of $\mathcal{O}_M(\mathbf{Z})$, i.e. a complex-valued function $u\colon\mathbf{Z}\to\mathbf{C}$ such that for any Schwartz-Bruhat function $v\in\mathcal{S}(\mathbf{Z})$, we have $uv\in\mathcal{S}(\mathbf{Z})$.*

Remark 4.4.2.7. We note that the Haar measure on $G/\gamma^{\mathbf{Z}}$ given by $A^{-1}\bar\mu_\gamma$, for $A:=\mu_1(G^1)$, agrees with the unique Haar measure obtained from the canonical measure on the $\mathbf{R}_{>0}$-modulated group $G$, and the volume-1 measure on $G^1$, as per Theorem D.1.2.1. We further refer the reader to Definition D.2.1.1 for the normalization required for a Haar measure on an $\mathbf{R}_{>0}$-modulated group to be the canonical measure. In particular, the Haar measure on $G/\gamma^{\mathbf{Z}}$ obtained as $B^{-1}\bar\mu_\gamma$ for $B:=\log(\lvert\gamma\rvert_G)\mu_1(G^1)$, is the unique volume-1 Haar measure on the compact Hausdorff abelian group $G/\gamma^{\mathbf{Z}}$.

Remark 4.4.2.8. The notation $\mathcal{O}_M(\Gamma)$, for $\Gamma$ a Hausdorff locally compact abelian group, is borrowed from [Sch-a, Ch.VII,§5,pp.243-244] and denotes the multiplier space of $\mathcal{S}(\Gamma)$, i.e. the $\mathbf{C}$-vector space of those continuous functions $u\colon\Gamma\to\mathbf{C}$ such that $u\cdot\mathcal{S}(\Gamma)\subset\mathcal{S}(\Gamma)$, topologized by transport of structure from $\mathcal{S}(\Gamma)$.
$\mathcal{O}_M(\Gamma)$ will only play a role here, to enable us to deduce that certain products, such as $uv$ in Lemma 4.4.2.6(2), are sequences of rapid decay (see also [Tre, Part III,Ch.51,p.527]).
In the special case $G=\mathbf{R}_{>0}$, we choose $\chi=1$, in which case $(\gamma^{\mathbf{Z}})^\perp$ is the subgroup of $\widehat{G}$ of those characters of the form $t\mapsto t^{\frac{2\pi im}{\log(\gamma)}}$ (noting that we have $\lvert\gamma\rvert_G=\gamma$ in this case).
The sequence $a_{\chi,m}(\phi)$ is the sequence of Fourier coefficients of $\phi$, and since $\phi\in\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$, it is a sequence of rapid decay, i.e. an element of $\mathcal{S}(\frac{2\pi i\mathbf{Z}}{\log(\gamma)})\simeq\mathcal{S}((\gamma^{\mathbf{Z}})^\perp)$.
A fundamental family of continuous seminorms $\{q_k\}_{k\ge 0}$ on $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$ is obtained from the family of seminorms $\widetilde{q}_k:=\lVert(t\partial_t)^k(\cdot)\rVert_u$ on $\mathcal{S}(\mathbf{R}_{>0})$ following the definition of quotient seminorms from [NB, Thm.5.11.2]. In particular

$$
q_k(\lvert\cdot\rvert_{\mathbf{R}}^{-\frac{2\pi im}{\log(\gamma)}})\le\widetilde{q}_k(\lvert\cdot\rvert_{\mathbf{R}}^{-\frac{2\pi im}{\log(\gamma)}})=\left(\frac{2\pi\lvert m\rvert}{\log(\gamma)}\right)^k\widetilde{q}_0(\lvert\cdot\rvert_{\mathbf{R}}^{-\frac{2\pi im}{\log(\gamma)}})=\left(\frac{2\pi\lvert m\rvert}{\log(\gamma)}\right)^k
$$

which illustrates the meaning of Lemma 4.4.2.6(2.b): the sequence $q_k(e_{\chi,m})$, for each $k\ge 0$ (i.e. for each member of a fundamental family of continuous seminorms, and hence, up to absolute constants, for any continuous seminorm) is a sequence of polynomial growth, and hence a Schwartz multiplier for $\mathcal{S}(\mathbf{Z})$.
Lemma 4.4.2.6(2.b) will be used to prove the convergence of the sequence of basis projections in several situations at the end of Chapter 6 of this work, enabling us to prove that certain continuous linear injective operators are actually linear topological isomorphisms, compatibly with $C_F$-actions on source and target.

Remark 4.4.2.9. We note that for each pair $(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}$, there exists a unique continuous character $\xi\in(\gamma^{\mathbf{Z}})^\perp$ such that $\xi=e_{\chi,m}$. A more general and stronger form of (2.b) is the assertion that $\widehat{G}\subset\mathcal{O}_M(G)$ holds. In particular, since $(\gamma^{\mathbf{Z}})^\perp\subset\widehat{G}$, we have that every $e_{\chi,m}$ is a Schwartz multiplier, and hence in particular a smooth function on $G$ such that multiplication by any Schwartz-Bruhat function on $G$ by it, is again a Schwartz-Bruhat function.
In particular, for any continuous seminorm $q$ on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$, for each $\chi\in\widetilde{G^1}$, there exists a polynomial $p\in\mathbf{C}[X]$ such that $q(e_{\chi,m})\ll_q p(m)$ as the integer $m\in\mathbf{Z}$ satisfies $\lvert m\rvert\to+\infty$.

Proof. (1) and (2) : We note that indeed $a_{\chi,m}(e_{\chi,m})=1$ and $a_{\chi,m}(e_{\chi',m'})=0$ for all pairs $(\chi',m')\ne(\chi,m)$. We are using the compactness of $G/\gamma^{\mathbf{Z}}$ to deduce that the smooth functions $e_{\chi,m}$ are all $\bar\mu_\gamma$-absolutely integrable over $G/\gamma^{\mathbf{Z}}$.

## PDF page 195

**4.4. EXPONENTIAL SYSTEM ON MONOGENIC QUOTIENTS OF $\mathbf{R}_{>0}$-MODULATED GROUPS** · **195**

In particular, the pair

$$
(\{e_{\chi,m}\}_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}},\{a_{\chi,m}(\cdot)\}_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}})
$$

is a bi-orthogonal sequence with respect to the duality $\langle\mathcal{S}(G/\gamma^{\mathbf{Z}}),\mathcal{S}(G/\gamma^{\mathbf{Z}})'\rangle$.
This implies that $\{e_{\chi,m}\}_{m\in\mathbf{Z}}$ is a topologically free set by [Jar, Part II,Ch.14,§14.1,Prop.1,p.289]. Let $\phi\in\mathcal{S}(G/\gamma^{\mathbf{Z}})$ be an arbitrary smooth function.
We denote by $t\partial_t$ the derivation operator along the continuous 1-parameter group of $G/\gamma^{\mathbf{Z}}$ induced by the choice of $\tau\colon\mathbf{R}_{>0}\to G$, the fixed continuous section to the module homomorphism $\lvert\cdot\rvert_G$, composed with the continuous quotient homomorphism $G\to G/\gamma^{\mathbf{Z}}$.
Since $\gamma^{\mathbf{Z}}\subset G$ is discrete and co-compact, there exists a smooth compactly supported function $\psi\in\mathcal{D}(G)$ such that $\sum_{m\in\mathbf{Z}}\psi(\gamma^mx)=\phi(x)$ as smooth functions of $x\in G$, invariant under the action of $\gamma^{\mathbf{Z}}$ by left-translation.
Since $G$ is second-countable and compactly generated (since $G^1$ is compact), there exists a sequence of compact subgroups $\{k_r\}_{r\ge 0}$, with $k_r\subset G$ such that $k_r^\perp\subset\widehat{G}$ is open and compactly generated for each integer $r\ge 0$, such that $\bigcup_{r\ge 0}k_r^\perp=\widehat{G}$ (see Lemma D.1.4.4), and such that $G/k_r$ is an abelian Lie group.
It follows that there exists a large enough $r\ge 0$ such that $\psi$ is $k_r$-invariant.
We consider the sum:

$$
\sum_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}:\chi\in F_j,\lvert m\rvert\le M}a_{\chi,m}(\phi)e_{\chi,m} \tag{4.4.2.8}
$$

for each integer $M\ge 0$ and each finite subset $F_j\subset\widetilde{G^1}$ indexed by an integer $j\ge 0$, such that $\bigcup_{j\ge 0}F_j=\widetilde{G^1}$.
We now note that the assignment:

$$
(\chi,m)\mapsto a_{\chi,m}(\phi) \tag{4.4.2.9}
$$

uniquely determines a continuous function on the discrete group $(\gamma^{\mathbf{Z}})^\perp\simeq\widehat{G/\gamma^{\mathbf{Z}}}$ (by [DE, Prop.3.1.5(a)] and [DE, Prop.3.6.1(a)], since $G/\gamma^{\mathbf{Z}}$ is compact Hausdorff) satisfying the following property: for $\mathcal{F}\colon\mathcal{S}(G/\gamma^{\mathbf{Z}})\to\mathcal{S}(\widehat{G/\gamma^{\mathbf{Z}}})$ the Fourier transform, defined as

$$
\phi\mapsto\mathcal{F}(\phi)(\eta):=\frac{1}{\log(\lvert\gamma\rvert_G)\mu_1(G^1)}\int_{G/\gamma^{\mathbf{Z}}}\phi(g)\overline{\eta}(g)\,\mathrm{d}\bar\mu_\gamma(g)
$$

we have:

$$
\mathcal{F}(\phi)(\overline{\eta})=a_{\chi,m}(\phi) \tag{4.4.2.10}
$$

for $\eta=\overline{\chi}\lvert\cdot\rvert_G^{\frac{2\pi im}{\log(\lvert\gamma\rvert_G)}+it_0(\chi)}$, noting that all $\eta\in(\gamma^{\mathbf{Z}})^\perp$ are described uniquely in this manner, by Lemma 4.4.2.5.
We further note that $\mathcal{F}(\phi)(\overline{\eta})$ is supported over $k_r^\perp\cap(\gamma^{\mathbf{Z}})^\perp\subset\widehat{G}$. In particular, $a_{\chi,m}(\phi)=0$ for all $(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}$ satisfying $\chi\in k_r^\perp$.
In order to show that the sum in (4.4.2.8) converges absolutely (which we are required to do, in order to verify the defining properties of an absolute Schauder basis; see the discussion preceding [Jar, Part II,Ch.14,§14.2,Prop.3,p.298] and the discussion at the beginning of [Jar, Part II,Ch.14,§14.6,p.305], as well as the discussion following [Jar, Part II,Ch.14,§14.7,Cor.6,p.314]) as $M\to+\infty$ and $j\to+\infty$, it is enough to show that the following assertion holds.
Let $G_0$ be a compact abelian Lie group (which, in our situation, is chosen to be $G/(\gamma^{\mathbf{Z}}\cdot k_r)$, where we may choose $k_r\subset G^1$ for each integer $r\ge 0$ large enough), $\mu_0$ the volume-1 Haar measure on $G_0$, $\phi\in\mathcal{S}(G_0)=\mathcal{D}(G_0)$. Then the sum:

$$
\sum_{\xi\in\widehat{G_0}}\mathcal{F}(\phi)(\xi)\overline{\xi} \tag{4.4.2.11}
$$

## PDF page 196

**196** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

converges uniformly over $G_0$ along with all of its directional derivatives along any smooth 1-parameter subgroup $\alpha\colon\mathbf{R}_{>0}\to G_0$.
Recall that for $G_0$ a compact abelian Lie group, this mode of convergence is, by definition, the convergence with respect to the Hausdorff locally convex topology on $\mathcal{D}(G_0)$. The assertion is therefore saying that the sum of smooth functions on $G_0$ from (4.4.2.11), converges in $\mathcal{D}(G_0)$.
To clarify the meaning of the convergence assertion further, we note that we regard $\bar\xi$ in (4.4.2.11) as a smooth function on $G_0$ (since it is a continuous character, hence smooth), and the collection $\{\mathcal{F}(\phi)(\xi)\}_{\xi\in\widehat{G_0}}$ as a collection of complex coefficients that multiply each $\bar\xi$ obtaining the smooth function $g\mapsto\mathcal{F}(\phi)(\xi)\bar\xi(g)$ of $g\in G_0$. The sum in (4.4.2.11) is the limit of finite sums of such smooth functions on $G_0$, and the assertion to be proven is that it converges uniformly, together with all of its directional derivatives, i.e. in $\mathcal{D}(G_0)$.
We will now establish this. Indeed, we have $\partial_\alpha\bar\xi=p_\alpha(\bar\xi)\bar\xi$, where $p_\alpha(\bar\xi)=(\partial_\alpha\bar\xi)(e)$ for $e\in G_0$ the neutral element.
Multiplication by $p_\alpha(\bar\xi)$ on $\mathcal{S}(\widehat{G_0})$ is a linear topological automorphism (it is multiplication by a polynomial function of $\xi\in\mathbf{Z}^A\times\mathbf{T}^B\times F$ for $A,B\in\mathbf{N}$ and $F$ a finite group) and $\mathcal{F}(\phi)(\xi)$ is a function of $\xi\in\mathbf{Z}^A\times\mathbf{T}^B\times F$ of rapid decay.
In particular, $p_\alpha(\bar\xi)\mathcal{F}(\phi)(\xi)$ is an element of $\mathcal{S}(\widehat{G_0})$, and as such, it is absolutely integrable with respect to the Plancherel measure on $\widehat{G_0}$ of the Haar measure $(\mu_1(G^1)\log\lvert\gamma\rvert_G)^{-1}\bar\mu_\gamma$. This, is a multiple of the counting measure on the discrete subgroup $(\gamma^{\mathbf{Z}})^\perp\subset\widehat{G_0}$, by [DE, Prop.1.4.4].
We now note that we have, for each finite subset $V\subset\widehat{G_0}$:

$$
\sup_{g\in G_0}\left\lvert\sum_{\xi\in V}p_\alpha(\bar\xi)\mathcal{F}(\phi)(\xi)\bar\xi(g)\right\rvert\le\sum_{\xi\in V}\lvert p_\alpha(\bar\xi)\mathcal{F}(\phi)(\xi)\rvert \tag{4.4.2.12}
$$

and by absolute integrability of the function $p_\alpha(\bar\xi)\mathcal{F}(\phi)(\xi)$ on $\widehat{G_0}$, we deduce that the rightmost side of (4.4.2.12) is bounded above by the convergent sum $\sum_{\xi\in\widehat{G_0}}\lvert p_\alpha(\bar\xi)\mathcal{F}(\phi)(\xi)\rvert$, which proves that the finite sums:

$$
\sum_{\xi\in V}\mathcal{F}(\phi)(\xi)(\partial_\alpha\bar\xi)
$$

converge absolutely and uniformly over $G_0$ as smooth functions on $G_0$. This proves the convergence assertion for the sum in (4.4.2.11) in $\mathcal{D}(G_0)$.
Note that $(\gamma^{\mathbf{Z}})^\perp$ contains $(\gamma^{\mathbf{Z}}\cdot k_r)^\perp$ for every $r\ge 0$, which is isomorphic to the dual group of $G/(\gamma^{\mathbf{Z}}\cdot k_r)$ by [DE, Prop.3.6.1(a)], and so indeed proving that for $\phi$ a $k_r$-invariant element of $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ (under the left-translation action on the right-, equivalently left-cosets), the sum (indexed by the sole elements of $(\gamma^{\mathbf{Z}})^\perp$ contained in $(\gamma^{\mathbf{Z}}\cdot k_r)^\perp$) from (4.4.2.11), converges, for $G_0=G/(\gamma^{\mathbf{Z}}\cdot k_r)$, suffices.
For each fixed $\chi\in\widehat{G^1}$, however, there exists a large enough $r\ge 0$ such that every $\xi\in(\gamma^{\mathbf{Z}})^\perp$ such that $\xi|_{G^1}=\chi|_{G^1}$, is already contained in $(\gamma^{\mathbf{Z}}\cdot k_r)^\perp$, and so the restriction of $p_\alpha$ to the subset of such characters $\xi\in(\gamma^{\mathbf{Z}})^\perp$ such that $\xi|_{G^1}=\chi|_{G^1}$ has absolute value that depends on $\xi$ through the unique integer $m\in\mathbf{Z}$ such that $\xi=\chi\lvert\cdot\rvert_G^{\frac{2\pi im}{\log(\lvert\gamma\rvert_G)}-it_0(\chi)}$, and, as a function of $\lvert m\rvert$, grows polynomially.
We conclude that (2) holds, and that the sum on the right side of (4.4.2.8) is absolutely convergent as $j\to+\infty$ and $M\to+\infty$ in $\mathcal{S}(G/\gamma^{\mathbf{Z}})$.
This therefore proves that the finite rank operators

$$
\sum_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}:\chi\in F_j,\lvert m\rvert\le M}a_{\chi,m}(\cdot)e_{\chi,m}
$$

converge absolutely (see the discussion preceding [Jar, Part II,Ch.14,§14.2,Prop.3,p.298] and the discussion at the beginning of [Jar, Part II,Ch.14,§14.6,p.305]) with respect to the topology of simple convergence, as $j\to+\infty$ and $M\to+\infty$. The limit of such sums is the identity on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$, since it is so pointwise.

## PDF page 197

**4.5. PERIODIC SCHAUDER BASES IN THE ABSENCE OF MULTIPLICITY** · **197**

It follows that $\{e_{\chi,m},a_{\chi,m}(\cdot))\}_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}}$ is not only a bi-orthogonal sequence with respect to the duality $\langle\mathcal{S}(G/\gamma^{\mathbf{Z}}),\mathcal{S}(G/\gamma^{\mathbf{Z}})'\rangle$. It is also a topological basis, and hence a Schauder basis by [Jar, Part II,Ch.14,§14.2,Prop.3,p.292], and an absolute Schauder basis, either by the foregoing, which shows that the mode of convergence of the sum in (4.4.2.8), as $j,M\in\mathbf{N}$ tend to grow, is absolute (in the sense of [Jar, Part II,Ch.14,§14.7,(\*),p.314]) for every $\phi\in\mathcal{S}(G/\gamma^{\mathbf{Z}})$, or by Theorem 4.1.2.6(3), since $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ is nuclear and $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ is a strict inductive limit of a sequence of nuclear Fréchet spaces by Lemma D.1.5.6(2) and second-countability of $G$.
By Lemma 4.1.2.4, which applies since $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ is Montel, and hence barrelled and reflexive, by Theorem D.1.5.7(2), the countable set of coefficient functionals $\{a_{\chi,m}(\cdot)\}_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}}$ is a Schauder basis (with respect to any choice of enumeration of the elements of $\widetilde{G^1}$). Since $\mathcal{S}(G/\gamma^{\mathbf{Z}})'_\beta$ is itself nuclear by Theorem D.1.5.7(1), then, with respect to any such enumeration of the countably many elements of $\widetilde{G^1}$, the resulting sequence $\{a_{\chi,m}(\cdot)\}_{(\chi,m)\in\widetilde{G^1}\times\mathbf{Z}}$ is an equicontinuous basis by [Jar, Part II,Ch.14,§14.3,Cor.3,p.296], and hence, by Theorem 4.1.2.6(1), it is an absolute Schauder basis. $\square$

4.5. Periodic Schauder Bases in the absence of multiplicity

In this section, we exhibit absolute Schauder bases for the quotients of $\mathcal{S}_\mathrm{E}(G)$ by the kernel of each of the monogenic periodization operators $\Phi_\gamma$ on $\mathcal{S}_\mathrm{E}(G)$ introduced in Definition 4.4.2.1.
We recall from the definition that we defined:

$$
\Phi_\gamma(f)(x):=\sum_{k\in\mathbf{Z}}f(\gamma^kx)
$$

and:

$$
\Phi_{\gamma,\chi}(f)(x):=\sum_{k\in\mathbf{Z}}\int_{G^1}\chi(g)f(\gamma^kgx)\,\mathrm{d}\mu_1(g)
$$

for each $f\in\mathcal{S}_\mathrm{E}(G)$. We have, however, yet to show that indeed these assignments are well posed, i.e. that the sums converge, uniformly over the compact Hausdorff abelian group $G/\gamma^{\mathbf{Z}}$, and with respect to the Hausdorff locally convex topology on $G/\gamma^{\mathbf{Z}}$.
This, we will be doing throughout the following subsection, along with establishing properties of the operators $\Phi_\gamma$ and $\Phi_{\gamma,\chi}$.

4.5.1. Periodic Schauder Bases: the monogenic case. Let $G$ be an $\mathbf{R}_{>0}$-modulated group, $\gamma\in G$ an element such that $\lvert\gamma\rvert_G>1$, and $\chi\in\widehat{G}$ a continuous character.

4.5.1.1. *Monogenic periodization on $\mathbf{R}_{>0}$-modulated groups.* In this section, we use the exponential system on $\mathcal{S}_\mathrm{E}(G/\gamma^{\mathbf{Z}})$ to source absolute Schauder bases for the ranges of the periodization operators $\Phi_\gamma$, $\Phi_{\gamma,\chi}$ from Definition 4.4.2.1, for then extending the constructions and results to the case of finitely many elements $\{\gamma_1,\dots,\gamma_N\}\subset G$ such that $\lvert\gamma_k\rvert_G>1$ for $1\le k\le N$, in the next subsection.

Proposition 4.5.1.1 (Sourcing Periodic Schauder Bases - I). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. We adopt the conditions and choices from Situation 4.4.2.3.
Then:*

(1) The linear map:

$$
\Phi_\gamma\colon\mathcal{S}_\mathrm{E}(G)\to\mathcal{S}(G/\gamma^{\mathbf{Z}}) \tag{4.5.1.1}
$$

defined by the assignment:

$$
\Phi_\gamma\colon f\mapsto\sum_{k\in\mathbf{Z}}f(\gamma^kx) \tag{4.5.1.2}
$$

## PDF page 198

**198** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

*as a function of $x \in G$, is continuous, surjective, and sends the closed subspace $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \subset \mathcal{S}_{\mathrm{E}}(G)$ of exponentially decaying Schwartz-Bruhat functions on $G$ that are $\chi|_{G^1}$-homogeneous with respect to the left-translation action by $G^1$, onto a closed subspace of $\mathcal{S}(G/\gamma^{\mathbf{Z}})$.*

(2) *$\Phi_{\chi,\gamma}(f)$ is a Schwartz-Bruhat function on the compact Hausdorff abelian group $G/\gamma^{\mathbf{Z}}$.*

(3) *The linear operator $\Phi_{\chi,\gamma}$ from (4.4.2.1) is continuous, relatively open, with closed range.*

(4) *$\ker(\Phi_{\chi,\gamma}) \cap \mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$ is the closure in $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$ of the linear subspace generated by the elements $\phi(x)-\phi(\gamma x)$ as functions of $x \in G$ and as $\phi$ varies over all the elements of $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$.*

(5) *$\ker(\Phi_{\gamma})$ is the closure in $\mathcal{S}_{\mathrm{E}}(G)$ of the linear subspace generated by the elements $\phi(x)-\phi(\gamma x)$ as functions of $x \in G$ and as $\phi$ varies over all the elements of $\mathcal{S}_{\mathrm{E}}(G)$.*

(6) The linear map:

$$
\tag{4.5.1.3}
P_{\gamma} : \mathcal{S}_{\mathrm{E}}(G) \to \mathcal{S}_{\mathrm{E}}(G)
$$

*assigned by $P_{\gamma}(\phi)(x) := \phi(x)-\phi(\gamma x)$ has closed range, and its formation commutes with passage to the $G^1$-isotypes for the continuous left-translation acton of $G^1$ on $\mathcal{S}_{\mathrm{E}}(G)$.*

REMARK 4.5.1.2 (On the non-bornologicity of $\mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$). Note that $\Phi_{\gamma}$ is itself open. Indeed, $\mathcal{S}_I(G)$ is linearly and topologically isomorphic to $\mathcal{S}_I(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1)$ by Theorem D.3.3.7(3), and hence Köthe's Open Mapping Theorem (see [Gro-f, Ch.4,§5,Thm.2(1),p.148], and [SN, §2,Cor.3,p.8]) applies, being $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ itself a strict LF-space, since $G$ is assumed to be second-countable.

We note that $\Phi_{\gamma}$ extends to a sequentially continuous linear map:

$$
\mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1) \to \mathcal{S}(G/\gamma^{\mathbf{Z}}).
$$

If $\mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$ is bornological, which happens if $G^1$ has compactly generated dual group, i.e. in the case $G^1$ is an abelian Lie group, then the canonical continuous linear operator $\mathcal{S}_I(G) \to \mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$ is a linear topological isomorphism by Corollary C.2.3.12.

See also Remark 4.5.1.3 below.

REMARK 4.5.1.3 (Caveat on tensor products and inductive limits). The phenomenon highlighted in Remark 4.5.1.2 is caused by a general result observed in [Gro-b, Ch.I,§1,No.3,Rem.1,p.47]: let $E$ be a Fréchet space, and $F$ a strict LF-space. Assume that $E$ is not normable and that there exists a defining sequence $\{F_m\}_{m \ge 0}$ for $F$, presenting $F$ as the Hausdorff locally convex inductive limit of the Fréchet spaces $F_m$. Further assume that the sequence is such that $F_m \subset F_{m+1}$ is a strict containment.

Then $\varinjlim_{m \ge 0} (F_m\, \widehat{\otimes}_{\pi} E) \to F\, \widehat{\otimes}_{\pi} E$ is not a linear topological isomorphism.

In the case of $\mathcal{S}_I(G)$ for $G$ a general modulated group, by Theorem D.3.3.7(3) any choice of continuous homomorphic section $\tau$ to the module $|\cdot|_G$ induces a linear topological isomorphism $\mathcal{S}_I(G) \simeq \mathcal{S}_I(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1)$, with $G^1 := \ker(|\cdot|_G)$ a compact Hausdorff abelian closed subgroup.

The Schwartz-Bruhat space $\mathcal{S}(G^1)$ is indeed a strict LF-space, since $G$ is assumed to be second-countable, which forces $G^1$ to also be second-countable.

If $G^1$ does not have finitely generated dual group, then a defining sequence $\{F_m\}_{m \ge 0}$ as in the foregoing can be found, i.e. such that the closed inclusions $F_m \subset F_{m+1}$ are strict.

Since $\mathcal{S}_I(\mathbf{R}_{>0})$ is a non-normable Fréchet space, we are led to the conclusion from Remark 4.5.1.2, i.e. the inductive tensor product topology on $\mathcal{S}_I(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1)$ and the projective tensor product topology on $\mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$ are not equivalent. The canonical continuous linear operator $\mathcal{S}_I(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1) \to \mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$ is, however, a continuous bijection.

Its linear inverse is sequentially continuous (as an application of Proposition C.2.3.11) and hence source and target have equivalent von-Neumann bornologies.

## PDF page 199

**4.5. PERIODIC SCHAUDER BASES IN THE ABSENCE OF MULTIPLICITY** · **199**

PROOF. (1) : By Theorem D.3.3.7(3), applied for $I = \mathbf{R}$, the choice $\tau$ of continuous homomorphic section to the module homomorphism $|\cdot|_G$ induces by pullback a linear topological isomorphism:

$$
\tag{4.5.1.4}
\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1) \to \mathcal{S}_{\mathrm{E}}(G)
$$

compatible with the left-translation action of $G^1$ through the right tensor factor on the source, and by left-translation on the target.

Formation of the series defining $\Phi_{\gamma}(f)(x)$ as a function of $x \in G$ for any $f \in \mathcal{S}_{\mathrm{E}}(G)$ converges pointwise over $G$ to a $\gamma^{\mathbf{Z}}$-invariant function, hence a function on $G/\gamma^{\mathbf{Z}}$. To see this, we proceed as follows.

We call $\gamma_0 := |\gamma|_G > 1$, and, for each $g \in G^1$, $\phi_g(t) := f(\tau(t)g)$ as a Schwartz-Bruhat function of $t \in \mathbf{R}_{>0}$ of exponential decay.

The function $t \mapsto \phi(t) := \sup_{g \in G^1} \phi_g(t)$ is continuous over $\mathbf{R}_{>0}$ because $G^1$ is compact Hausdorff, and, for every integer $N \ge 1$, there exists $T_N > 0$ and a real number $C_N > 0$, such that $\phi(t)$ still satisfies the estimate $|\phi(t)| \le C_N e^{-N|\log(t)|}$ for all $t \in \mathbf{R}_{>0}$ such that $|\log(t)| > T_N$.

The same method from the proof of Lemma 4.2.1.5 then shows that the series defining $\Phi_{\gamma}(f)(x)$ converges for every $x \in G$, since it is dominated from above by the series $\sum_{k \in \mathbf{Z}} |\phi(\gamma_0^k t)|$, for $\gamma_0 := |\gamma|_G > 1$. Upon replacing $f$ with $\partial_{\alpha}^k f$ for each integer $k \ge 0$ and for $\alpha : \mathbf{R}_{>0} \to G$ the arbitrary continuous 1-parameter subgroup, the same holds for the series defining $\Phi_{\gamma}(\partial_{\alpha}^k f)$, and the convergence is uniform over the compact subsets of $G$: since $G^1$ is compact, the locally uniform mode of convergence is seen by means of the same method from the proof of Lemma 4.2.1.5, which discusses the case $G = \mathbf{R}_{>0}$.

Formation of $\partial_{\alpha}^k$ commutes with $\Phi_{\gamma}$ for each integer $k \ge 0$, and hence $\Phi_{\gamma}(f)$ is a smooth $\gamma^{\mathbf{Z}}$-invariant function on $G$ (we refer the reader to the proof of Lemma 2.2.4.3, for a similar argument. Inducting on the degree $k \ge 1$ of $\partial_{\alpha}$, we may rename $\partial_{\alpha}^{k-1} f$ as $f$ and assume $k = 1$. Since $G \simeq \mathbf{R}_{>0} \times G^1$ as Hausdorff locally compact abelian groups, it is enough to treat the case of $\alpha$ with image contained in $G^1$, respectively $\alpha(\mathbf{R}_{>0}) \cap G^1 = \{e\}$, the neutral element.

In the former case, uniform convergence of the series defining $\Phi_{\gamma}$ on compact subsets, and uniform convergence over $G$ of the incremental ratio $(u-1)^{-1}(f(\alpha(u)^{-1}x)-f(x))$ as $u \to 1$, for any $f \in \mathcal{S}_{\mathrm{E}}(G)$, imply the desired commutation of $\Phi_{\gamma}$ and $\partial_{\alpha}$.

We therefore assume $\alpha(\mathbf{R}_{>0}) \cap G^1 = \{e\}$. In this case, the argument is closely analogous to the proof of Lemma 4.2.1.5.

For $k \subset G$ a compact subgroup such that $k^{\perp}$ is compactly generated, and such that $f$ is $k$-invariant, then $\Phi_{\gamma}(f)$ is also $k$-invariant, since the actions of $\gamma^{\mathbf{Z}}$ and of $k$ by left-translation on $\mathcal{S}_{\mathrm{E}}(G)$ commute. This shows that $\Phi_{\gamma}(f)$ is Schwartz-Bruhat over $\mathcal{S}(G/\gamma^{\mathbf{Z}})$.

$\Phi_{\gamma}$ is surjective because $G/\gamma^{\mathbf{Z}}$ is compact Hausdorff: we may therefore find a smooth compactly supported function $u_0 \in \mathcal{D}(G)$ such that $\Phi_{\gamma}(u_0) = 1$, the constant function with value 1 on $G/\gamma^{\mathbf{Z}}$, and for every $\phi \in \mathcal{S}(G/\gamma^{\mathbf{Z}})$, the function $\psi := u_0 \cdot (\phi \circ \pi)$, for $\pi : G \to G/\gamma^{\mathbf{Z}}$ the quotient homomorphism, is smooth and compactly supported over $G$, hence of exponential decay, and we have $\Phi_{\gamma}(\psi) = \phi$ (we further refer the reader to [Bou-II, Ch.VII,§2,No.1,Lemma 1,INT VII.28] and to the footnote [Bou-II, Ch.VII,§2,No.1,Remark 1,INT VII.30] for similar arguments).

For the purposes of showing continuity of the linear operator $\Phi_{\gamma}$, we observe that any convergent Cauchy net $\{f_i\}_{i \in I} \subset \mathcal{S}_{\mathrm{E}}(G)$ is eventually bounded$^{1}$ (i.e. there exists $i_0 \in I$ such that $\{f_i\}_{i \in I, i \ge i_0}$ is bounded), and hence, up to replacing $I$ with $I_0 := \{i \in I : i \ge i_0\}$ for some $i_0$ large enough and renaming $I_0$ as $I$, it is contained within the pre-image $\mathcal{S}_{\mathrm{E}}(\Gamma \cdot \tau(\mathbf{R}_{>0}), k)$ of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(k, \Gamma)$ under (4.5.1.12) (see Definition D.1.5.3 for the construction of the Hausdorff locally convex topological $\mathbf{C}$-vector space of Schwartz-Bruhat functions on a Hausdorff locally compact abelian group), where $k \subset G^1$ is a compact subgroup whose orthogonal $k^{\perp} \subset \widehat{G^1}$ is compactly generated, $\Gamma \subset G^1$ is an open

---

$^{1}$Return here.

## PDF page 200

**200** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

and compactly generated subgroup, and $k \subset \Gamma$, and $\mathcal{S}(k, \Gamma)$ denotes the $\mathbf{C}$-linear subspace of $\mathcal{S}(G^1)$ of those continuous functions that are supported over $\Gamma$, are $k$-invariant, and induce a unique continuous function on the elementary Lie group $\Gamma/k$ that is Schwartz there.

Indeed, since $G^1$ is compact, we may choose $\Gamma = G^1$. The assertion on a fixed bounded subset $B \subset \mathcal{S}_{\mathrm{E}}(G)$ being contained in some $\mathcal{S}_{\mathrm{E}}(k, G)$ follows from Theorem D.3.3.7(3).

We may further denote by $G^1_0$ the quotient $G^1/k$ and define $G_0 := (\tau(\mathbf{R}_{>0}) \cdot G^1)/k = G/k$, promoting it to an $\mathbf{R}_{>0}$-modulated group by defining the module $|\cdot|_{G_0}$ by $k$-invariance (being $k$ contained in $G^1$, the module descends to $(\tau(\mathbf{R}_{>0}) \cdot G^1)/k$, since $|k|_G = 1$).

We let $\gamma^{\mathbf{Z}}$ acts by left-multiplication on the left cosets $G/k$, obtaining a continuous action of $\gamma^{\mathbf{Z}}$ on $\mathcal{S}_{\mathrm{E}}(G/k) \simeq \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1_0)$ by left-translation that is compatible with the one inherited from the left-translation action of the subgroup $\gamma^{\mathbf{Z}} \subset G$ on $\mathcal{S}_{\mathrm{E}}(G)$ (i.e. even though $\gamma^{\mathbf{Z}}$ is not a subgroup of $G/k$ anymore).

We note that, since $G$ is abelian, we have the canonical identification of homogeneous spaces topologized with the respective quotient topologies: $\gamma^{\mathbf{Z}}\backslash G/k = G/(\gamma^{\mathbf{Z}} \cdot k)$.

$G/k$ is now an elementary $\mathbf{R}_{>0}$-modulated abelian Lie group, with $G^1_0$ an elementary compact abelian Lie group, and the resulting operator $\Phi_{\gamma,0} : \mathcal{S}_{\mathrm{E}}(G/k) \to \mathcal{S}(G/(\gamma^{\mathbf{Z}} \cdot k))$ defined by averaging an element of $\mathcal{S}_{\mathrm{E}}(G/k)$ over the action of $\gamma^{\mathbf{Z}}$, is indeed valued in $\mathcal{S}(G/(\gamma^{\mathbf{Z}} \cdot k))$, which is seen upon repeating the argument from the foregoing, and promotes the following to a commutative diagram of linear operators:

(4.5.1.5)

```latex
\begin{tikzcd}
\mathcal{S}_{\mathrm{E}}(G/k) \arrow[r] \arrow[d, "\Phi_{\gamma,0}"'] & \mathcal{S}_{\mathrm{E}}(G) \arrow[d, "\Phi_{\gamma}"] \\
\mathcal{S}(G/(\gamma^{\mathbf{Z}} \cdot k)) \arrow[r] & \mathcal{S}_{\mathrm{E}}(G/\gamma^{\mathbf{Z}})
\end{tikzcd}
```

where the horizontal arrows, sending functions on $G/k$, respectively $G/(\gamma^{\mathbf{Z}} \cdot k)$, to $k$-invariant functions on $G$, respectively $G/\gamma^{\mathbf{Z}}$ (in the latter case, $G/\gamma^{\mathbf{Z}}$ is identified with $\gamma^{\mathbf{Z}}\backslash G$ and the continuous action of $k$ is by right-translation on the left cosets) are continuous.

It is therefore enough to show that $\Phi_{\gamma,0}$ is continuous (for any such $k$), to conclude that we have, for $f$ the limit in $\mathcal{S}_{\mathrm{E}}(G)$ of the Cauchy net $\{f_i\}_{i \in I}$, also contained in $\mathcal{S}_{\mathrm{E}}(k, G)$ since this latter is a closed subspace, $\Phi_{\gamma}(f_i) = \Phi_{\gamma,0}(f_i) \to \Phi_{\gamma,0}(f) = \Phi_{\gamma}(f)$. $^{2}$

We are using Theorem D.3.3.7(3) to deduce that the bounded subsets of $\mathcal{S}_I(G)$ are indeed contained in some $\mathcal{S}_I(k, G)$, the pre-image under the linear topological isomorphism $\mathcal{S}_I(G) \simeq \mathcal{S}_I(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1)$ of $\mathcal{S}_I(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(k, G^1) \simeq \mathcal{S}_I(G/k)$.

We now return to continuity of $\Phi_{\gamma,0}$. The elementary Lie group $G/(\gamma^{\mathbf{Z}} \cdot k)$ is now compact Hausdorff, and the Hausdorff locally convex topology on $\mathcal{S}(G/(\gamma^{\mathbf{Z}} \cdot k))$ is now equivalent to the topology of uniform convergence on smooth functions and their derivatives of arbitrary order along any continuous, equivalently smooth, 1-parameter subgroup.

In this special case, the proof of continuity of $\Phi_{\gamma,0}$ then proceeds in close analogy with the proof of Lemma 4.2.1.5(1) and (2), using uniform differentiability of the elements of $\mathcal{S}(G/k)$.

We now return to the case of a general $\mathbf{R}_{>0}$-modulated Hausdorff locally compact abelian group $G$.

To show that the closed subspace $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \subset \mathcal{S}_{\mathrm{E}}(G)$ is sent by $\Phi_{\gamma}$ onto a closed subspace of $\mathcal{S}(G/\gamma^{\mathbf{Z}})$, we proceed as follows.

We define on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ the following operator:

$$
\Psi_{\chi} : \mathcal{S}(G/\gamma^{\mathbf{Z}}) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})
$$

assigned by $\Psi_{\chi}(f)(x) := \int_{G^1} \chi(g) f(gx) \, \mathrm{d}\mu_1(g)$ as functions of $x \in G$, invariant under $\gamma^{\mathbf{Z}}$.

---

$^{2}$Return here.

## PDF page 201

**4.5. PERIODIC SCHAUDER BASES IN THE ABSENCE OF MULTIPLICITY** · **201**

We define the operator $\Psi_{\gamma} : \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$, as:

$$
\tag{4.5.1.6}
\Psi_{\gamma}(\phi)(x) := \sum_{k \in \mathbf{Z}} \phi(\gamma^k x)
$$

as functions of $x \in G$, invariant under the action of $\gamma^{\mathbf{Z}}$.

The following diagram of linear operators:

(4.5.1.7)

```latex
\begin{tikzcd}
\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \subset \mathcal{S}_{\mathrm{E}}(G) \arrow[r, "\Phi_{\gamma}"] \arrow[d, "\Phi_{\chi|_{G^1}}"'] & \mathcal{S}(G/\gamma^{\mathbf{Z}}) \arrow[d, "\Psi_{\chi}"] \\
\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r, "\Psi_{\gamma}"'] & \mathcal{S}(G/\gamma^{\mathbf{Z}})
\end{tikzcd}
```

is commutative, where $\Phi_{\chi|_{G^1}}$ is the operator:

$$
\tag{4.5.1.8}
\Phi_{\chi|_{G^1}} : f \mapsto \int_{G^1} \chi(g) f(gx) \, \mathrm{d}\mu_1(g)
$$

and where the closed subspace $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$ is mapped linearly and topologically isomorphically onto $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ by $\Phi_{\chi|_{G^1}}$, by Lemma 4.3.3.1 (up to multiplication by $\mu_1(G^1)$) since $G^1$ is compact and its left-translation action on $\mathcal{S}_{\mathrm{E}}(G)$ is uniformly continuous (see Lemma D.2.2.1).

The same argument as for Lemma 4.3.3.1 and Lemma D.2.2.1, using completeness of $\mathcal{S}(G/\gamma^{\mathbf{Z}})$, compactness of $G^1$, and uniform continuity of its action by left-translation on $\mathcal{S}_{\mathrm{E}}(G)$, and hence on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ by left translation on the left cosets, shows that $\Psi_{\chi}$ is indeed valued in $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ and has closed range (because its square is the multiplication operator by $\mu_1(G^1)$), which, by commutativity of the diagram in (4.5.1.7), shows that so is the linear image under $\Phi_{\gamma}$ of $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$, so long as we show that $\Phi_{\gamma}$ in the topmost horizontal arrow is surjective. The surjectivity assertion was shown in the foregoing and holds by compactness of $G/\gamma^{\mathbf{Z}}$, which finishes the proof of (1).

(2) and (3) : The operator $\Phi_{\gamma,\chi}$ is the composition of the two operators $\Phi_{\chi|_{G^1}}$ from (4.5.1.8), and $\Phi_{\gamma}$ from (4.5.1.1), which, by (1), is continuous.

The former is, by Lemma 4.3.3.1, being $G^1$ compact Hausdorff and $\mathcal{S}_{\mathrm{E}}(G)$ a complete, bornological Hausdorff locally convex topological $\mathbf{C}$-vector space by Lemma D.3.1.2 and Theorem D.3.3.7(1) (and since the right-translation action of $G^1$ on $\mathcal{S}_{\mathrm{E}}(G)$ is uniformly sequentially continuous by Proposition D.1.9.2 and Proposition D.3.3.12), a continuous endomorphism of $\mathcal{S}_{\mathrm{E}}(G)$ with closed range.

Its range is the closed subspace $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \simeq \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ of the Hausdorff locally convex topological $\mathbf{C}$-vector space of exponentially decaying Schwartz-Bruhat functions on $G$ that are $\chi|_{G^1}$-homogeneous with respect to the left-translation action by $G^1$.

By Theorem D.3.3.7(1), $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$ is linearly and topologically isomorphic to $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ under pullback along the chosen continuous homomorphic section $\tau$ to the module $|\cdot|_G$. In particular, it is a Fréchet space.

By commutation of the diagram from (4.5.1.7) and since $\Phi_{\chi|_{G^1}}$ has closed range by Lemma 4.3.3.1, and it is therefore relatively open, then in order to show that $\Phi_{\chi,\gamma}$ is relatively open, it is enough to show that $\Psi_{\gamma}$ is relatively open. It has closed range by (1), and since $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ is a strict LF-space, so is any of its closed subspaces. $\Psi_{\gamma}$ is therefore relatively open by Köthe's Open Mapping Theorem (see [Gro-f, Ch.4,§5,Thm.2(1),p.148], and [SN, §2,Cor.3,p.8]).

(4) : The kernel $\ker(\Phi_{\chi,\gamma}) \subset \mathcal{S}_{\mathrm{E}}(G)$, a closed subspace by (1), contains the closure $V_{\chi,\gamma}$ of the linear subspace generated by the elements $\phi(x)-\phi(\gamma x)$ as $\phi$ varies over all the elements of $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$, i.e. all exponentially decaying Schwartz-Bruhat functions on $G$ that are $\chi|_{G^1}$-homogeneous with respect to the left-translation action by $G^1$.

## PDF page 202

**202** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

The Mellin transform $M \circ \Phi_{\chi|_{G^1}} : \mathcal{S}_{\mathrm{E}}(G) \to A\mathcal{S}(\mathbf{C})$ (see Discussion 4.4.1.1, choosing $\pi = \gamma^{-1}$), sends $V_{\chi,\gamma} \subset \mathcal{S}_{\mathrm{E}}(G)$ (up to multiplication by the reciprocal of the $\mu_1$-volume of $G^1$. Compare with Lemma 4.3.3.1) injectively onto the closed subspace $(1-\chi(\gamma)|\gamma|_G^{-s})A\mathcal{S}(\mathbf{C})$ (by the Asymptotic Residue Theorem, Theorem B.3.2.1, from which it follows that it is sequentially closed, hence closed, being $A\mathcal{S}(\mathbf{C})$ a Fréchet space by Lemma D.3.1.2).

It follows that the orthogonal to $(1-\chi(\gamma)|\gamma|_G^{-s})A\mathcal{S}(\mathbf{C})$ with respect to the duality $\langle A\mathcal{S}(\mathbf{C}), A\mathcal{S}(\mathbf{C})'_{\beta} \rangle$ is linearly and topologically generated by the continuous point-evaluation functionals supported at the points of the complex $s$-plane $\left\{ \frac{2\pi i m}{\log(\gamma)} - it_0(\chi), m \in \mathbf{Z} \right\}$, and these continuous functionals form a topologically free countable set, as is seen by repeating the argument for Theorem 7.1.4.2(2) and (3) (i.e. using the Asymptotic Residue Theorem and boundedness over the vertical strips of bounded width of the complex $s$-plane, away from $i\mathbf{R}$, of the reciprocal of $1-\chi(\gamma)|\gamma|_G^{-s}$, to show the existence of a bi-orthogonal sequence, for then deducing topological freeness from [Jar, Part II,Ch.14,§14.1,Prop.1,p.289]).

Such functionals are, each respectively, the image of the continuous linear functionals sending $\phi \in \mathcal{S}(G/\gamma^{\mathbf{Z}})$ to $a_{\chi,m}(\phi)$, the functional $a_{\chi,m}(\cdot)$ being defined in (4.4.2.6) of Lemma 4.4.2.6, and hence, being the latter set of functionals an unconditional Schauder basic sequence within $\mathcal{S}(G/\gamma^{\mathbf{Z}})'_{\beta}$ by Lemma 4.4.2.6, the continuous linear map:

$$
\mathcal{S}(G/\gamma^{\mathbf{Z}})'_{\beta} \to (\mathcal{S}_{\mathrm{E}}(G/V_{\chi,\gamma})'_{\beta}
$$

which is the continuous adjoint of $\Phi_{\gamma}$, restricts to an injective continuous linear operator from the closure $W_{\chi,\gamma}$ of the set $\{e'_{\xi}, \xi \in (\gamma^{\mathbf{Z}})_{\chi} \subset (\gamma^{\mathbf{Z}})^{\perp}\}$ from (4.5.1.10).

By (1), we know that $\Phi_{\gamma} : \mathcal{S}_{\mathrm{E}}(G) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ is itself continuous, and sends the closed subspace $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \subset \mathcal{S}_{\mathrm{E}}(G)$ onto a closed subspace of $\mathcal{S}(G/\gamma^{\mathbf{Z}})$.

By reflexivity of both source of $\Phi_{\gamma}$ (which is the quotient of $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$, which is linearly and topologically isomorphic to $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ by Proposition D.3.3.12, by $V_{\chi,\gamma}$. Its reflexivity is seen from [Scha, Ch.III,§7,Thm.7.4,p.103], since $V_{\chi,\gamma}$ is closed and hence $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))/V_{\chi,\gamma}$ is nuclear Fréchet, hence Montel, hence reflexive) and target (which is the closed image of $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$ under $\Phi_{\gamma}$ in $\mathcal{S}(G/\gamma^{\mathbf{Z}})$), in order to show that $\Phi_{\gamma}$ is injective it is enough to show that so is $\Phi''_{\gamma}$, and by [NB, Thm.8.10.6(e)] this is indeed the case, since, by the foregoing, a topologically free set of strong (hence weak) topological generators for $(\mathcal{S}_{\mathrm{E}}(G)/V_{\chi,\gamma})'$, is in the image of $\Phi'_{\gamma}$.

The continuous linear operator $\Phi_{\gamma} : \mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))/V_{\chi,\gamma} \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ is therefore injective. It is also surjective onto its linear image, and relatively open by (3), hence a linear topological isomorphism onto its image.

This proves the assertions on $E_{\gamma}(\chi|_{G^1})$ being an absolute Schauder basis for $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))/V_{\chi,\gamma} \simeq \mathcal{S}_{\mathrm{E}}(G)/\ker(\Phi_{\chi,\gamma})$.

(5) : (4) and its proof give more: the set $\{e'_{\xi} : \xi \in (\gamma^{\mathbf{Z}})^{\perp}\} \subset \mathcal{S}(G/\gamma^{\mathbf{Z}})'_{\beta}$ is an unconditional Schauder basis by Lemma 4.4.2.6, and by (4) (and its argument) it is mapped under $\Phi'_{\gamma}$ onto a strongly topologically free set of weak topological generators of the continuous dual of the quotient $\mathcal{S}_{\mathrm{E}}(G)/V_{\gamma}$, with $V_{\gamma}$ the closure of the linear subspace of $\mathcal{S}_{\mathrm{E}}(G)$ linearly generated by the elements $\phi(x)-\phi(\gamma x)$ as $\phi$ varies over all the elements $\phi \in \mathcal{S}_{\mathrm{E}}(G)$.

To see this, we proceed as follows. We observe that by (4), the bi-orthogonal set to $\{e_{\xi} : \xi \in (\gamma^{\mathbf{Z}})^{\perp}_{\chi}\}$ can be chosen to be contained within $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$ (a consequence of Lemma 4.3.3.1 applied to the operator $\Phi_{\chi} : \mathcal{S}_{\mathrm{E}}(G) \to \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, $\Phi_{\chi}(\phi) := \int_{G^1} \chi(g)\phi(gx) \, \mathrm{d}\mu_1(g)$, by compactness of $G^1$).

It follows that $\{e'_{\xi} : \xi \in (\gamma^{\mathbf{Z}})^{\perp}\}$ is indeed topologically free by [Jar, Part II,Ch.14,§14.1,Prop.1,p.289], because each subset $\{e'_{\xi} : \xi \in (\gamma^{\mathbf{Z}})^{\perp}_{\chi}\}$ is, and we have $\Phi_{\chi_1}(\mathrm{H}^0(\chi_2|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))) = 0$ if $\chi_1 \ne \chi_2$, for $\chi_1, \chi_2 \in \widetilde{G^1}$.

We deduce that the continuous linear operator $\mathcal{S}(G/\gamma^{\mathbf{Z}})'_{\beta} \to (\mathcal{S}_{\mathrm{E}}(G)/V_{\gamma})'_{\beta}$ is injective.

## PDF page 203

**4.5. PERIODIC SCHAUDER BASES IN THE ABSENCE OF MULTIPLICITY** · **203**

Its range is weakly dense. Indeed, $\bigoplus_{\chi \in \widetilde{G^1}} \mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \subset \mathcal{S}_{\mathrm{E}}(G)$ is strongly dense, and hence so is its image under the open quotient map onto $\mathcal{S}_{\mathrm{E}}(G)/V_{\gamma}$. This implies that $\bigcap_{\chi \in \widetilde{G^1}} \ker(\Phi_{\chi})$ is trivial in $\mathcal{S}_{\mathrm{E}}(G)$ (alternatively, this is so by Fourier Inversion, since each element of $\bigcap_{\chi \in \widetilde{G^1}} \ker(\Phi_{\chi})$ has everywhere vanishing Fourier transform), and so $\{e'_{\xi} : \xi \in (\gamma^{\mathbf{Z}})^{\perp}\}$ separates the points of $\mathcal{S}_{\mathrm{E}}(G)/V_{\gamma}$, because each $\{e'_{\xi} : \xi \in (\gamma^{\mathbf{Z}})^{\perp}_{\chi}\}$ separates the points of $\mathcal{S}_{\mathrm{E}}(G)/V_{\chi,\gamma}$.

To conclude, we now use Theorem D.3.3.7(3).

By [NB, Thm.8.10.6(e)] applied to $\Phi'_{\gamma}$ and using semi-reflexivity of source and target, $\Phi_{\gamma} : \mathcal{S}_{\mathrm{E}}(G)/V_{\gamma} \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ is injective. Since $\Phi_{\gamma}$ is surjective, it is a continuous bijection. Its linear inverse sends bounded subsets to bounded subsets by Theorem D.3.3.7(3), because $\mathcal{S}_{\mathrm{E}}(G)$ is strict LF and $\Phi_{\gamma}$ is therefore open (and $V_{\gamma}$ is closed since its intersection with each $\mathcal{S}_{\mathrm{E}}(k, G)$ is closed for each $k \subset G^1$ compact with compactly generated $k^{\perp}$).

This implies that $\Phi_{\gamma} : \mathcal{S}_{\mathrm{E}}(G)/V_{\gamma} \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ is a linear topological isomorphism.

(6) : The range of $P_{\gamma}$ is $\ker(\Phi_{\gamma})$, which is closed, since $\Phi_{\gamma}$ from (4.5.1.1) is continuous.

We let $\Phi_{\chi} : \mathcal{S}_{\mathrm{E}}(G) \to \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ be the continuous operator $\Phi_{\chi}(\phi) := \int_{G^1} \chi(g)\phi(gx) \, \mathrm{d}\mu_1(g)$. $\Phi_{\chi}$ is surjective by Lemma 4.3.3.1 and induces a linear topological isomorphism $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \simeq \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, up to multiplication by the nonzero real number $\mu_1(G^1)$, with $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \simeq \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ the closed subspace of those Schwartz-Bruhat functions on $G$ with exponential decay, that are $\chi|_{G^1}$-homogeneous with respect to the continuous left-translation action by $G^1$.

We have $\Phi_{\chi,\gamma} = \Phi_{\gamma} \circ \Phi_{\chi}$, and since the $\gamma^{\mathbf{Z}}$-action and the $G^1$-action by left-translation on $\mathcal{S}_{\mathrm{E}}(G)$ commute, we have $P_{\gamma} \circ \Phi_{\chi} = \Phi_{\chi} \circ P_{\gamma}$ (upon identifying the range of $\Phi_{\chi}$ with the closed subspace $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G)) \subset \mathcal{S}_{\mathrm{E}}(G)$).

In particular, the range of $P_{\gamma} \circ \Phi_{\chi} = \Phi_{\chi} \circ P_{\gamma}$ is the intersection of $\ker(\Phi_{\gamma})$ with $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$, which equals the intersection of $\ker(\Phi_{\chi,\gamma})$ and $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$. In particular, it is again a closed subspace of $\mathcal{S}_{\mathrm{E}}(G)$ and of $\mathrm{H}^0(\chi|_{G^1}, \mathcal{S}_{\mathrm{E}}(G))$, equivalently of $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$. $\square$

REMARK 4.5.1.4. We note that in the proof of (5), we do not need to know that $\mathcal{S}_{\mathrm{E}}(G)$ is bornological, which is indeed the case under the second-countability assumption on $G$ that is being made from Situation 4.4.2.3.

Recall that the canonical continuous linear operator $\mathcal{S}_I(\mathbf{R}_{>0}) \bar{\otimes} \mathcal{S}(G^1) \to \mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$ is a continuous bijection. In particular, the $\gamma^{\mathbf{Z}}$-periodization operator $\Phi_{\gamma}$ induces a linear operator $\Phi_{\gamma} : \mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$, which is surjective.

It is also sequentially continuous, and the induced continuous linear bijection $\mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)/\ker(\Phi_{\gamma}) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ has sequentially continuous linear inverse, because so does the continuous linear bijection $\mathcal{S}_I(G) \to \mathcal{S}_I(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$, as an application of Proposition C.2.3.11.

Since $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ is bornological, [NB, Thm.13.2.7(a)] then applies.

COROLLARY 4.5.1.5 (Boundedness and equicontinuity). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. We adopt the assumptions and choices from Situation 4.4.2.3.*

*Then for each $\chi \in \widetilde{G^1}$, the set of representatives in $\widehat{G}$ chosen in Situation 4.4.2.3 for the continuous characters of $G^1$, then the set $\{a_{\chi,m}(\cdot)\}_{m \in \mathbf{Z}}$ from (4.4.2.6) is bounded in $\mathcal{S}(G/\gamma^{\mathbf{Z}})'_{\beta}$, and bounded and equicontinuous in $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})'_{\beta} \subset \mathcal{S}(G/\gamma^{\mathbf{Z}})$, where $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$ is the closed subspace of $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ of those elements that are $\chi|_{G^1}$-homogeneous under the continuous left-translation action by $G^1$ on the left cosets.*

PROOF. By Proposition 4.5.1.1(3), the continuous linear operator $\Phi_{\chi,\gamma} : \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \to \mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$ is surjective and open, with $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$ is the closed range of the continuous linear operator $\Psi_{\chi} : \mathcal{S}(G/\gamma^{\mathbf{Z}}) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ defined by $\Psi_{\chi}(\phi)(x) := \frac{1}{\mu_1(G^1)} \int_{G^1} \chi(g)\phi(gx) \, \mathrm{d}\mu_1(g)$ (its continuity, surjectivity onto the closed subspace of the $\chi|_{G^1}$-homogeneous elements in $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ under the continuous left-translation action by $G^1$ on the left cosets, is seen as a consequence of Lemma 4.3.3.1).

## PDF page 204

**204** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

By [Kothe-II, Ch.7,§33.3,(6),p.15] applied to $\Phi_{\chi,\gamma}$, its continuous adjoint $\Phi'_{\chi,\gamma} : \mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})'_{\gamma} \to \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})'_{\gamma}$ is a linear topological embedding (with respect to the topology of uniform convergence on the precompact subsets of $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$). Since both source and target are nuclear, by [Tre, Part III,Ch.50,Prop.50.2(50.12,p.519] we deduce that $\Phi'_{\chi,\gamma} : \mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})'_{\beta} \to \mathcal{S}(G)(\chi|_{G^1})'_{\beta}$ is a linear topological embedding.

The boundedness assertion follows from simple boundedness of $\{a_{\chi,m}(\cdot)\}_{m \in \mathbf{Z}}$, which is seen by means of the same argument provided in the proof of Corollary 4.2.1.7, using the Mellin transform and Theorem D.3.3.13.

By [Scha, Ch.III,§3.4,Corollary,p.82], since $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$ is complete, every simply bounded subset in $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})'$ is bounded in the strong topology, and by [Scha, Ch.III,§4.2,Thm.p.83], which applies since $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$ is barrelled (being, by Proposition 4.5.1.1(1), a quotient of a strict LF-space, or by [Bru, §9,Prop.11(a),p.61]) it is equicontinuous.

Its image in $\mathcal{S}(G/\gamma^{\mathbf{Z}})'_{\beta}$ under the continuous adjoint of $\Psi_{\chi}$ is also bounded. $\square$

4.5.1.2. Exponential system on $\mathcal{S}_{\mathrm{E}}(G)/\ker(\Phi_{\chi,\gamma})$.

NOTATION 4.5.1.1. Let $G$ be an $\mathbf{R}_{>0}$-modulated group satisfying the assumptions from Situation 4.4.2.3. Let $\gamma \in G$ be such that $|\gamma|_G > 1$.

On $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ we find the continuous left-translation action of the compact group $G^1$ on the left cosets, and the operator $\Psi_{\chi} : f \mapsto \frac{1}{\mu_1(G^1)} \int_{G^1} \chi(g)f(gx) \, \mathrm{d}\mu_1(g)$ is a continuous idempotent operator valued in $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ by Lemma 4.3.3.1, whose range is the linear subspace of those elements of $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ that are $\chi|_{G^1}$-homogeneous under such continuous left-translation action.

We denote such subspace by:

$$
\tag{4.5.1.9}
\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})) = \mathrm{Im}(\Psi_{\chi}) \subset \mathcal{S}(G/\gamma^{\mathbf{Z}})
$$

a closed subspace, being $\Psi_{\chi}$ continuous and idempotent.

COROLLARY 4.5.1.6 (Sourcing Periodic Schauder Bases - II). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. We adopt the conditions and choices from Situation 4.4.2.3.*

*Any enumeration of the countable set comprised of the continuous functionals*

$$
\tag{4.5.1.10}
e'_{\xi} : \phi \mapsto \int_G \phi(g)\xi(g) \, \mathrm{d}\mu(g)
$$

*as $\xi \in \widehat{G}$ varies over the countable subset $(\gamma^{\mathbf{Z}})^{\perp}_{\chi} \subset (\gamma^{\mathbf{Z}})^{\perp}$ of those elements of $(\gamma^{\mathbf{Z}})^{\perp}$ such that $\xi|_{G^1} = \chi|_{G^1}$, is an unconditional Schauder basis for the orthogonal of $\ker(\Phi_{\chi,\gamma})$ with respect to the duality $\langle \mathcal{S}_{\mathrm{E}}(G), \mathcal{S}_{\mathrm{E}}(G)' \rangle$, equipped with the strong topology on the dual $(\mathcal{S}_{\mathrm{E}}(G)/\ker(\Phi_{\chi,\gamma}))'$.*

*Its dual basis in $\mathcal{S}_{\mathrm{E}}(G)/\ker(\Phi_{\chi,\gamma})$ is absolute and maps bijectively under the operator $\Phi_{\gamma}$ from (4.5.1.1), onto the subset:*

$$
\tag{4.5.1.11}
E_{\gamma}(\chi|_{G^1}) := \{\bar{\xi} : \xi \in (\gamma^{\mathbf{Z}})^{\perp}_{\chi}\} \subset \mathcal{S}(G/\gamma^{\mathbf{Z}})
$$

*equipped with the induced enumeration.*

PROOF. By Proposition 4.5.1.1(3) and (4), the operator $\Phi_{\chi,\gamma}$ induces a linear topological embedding:

$$
\tag{4.5.1.12}
\Phi_{\chi,\gamma} : \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/\ker(\Phi_{\chi,\gamma}) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})
$$

whose image is the closed subspace $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$ of the elements of $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ that are $\chi|_{G^1}$-homogeneous with respect to the continuous left-translation action of $G^1$ on the left cosets $G/\gamma^{\mathbf{Z}}$.

$E_{\gamma}(\chi|_{G^1})$ is an absolute Schauder basis for $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$ by Lemma 4.4.2.6.

Since $E_{\chi}(\chi|_{G^1})$ is the bi-orthogonal set to the set $\{a_{\chi,m}(\cdot)\}_{(\chi,m) \in \widetilde{G^1} \times \mathbf{Z}}$ defined in (4.4.2.6), to finish the proof it is enough to show that indeed for each $\xi \in (\gamma^{\mathbf{Z}})^{\perp}_{\chi}$ there exists a unique pair $(\chi, m) \in \widetilde{G^1} \times \mathbf{Z}$ such

## PDF page 205

**4.5. PERIODIC SCHAUDER BASES IN THE ABSENCE OF MULTIPLICITY** · **205**

that $\Phi'_{\gamma}(a_{\chi,m}(\cdot)) = e'_{\xi}$. Indeed, each such $\xi$ is uniquely of the form $\chi|\cdot|_G^{\frac{2\pi i m}{\log(|\gamma|_G)}-it_0(\chi)}$, following the notation and choices introduced in Situation 4.4.2.3. $\square$

4.5.2. Periodic Schauder Bases: support conditions in the monogenic case. The following is an analog for general $\mathbf{R}_{>0}$-modulated groups satisfying the assumptions from Situation 4.4.2.3 of Proposition 4.2.2.2.

We let $G$ be an $\mathbf{R}_{>0}$-modulated group satisfying the assumptions made in Situation 4.4.2.3.

For any compact subset $K \subset \mathbf{R}_{>0}$ with non-empty interior, and for any compact subgroup $k \subset G^1$ whose orthogonal $k^{\perp}$ is compactly generated, we denote by $\mathcal{S}_K(k, G) \subset \mathcal{D}(G)$ the linear subspace of those smooth compactly supported functions on $G$ that are $k$-invariant, and whose support is contained in $\tau(K) \cdot G^1 \subset G$.

By [Sch-a, Thm.II,p.66] and [Scha, Ch.II,§6,6.4,p.58] and the definition of the topology on $\mathcal{D}(G)$ in [Bru, §1], the topology induced on $\mathcal{S}_K(k, G)$ by the locally convex inductive limit topology on $\mathcal{D}(G)$ is the topology obtained by transport of structure from the Hausdorff locally convex Fréchet topology of uniform convergence on functions and their derivatives (directional, along arbitrary continuous, equivalently smooth, 1-parameter subgroups) of any order on $\mathcal{D}_Z(P)$ for $P := \tau(\mathbf{R}_{>0}) \cdot G^1/k$, an abelian elementary Lie group since $G^1$ is compact, and $Z \subset P$ the compact subset $\tau(K) \cdot G^1/k$, i.e. the continuous linear inclusion $\mathcal{S}_K(k, G) \subset \mathcal{D}(G)$ is a linear topological embedding.

We further note that under the linear topological isomorphism $\mathcal{S}_{\mathrm{E}}(G) \simeq \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$ from Theorem D.3.3.7(3), for any compact subgroup $k \subset G^1$ with $k^{\perp}$ compactly generated, we have that $\mathcal{S}_K(k, G)$ is mapped linearly and topologically isomorphically onto $\mathcal{D}_K(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(k, G^1)$. To see this, we use nuclearity of $\mathcal{D}_K(\mathbf{R}_{>0})$ (which is [Tre, Part III,Ch.51,Corollary,p.530]) and [Jar, Part III,Ch.16,§16.2,Cor.3,p.348], to deduce that the linear inclusion $\mathcal{D}_K(\mathbf{R}_{>0}) \otimes_{\pi} \mathcal{S}(k, G^1) \to \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \otimes_{\pi} \mathcal{S}(G^1)$ is a linear topological embedding (by Proposition 4.2.2.2(1)), and it remains so upon passage to completions on source and target. The source is $\mathcal{D}_K(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(k, G^1)$ and the target is $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(G^1)$.

We further denote by $\mathcal{D}_K(G) \subset \mathcal{S}_{\mathrm{E}}(G)$ the linear subspace of those Schwartz-Bruhat functions on $G$ of exponential decay, whose support is compact and contained within $\tau(K) \cdot G^1$.

PROPOSITION 4.5.2.1 (Sourcing Periodic Schauder Bases - III). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. We adopt the assumptions and choices from Situation 4.4.2.3.*

*(1) For any compact subgroup $k \subset G^1$ such that $k^{\perp}$ is compactly generated, and for any compact subset $K \subset \mathbf{R}_{>0}$ with non-empty interior, the linear subspace $\mathcal{S}_K(k, G) \subset \mathcal{S}_{\mathrm{E}}(G)$ is closed, and the subspace topology agrees with the topology on $\mathcal{S}_K(k, G)$ obtained by transport of structure from the Hausdorff locally convex Fréchet topology of uniform convergence on functions and their derivatives of any order on $\mathcal{D}_Z(P)$ for $P := \tau(\mathbf{R}_{>0}) \cdot G^1/k$, an abelian elementary Lie group, and $Z \subset P$ the compact subset $\tau(K) \cdot G^1/k$.*

*(2) If $K = b \cdot [1/a, a]$ for $a, b > 0$ real numbers, $a > 1$, and $2\log(a) > \log(|\gamma|_G)$, then the quotient $G \to G/\gamma^{\mathbf{Z}}$ maps $\tau(K) \cdot G^1$ surjectively onto $G/\gamma^{\mathbf{Z}}$.*

*For any compact subgroup $k \subset G^1$ such that $k^{\perp} \subset \widehat{G^1}$ is compactly generated, the induced continuous linear map:*

$$
\tag{4.5.2.1}
\Phi_{\gamma} : \mathcal{S}_K(k, G)/(\ker(\Phi_{\gamma}) \cap \mathcal{S}_K(k, G)) \to \mathcal{S}(G/(\gamma^{\mathbf{Z}} \cdot k))
$$

*is a linear topological isomorphism.*

*(3) Under the assumption on $k$ from (1) and on $K$ from (2), let $\phi$ be an element in the intersection $\ker(\Phi_{\gamma}) \cap \mathcal{S}_K(k, G)$. Then there exists $\psi \in \mathcal{S}_{K_0}(k, G)$ such that:*

*(1) For $A_0 := \max\{ab, a/b\}$, $K_0 \subset \mathbf{R}_{>0}$ is a compact subset contained in $[e^{-A}, e^{A}]$, with $A := |-\log(|\gamma|_G) + \log(A_0)|$.*

*(2) $\psi(x)-\psi(\gamma x) = \phi(x)$ as Schwartz-Bruhat functions of $x \in G$, supported over $K$.*

## PDF page 206

**206** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

PROOF. (1) : The subspace topology on $\mathcal{S}_K(k, G)$ is stronger than the Fréchet topology of uniform convergence on functions and their derivatives of arbitrary order (because it is generated by a larger family of seminorms, equivalently because the seminorms defining the Fréchet topology on $\mathcal{D}_Z(P)$ induce on $\mathcal{S}_K(k, G)$ continuous seminorms).

With respect to the subspace topology, $\mathcal{S}_K(k, G)$ is a sequentially closed subspace, since such topology preserves the support and $k$-invariance conditions upon formation of limits in $\mathcal{S}_{\mathrm{E}}(G)$ of Cauchy sequences of elements in $\mathcal{S}_K(k, G)$, and hence $\mathcal{S}_K(k, G)$ is sequentially closed in $\mathcal{S}_{\mathrm{E}}(G)$.

We note that $\mathcal{S}_K(k, G)$ is contained within the pre-image $\mathcal{S}_{\mathrm{E}}(k, G)$ in $\mathcal{S}_{\mathrm{E}}(G)$ of the closed subspace $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(k, G^1)$ of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1)$ under the linear topological isomorphism from Theorem D.3.3.7(3), where $\mathcal{S}(k, G^1)$ is the closed subspace of those smooth functions on $G^1$ that are $k$-invariant, and indeed $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(k, G^1)$ is a closed subspace of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(G^1)$ by nuclearity of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, which holds by Lemma D.3.2.3(1), and by Proposition C.2.3.13(2).

It is therefore enough to show that $\mathcal{S}_K(k, G)$ is closed as a linear subspace of $\mathcal{S}_{\mathrm{E}}(k, G)$. Since $\mathcal{S}_{\mathrm{E}}(k, G)$ is a Fréchet space by [Jar, Part III,Ch.15,§15.1,Cor.4,p.26], it is sequential, and hence $\mathcal{S}_K(k, G)$ is closed, being sequentially closed within the larger ambient, and since $\mathcal{S}_{\mathrm{E}}(k, G)$ is itself closed within the larger ambient by the foregoing.

(2) : Let $x \in G/\gamma^{\mathbf{Z}}$ be an arbitrary point. The subset

$$
\tau([1, |\gamma|_G)) \cdot G^1 \subset G
$$

tassellates $G$ under the proper and free action of the discrete subgroup $\gamma^{\mathbf{Z}} \subset G$, since $|\gamma|_G^{\mathbf{Z}} \cdot [1, |\gamma|_G) = \mathbf{R}_{>0}$.

Since $2\log(a) > \log(|\gamma|_G)$, there exists $b' \in \mathbf{R}_{>0}$ such that $b' \cdot [1, |\gamma|_G) \subset [1/a, a]$ (for instance, $b' := 1/a$) and hence $(b/a) \cdot [1, |\gamma|_G) \subset K$.

We note that $|\gamma|_G^{\mathbf{Z}} \cdot (b/a) \cdot [1, |\gamma|_G) = (b/a) \cdot |\gamma|_G^{\mathbf{Z}} \cdot [1, |\gamma|_G) = (b/a) \cdot \mathbf{R}_{>0} = \mathbf{R}_{>0}$, and hence there exists $y \in \tau((b/a) \cdot [1, |\gamma|_G)) \cdot G^1 \subset \tau(K) \cdot G^1$ mapping to $x$ under the quotient homomorphism $G \to G/\gamma^{\mathbf{Z}}$.

Under the given assumptions on $K$ and $k$, the continuous linear operator $\mathcal{S}_K(k, G) \to \mathcal{S}(G/(\gamma^{\mathbf{Z}} \cdot k))$ is surjective, hence open by [NB, Thm.14.4.5], being source and target Fréchet spaces.

To see the surjectivity aspect, it is enough to observe that there exists a smooth compactly supported function $u_0 \in \mathcal{D}(G)$ whose support is contained within $\tau(K) \cdot G^1$, and such that $\Phi_{\gamma}(u_0) = 1$ as a continuous function on the compact group $G/\gamma^{\mathbf{Z}}$. It is here that we are using the assumption on $K$. Indeed, under the quotient homomorphism $G \to G/\gamma^{\mathbf{Z}}$, $\tau(K) \cdot G^1$ surjects onto $G/\gamma^{\mathbf{Z}}$. We let $K' \subset K$ be a compact subset with non-empty interior such that $\tau(K') \cdot G^1$ surjects onto $G/\gamma^{\mathbf{Z}}$. We choose $v_0 \in \mathcal{D}(\mathbf{R}_{>0})$ real-valued and nonnegative, supported over $K$ and constant and identically 1 over $K'$.

We call $v := v_0 \otimes 1_{G^1}$, which is an element of $\mathcal{D}(G)$ with support contained in $\tau(K) \cdot G^1$.

Then $\Phi_{\gamma}(v) = \Phi_{|\gamma|_G}(v_0)$, and hence $u_0 := v/\Phi_{|\gamma|_G}(v_0)$ is an example of a smooth compactly supported function on $G$ supported over $\tau(K) \cdot G^1$ and satisfying $\Phi_{\gamma}(u_0) = 1$. It is even $k$-invariant, for $k \subset G^1$ a compact subgroup with compactly generated $k^{\perp}$.

Alternatively, given such $u_0$ with $\Phi_{\gamma}(u_0) = 1$, and upon choosing the volume-1 Haar measure $\mu_k$ on $k$, and the unique Haar measure $\mu_{G^1/k}$ prescribed as per Theorem D.1.2.1 by the choices $\mu_1$ on $G^1$ and $\mu_k$ on $k$, the function on $G$ defined by $u_1(x) := \int_k u_0(g^{-1}x) \, \mathrm{d}\mu_k(g)$ is a smooth compactly supported function on $G$ whose support is contained within $\tau(K) \cdot G^1$, and such that it is $k$-invariant. An application of Dominated Convergence shows that $\Phi_{\gamma}(u_1)(x) = \int_k \Phi_{\gamma}(u_0)(g^{-1}x) \, \mathrm{d}\mu_k(g) = \mu_k(k) = 1$ for all $x \in G$.

It follows that the restriction of $\Phi_{\gamma}$ to $\mathcal{S}_K(k, G)$ also surjects onto $\mathcal{S}(G/(\gamma^{\mathbf{Z}} \cdot k))$.

The operator $\Phi_{\gamma}$ therefore induces a linear topological isomorphism as in (4.5.2.1).

(3) : We refer the reader to Discussion 4.4.1.1 for the notation on the Mellin transform in force below and throughout the rest of the argument.

By Proposition 4.5.1.1(5), there exists $\psi \in \mathcal{S}_{\mathrm{E}}(k, G)$ such that $\psi(x)-\psi(\gamma x) = \phi(x)$ as Schwartz-Bruhat functions on $G$ of exponential decay. To show that $\psi$ is compactly supported if $\phi$ is, and that its support

## PDF page 207

**4.5. PERIODIC SCHAUDER BASES IN THE ABSENCE OF MULTIPLICITY** · **207**

is contained in a compact subset of the form $\tau(K_0) \cdot G^1$ with $K_0 \subset \mathbf{R}_{>0}$ of the desired form, it is enough to repeat the argument for Proposition 4.2.2.2(3): we conclude by the Paley-Wiener Theorem (see [Ru-2, Ch.19,Thm.19.3,p.375], which applies since we have in particular that the function of $t \in \mathbf{R}_{>0}$ defined by $\phi(\tau(t)g)$ is, for each $g \in G^1$, in $L^2((1/A_0, A_0), \mathrm{d}t/t)$ for the stated $A_0$). $\square$

REMARK 4.5.2.2. Note that in the proof of Proposition 4.5.2.1 we are not claiming that $\mathcal{S}_{\mathrm{E}}(G)$ is a sequential space, nor are we claiming that in a strict LF-space, a subspace is closed if and only if its pre-image in each of the spaces in a defining sequence is closed.

In the special case at hand, $\mathcal{S}_K(k, G)$ is already entirely contained within $\mathcal{S}_{\mathrm{E}}(k, G) := \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(k, G^1)$, which is itself linearly and topologically isomorphic to $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(k, G^1)$ since the tensor factors are Fréchet spaces (see Corollary C.2.3.12), and the projective tensor product topology on the latter is equivalent to the subspace topology inherited by $\mathcal{S}_{\mathrm{E}}(G)$. We use [Jar, Part III,Ch.16,§16.2,Cor.3,p.348] and nuclearity of $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, to identify injective and projective tensor topologies; see also Proposition C.2.3.13(2).

We deduce that $\mathcal{S}_{\mathrm{E}}(k, G) := \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0}) \overline{\otimes} \mathcal{S}(k, G^1) \simeq \mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(k, G^1)$ is metrizable, hence sequential, and it therefore suffices to prove sequential closedness of $\mathcal{S}_K(k, G)$ in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})\, \widehat{\otimes}_{\pi} \mathcal{S}(k, G^1)$ to deduce closedness of $\mathcal{S}_K(k, G)$ in $\mathcal{S}_{\mathrm{E}}(k, G)$, and hence in $\mathcal{S}_{\mathrm{E}}(G)$, being $\mathcal{S}_{\mathrm{E}}(k, G)$ a closed subspace of $\mathcal{S}_{\mathrm{E}}(G)$ (since $\mathcal{S}(k, G^1) \subset \mathcal{S}(G^1)$ is).

THEOREM 4.5.2.3 (Sourcing Periodic Schauder Bases - IV). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. We adopt the assumptions and choices from Situation 4.4.2.3. Let $\chi \in \widehat{G}$ be a continuous character. Assume $\chi$ is an element of the set $\widetilde{G^1}$ of representatives of the continuous characters of $G^1$ chosen in Situation 4.4.2.3.*

*For any compact subset $K \subset \mathbf{R}_{>0}$ with non-empty interior, the continuous linear map:*

$$
\tag{4.5.2.2}
\Phi_{\chi,\gamma} : \mathcal{S}_K(G)/(\ker(\Phi_{\chi,\gamma}) \cap \mathcal{S}_K(G)) \to \mathcal{S}_{\mathrm{E}}(G)/\ker(\Phi_{\chi,\gamma})
$$

*induced by the inclusion $\mathcal{S}_K(G) \subset \mathcal{S}_{\mathrm{E}}(G)$, is a linear topological isomorphism, compatible with passage to closed subspaces of $k$-invariant functions, for $k \subset G^1$ a compact subgroup with compactly generated $k^{\perp}$.*

*In particular:*

*(1) the continuous functionals*

$$
e'_{\chi,m} : \phi \mapsto \int_G \phi(g)\chi(g)|g|_G^{\frac{2\pi i m}{\log(|\gamma|_G)}-it_0(\chi)} \, \mathrm{d}\mu(g)
$$

*for $m \in \mathbf{Z}$, defined in (4.5.1.10) from Proposition 4.5.1.1, are an unconditional Schauder basis for the orthogonal of $\ker(\Phi_{\chi,\gamma})$ with respect to the duality $\langle \mathcal{S}_{\mathrm{E}}(G), \mathcal{S}_{\mathrm{E}}(G)' \rangle$, equipped with the strong topology on the dual $(\mathcal{S}_{\mathrm{E}}(G)/\ker(\Phi_{\chi,\gamma}))'$.*

*(2) The bi-orthogonal sequence in $\mathcal{S}_{\mathrm{E}}(G)$ can be chosen to be contained in $\mathcal{S}_K(G)$ for $K = b \cdot [1/a, a]$ and $a, b \in \mathbf{R}_{>0}$ and a satisfying $2\log(a) > \log(|\gamma|_G)$, and its image is an absolute Schauder basis for the quotient $\mathcal{S}_K(G)/(\ker(\Phi_{\chi,\gamma}) \cap \mathcal{S}_K(G))$. Under this assumption on $a, b$, the image of the functionals $e'_{\chi,m}$ are an unconditional Schauder basis for the strong dual of $\mathcal{S}_K(G)/(\ker(\Phi_{\chi,\gamma}) \cap \mathcal{S}_K(G))$.*

PROOF. Since $\chi$ is fixed, there exists a compact subgroup $k \subset G^1$ with $k^{\perp}$ compactly generated, equivalently finitely generated, such that $\chi(k) = 1$, i.e. $\chi \in k^{\perp}$ (this is so, because $G^1$ is compact and second-countable, hence separable, and so $\widehat{G^1}$ is separable and discrete, hence countable, and hence a directed union of its finitely generated abelian subgroups $\Gamma$. We can then choose $\Gamma$ so large as to have $\chi \in \Gamma$, and define $k := \Gamma^{\perp}$ is then closed in $G^1$, hence compact, and we have $k^{\perp} = (\Gamma^{\perp})^{\perp} = \Gamma$ by [DE, Prop.3.6.1(b)]).

All the assertions of the Theorem therefore follow from the combination of the following two assertions: $\Phi_{\gamma}$ induces the linear topological isomorphism in (4.5.2.1) from Proposition 4.5.2.1(2), since $\Phi_{\chi,\gamma}$ factors through the projector $\pi_k : \mathcal{S}_{\mathrm{E}}(G) \to \mathcal{S}_{\mathrm{E}}(k, G)$ defined as $\pi_k(\phi)(x) := \int_k \phi(gx) \, \mathrm{d}\mu_k(g)$ for $\mu_k$ the volume-1 Haar measure on $k$, which respects the closed subspace $\mathcal{S}_K(G)$, sending it onto $\mathcal{S}_K(k, G)$.

## PDF page 208

**208** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

The functionals $e'_{\chi,m}$ from (4.5.1.10) are indeed the image under the continuous adjoint $\Phi'_{\chi,\gamma}$, of the unconditional Schauder basis $E_{\gamma}(\chi|_{G^1})$ from (4.5.1.11) of Corollary 4.5.1.6 (and hence from Lemma 4.4.2.6). They are therefore an unconditional Schauder basis for the strong dual of $\mathcal{S}_K(G)/(\ker(\Phi_{\chi,\gamma}) \cap \mathcal{S}_K(G)) = \mathcal{S}_K(k, G)/(\ker(\Phi_{\chi,\gamma}) \cap \mathcal{S}_K(k, G))$.

Its bi-orthogonal set is an absolute Schauder basis because its image under the linear topological isomorphism from (4.5.2.1) is. $\square$

4.5.3. Monogenic periodization of $I$-exponentially decaying Schwartz-Bruhat functions. We deduce the following two Corollaries to Theorem D.1.7.1 from §D.1.7, the Distributional Poisson Summation Formula, which will make Theorem 4.6.2.1, Theorem 4.6.1.5 and Lemma 4.4.2.6 applicable:

COROLLARY 4.5.3.1 (Monogenic periodization on $\mathcal{S}_I(G)$). *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is $\mathbf{R}_{>0}$-modulated. Let $\gamma \in G$ be such that $|\gamma|_G > 1$. Assume the choices and assumptions from Situation 4.4.2.3 are in force.*

*Let $I \subset \mathbf{R}$ be a non-empty open connected interval. If $0 \in I$, then the continuous surjective linear operator $\Phi_{\gamma} : \mathcal{S}_{\mathrm{E}}(G) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ from (4.5.1.1) of Proposition 4.5.1.1 factors through a unique continuous surjective linear operator*

$$
\tag{4.5.3.1}
\Phi_{\gamma} : \mathcal{S}_I(G) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})
$$

*making the following diagram of continuous linear operators:*

(4.5.3.2)

```latex
\begin{tikzcd}
\mathcal{S}_I(G) \arrow[r, "\Phi_{\gamma}"] \arrow[d] & \mathcal{S}(G/\gamma^{\mathbf{Z}}) \arrow[d, equal] \\
\mathcal{S}(G) \arrow[r, "\Phi_{\gamma^{\mathbf{Z}}}"'] & \mathcal{S}(G/\gamma^{\mathbf{Z}})
\end{tikzcd}
```

*where $\mathcal{S}_I(G) \to \mathcal{S}(G)$ is the canonical continuous injective linear operator, and the bottom horizontal arrow is the continuous surjective open linear operator from (D.1.7.2) of Theorem D.1.7.1 applied to $k = \gamma^{\mathbf{Z}}$.*

*Upon denoting*

$$
\tag{4.5.3.3}
P_{\gamma} : \mathcal{S}_I(G) \to \mathcal{S}_I(G), \quad P_{\gamma} : \mathcal{S}(G) \to \mathcal{S}(G)
$$

*the continuous linear operator assigned by $P_{\gamma}(\phi)(x) := \phi(x)-\phi(\gamma x)$, we have:*

*(1) The kernel of $\Phi_{\gamma}$ in $\mathcal{S}_I(G)$ is the closure $V_{I,\gamma}$ of the linear subspace generated by the elements $\phi(x)-\phi(\gamma x)$ as $\phi \in \mathcal{S}_I(G)$ varies over all the elements of $\mathcal{S}_I(G)$, compatibly with passage to $G^1$-isotypes, i.e. $\ker(\Phi_{\gamma}) = P_{\gamma}\mathcal{S}_I(G)$.*

*(2) The kernel of $\Phi_{\gamma^{\mathbf{Z}}} : \mathcal{S}(G) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ from (D.1.7.2) of Theorem D.1.7.1 in the case $k = \gamma^{\mathbf{Z}}$ is the closure $V_{\gamma}$ of the linear subspace generated by the elements $\phi(x)-\phi(\gamma x)$ as $\phi \in \mathcal{S}(G)$ varies over all the elements of $\mathcal{S}(G)$, i.e. $\ker(\Phi_{\gamma^{\mathbf{Z}}}) = P_{\gamma}\mathcal{S}(G)$, compatibly with passage to $G^1$-isotypes.*

PROOF. We define $\Phi_{\gamma} : \mathcal{S}_I(G) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ as the composition of $\Phi_{\gamma} : \mathcal{S}(G) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ with the canonical injective linear operator $\mathcal{S}_I(G) \to \mathcal{S}(G)$, which exists by the assumption $0 \in I$ (see Theorem D.3.3.7(4)).

By Proposition 4.5.1.1(1), $\Phi_{\gamma} : \mathcal{S}_I(G) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ is surjective since $\Phi_{\gamma} : \mathcal{S}_{\mathrm{E}}(G) \to \mathcal{S}(G/\gamma^{\mathbf{Z}})$ is.

It follows that we have continuous linear bijections:

$$
\tag{4.5.3.4}
\mathcal{S}_{\mathrm{E}}(G)/P_{\gamma}\mathcal{S}_{\mathrm{E}}(G) \to \mathcal{S}_I(G)/\ker(\Phi_{\gamma}) \to \mathcal{S}(G)/\ker(\Phi_{\gamma^{\mathbf{Z}}})
$$

where we used Proposition 4.5.1.1(5),(6) to deduce that we have $\ker(\Phi_{\gamma}) = P_{\gamma}\mathcal{S}_{\mathrm{E}}(G)$, and hence $P_{\gamma}\mathcal{S}_I(G) = \mathcal{S}_I(G) \cap V_{\gamma}$ (where the intersection denotes the pre-image of $V_{\gamma}$ along the continuous linear inclusion $\mathcal{S}_I(G) \to \mathcal{S}(G)$).

## PDF page 209

**4.6. PERIODIC SCHAUDER BASES IN THE PRESENCE OF MULTIPLICITY** · **209**

Since we also have continuous linear bijections:

(4.5.3.5)

$$
\mathcal{S}_{\mathrm{E}}(G)/P_{\gamma}\mathcal{S}_{\mathrm{E}}(G)\to\mathcal{S}_I(G)/V_{I,\gamma}\to\mathcal{S}(G)/V_{\gamma}
$$

we deduce that the canonical continuous linear operators:

(4.5.3.6)

$$
\mathcal{S}_I(G)/V_{I,\gamma}\to\mathcal{S}_I(G)/\ker(\Phi_{\gamma}),\ \mathcal{S}(G)/V_{\gamma}\to\mathcal{S}_I(G)/\ker(\Phi_{\gamma^{\mathbf{Z}}})
$$

induced by the inclusions $V_{I,\gamma}\subset\ker(\Phi_{\gamma})\subset\mathcal{S}_I(G)$, and $V_{\gamma}\subset\ker(\Phi_{\gamma^{\mathbf{Z}}})$, are also bijections. This gives $V_{I,\gamma}=\ker(\Phi_{\gamma})$ and $V_{\gamma}=\ker(\Phi_{\gamma^{\mathbf{Z}}})$, as closed subspaces of $\mathcal{S}_I(G)$, respectively $\mathcal{S}(G)$.

Compatibilty of the formation of $V_{I,\gamma}$ and $V_{\gamma}$ with passage to $G^1$-isotypes is a consequence of the commutation of the continuous left-translation actions on $G$ by $\gamma^{\mathbf{Z}}$ and $G^1$. $\square$

**4.6. Periodic Schauder Bases in the presence of multiplicity**

**4.6.1. Bases in the presence of multiplicity.** Throughout this subsection, we use Theorem 4.5.2.3 as an instrument to identify absolute Schauder bases on certain quotients of $\mathcal{S}_{\mathrm{E}}(G)$, for $G$ an $\mathbf{R}_{>0}$-modulated abelian group.

SITUATION 4.6.1.1. Let $G$ be an $\mathbf{R}_{>0}$-modulated group. Assume $G$ is second-countable.

(1) Let $\tau$ be a choice of continuous homomorphic section to the module $\lvert\cdot\rvert_G$.

(2) Let $\mu_1$ be a choice of Haar measure on $G^1$, and $\mu$ the unique Haar measure on $G$ matching the Radon product $\frac{\mathrm{d}t}{t}\otimes\mu_1$ under push-forward along the isomorphism $G\simeq\mathbf{R}_{>0}\times G^1$ of Hausdorff locally compact abelian groups induced by the choice of $\tau$.

(3) Let $N\ge 1$ be an integer, and $\gamma_1,\dots,\gamma_N\in G$ be such that $\lvert\gamma_k\rvert_G>1$ for all $1\le k\le N$. We allow repetitions among the $\gamma_k$'s. We will be writing $S=(\gamma_1,\dots,\gamma_N)$ to mean the ordered list of the $\gamma_k$'s, possibly with repetitions.

(4) We choose, for each continuous character $\omega\in\widehat{G^1}$, a continuous character $\chi\in\widehat{G}$ such that $\chi|_{G^1}$. We denote by $\widetilde{G^1}$ the subset of $\widehat{G}$ given by the chosen continuous characters $\chi$.

(5) We let $k$ be an integer such that $1\le k\le N$, and let $\gamma_k\in G$ be as in (3). We call, for each $\chi\in\widetilde{G^1}$, $x_{0,k}(\chi)\in\mathbf{R}$ the unique real number such that $\chi(\tau(t))=t^{ix_{0,k}(\chi)}$ as smooth functions of $t\in\mathbf{R}_{>0}$ and $t_{0,k}(\chi)\in\mathbf{R}$ the unique real number such that $\chi(\gamma_k)=\lvert\gamma_k\rvert_G^{it_{0,k}(\chi)}$. In particular, $\chi\lvert\cdot\rvert_G^{\frac{-2\pi im}{\log(\lvert\gamma\rvert_G)}-it_{0,k}(\chi)}$ is a parametrization of all the countably many elements of $(\gamma_k^{\mathbf{Z}})^{\perp}$, as $(\chi,m)$ vary over $\widetilde{G^1}\times\mathbf{Z}$.

NOTATION 4.6.1.1. We let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group, and $\gamma\in G$ such that $\lvert\gamma\rvert_G>1$. We record here notation first introduced in Corollary 4.5.1.6, to be used throughout the rest of this section.

We adopt the notation $\widetilde{G^1}$ from Situation 4.4.2.3, for a fixed choice of representatives for the elements of $\widehat{G^1}$, i.e. for each $\omega\in\widehat{G^1}$, one continuous character $\chi\in\widehat{G}$ such that $\chi|_{G^1}=\omega$. This is equivalent to choosing a holomorphic parametrization $\chi\lvert\cdot\rvert_G^s$ for the Riemann surface $\Omega(G)$ of continuous quasi-characters on $G$.

We define, for each $\chi\in\widetilde{G^1}$, the subset:

(4.6.1.1)

$$
(\gamma^{\mathbf{Z}})^{\perp}_{\chi}\subset(\gamma^{\mathbf{Z}})^{\perp}\subset\widehat{G}
$$

to be the subset of those continuous characters $\xi\in\widehat{G}$ such that $\xi(\gamma^{\mathbf{Z}})=1$, equivalently $\xi(\gamma)=1$, and such that $\xi|_{G^1}=\chi|_{G^1}$.

REMARK 4.6.1.2. Let $G$ be a second-countable $\mathbf{R}_{>0}$-modulated group.

Since $G^1$ is compact, $\widehat{G^1}$ is discrete by [DE, Prop.3.1.5(a)].

We note that since $G$ is second-countable, so is $G^1$, and hence $\widehat{G^1}$ is countable, and it is therefore the directed union of its finitely generated abelian subgroups, each of which is therefore open, closed, discrete. Finitely generated and compactly generated are equivalent conditions on the subgroups of $\widehat{G^1}$.

## PDF page 210

**210** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

For each $\eta\in\widehat{G^1}$, there therefore exists a large enough finitely generated subgroup $\Gamma\subset\widehat{G^1}$ containing the character $\eta$. We define $k:=\Gamma^{\perp}\subset G^1$. Since orthogonals of closed subgroups are closed subgroups (see [DE, Ch.3,§3.6,p.78]. For $\Gamma\subset\widehat{G}$, we have

$$
\Gamma^{\perp}=\{x\in G:\chi(x)=1,\ \text{for all}\ \chi\in\Gamma\}
$$

and hence $\Gamma^{\perp}$ is the intersection of the closed subgroups $\ker(\chi)$ as $\chi$ varies over all $\chi\in\Gamma$), $k\subset G^1$ is closed, hence compact, and $\eta(k)=1$, i.e. $\eta\in k^{\perp}$ (since $k^{\perp}=\Gamma$ by [DE, Prop.3.6.1(b)]).

In particular, for each $\chi\in\widetilde{G^1}$, there exists a compact subgroup $k\subset G^1$ with finitely generated orthogonal $k^{\perp}$ such that $\chi(k)=1$. This implies that we have:

(4.6.1.2)

$$
(\gamma^{\mathbf{Z}})^{\perp}_{\chi}\subset(\gamma^{\mathbf{Z}}\cdot k)^{\perp}
$$

for such $\chi$.

*4.6.1.1. Polygenic periodization and absolute bases in the presence of multiplicity.*

LEMMA 4.6.1.3. *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. Assume the conditions and choices of Situation 4.6.1.1 are in force.*

*Let $\gamma_1,\dots,\gamma_N\in G$ be such that $\lvert\gamma_k\rvert_G>1$ for all $1\le k\le N$.*

Let $\chi\in\widetilde{G^1}$ be a continuous character. Let $S_0:=(\gamma_1,\dots,\gamma_{N-1})$.

(1) The operator

(4.6.1.3)

$$
P_{S_0}:\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\to\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

*defined as the continuous linear endomorphism assigned by the composition $P_{S_0}:=\prod_{1\le k\le N-1}P_{\gamma_k}$, where $P_{\gamma_k}$ is defined by the assignment:*

(4.6.1.4)

$$
P_{\gamma_k}(\phi)(g):=\phi(x)-\phi(\gamma_k x)
$$

*on any $\phi\in\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, as functions of $x\in G$, has closed range.*

(2) The quotient

(4.6.1.5)

$$
\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_0}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

is a separable nuclear Fréchet space.

(3) The operator

(4.6.1.6)

$$
P_{\gamma_N}:\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\to\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

induces a linear topological isomorphism:

(4.6.1.7)

$$
Q:\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_0}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\to P_{\gamma_N}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_0\cup\{\gamma_N\}}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

*where both source and target are separable nuclear Fréchet space, compatibly with the continuous left-translation actions of $G$ on source and target.*

PROOF. (1) : This is a consequence of Proposition 4.5.1.1(4).

(2) : $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ is a nuclear Fréchet space by Proposition D.3.3.12 (it is linearly and topologically isomorphic to $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, which is a nuclear Fréchet space by Lemma D.3.2.3(1)).

Since $P_{S_0}$ has closed range in $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ by (1), the subquotient in (4.6.1.5) is also a Fréchet space, nuclear by [Scha, Ch.III,§7.4,p.103].

(3) : The operator $P_{\gamma_N}$ from (4.6.1.6) followed by the quotient, induces a surjective continuous linear operator

(4.6.1.8)

$$
Q:\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\to P_{\gamma_N}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_0\cup\{\gamma_N\}}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

## PDF page 211

**4.6. PERIODIC SCHAUDER BASES IN THE PRESENCE OF MULTIPLICITY** · **211**

which is open by [NB, Thm.14.4.5], being source and target Fréchet spaces. To show that $\ker(Q)=P_{S_0}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, we proceed as follows. Assume $\phi\in\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, is such that $P_{\gamma_N}(\phi)\in P_{S_0\cup\{\gamma_N\}}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$.

Then

$$
\widetilde{M}(P_{\gamma_N}(\phi))(\chi\lvert\cdot\rvert_G^s)=(1-\chi(\gamma_N)\lvert\gamma_N\rvert_G^{-s})\widetilde{M}(\phi))(\chi\lvert\cdot\rvert_G^s)
$$

as entire functions on the complex $s$-plane and elements of $A\mathcal{S}(\mathbf{C})$. We refer the reader to Discussion 4.4.1.1, for the definition of $\widetilde{M}(\phi)(\chi\lvert\cdot\rvert_G^s)=\int_{\mathbf{R}_{>0}}t^{s+ix_0(\chi)}\int_{G^1}\chi(g)\phi(gx)\,\mathrm{d}\mu_1(g)\frac{\mathrm{d}t}{t}$.

Since $P_{\gamma_N}(\phi)\in P_{S_0\cup\{\gamma_N\}}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, we have:

(4.6.1.9)

$$
(1-\chi(\gamma_N)\lvert\gamma_N\rvert_G^{-s})\widetilde{M}(\phi))(\chi\lvert\cdot\rvert_G^s)=\prod_{1\le k\le N}(1-\chi(\gamma_k)\lvert\gamma_k\rvert_G^{-s})\widetilde{M}(\psi)(\chi\lvert\cdot\rvert_G^s)
$$

for some $\psi\in\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$.

By the Asymptotic Residue Theorem (see Theorem B.3.2.1), which applies because the meromorphic function $(1-\chi(\gamma_N)\lvert\gamma_N\rvert_G^{-s})^{-1}$ is periodic and with slow growth near its poles, which are all located within the vertical line $i\mathbf{R}$ of the complex $s$-plane, and since $\widetilde{M}$ factors through $M$ as per (4.4.1.3) from Discussion 4.4.1.1, and $M$ is a linear topological isomorphism by Theorem D.3.3.13, we deduce that we have $\phi=P_{S_0}(\psi)$, i.e. $\phi\in P_{S_0}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ (here we use Lemma 4.3.3.1 to identify $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, with the closed subspace $\mathrm{H}^0(\chi|_{G^1},\mathcal{S}_{\mathrm{E}}(G))$ of the exponentially decaying Schwartz-Bruhat functions on $G$ that are $\chi|_{G^1}$-homogeneous with respect to the continuous left-translation action by $G^1$, under the continuous linear operator $\phi\mapsto\frac{1}{\mu_1(G^1)}\int_{G^1}\chi(g)\phi(gx)\,\mathrm{d}\mu_1(g)$)

It follows that the operator $Q$ from (4.6.1.8) induces a linear topological isomorphism:

(4.6.1.10)

$$
\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_0}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\to P_{\gamma_N}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_0\cup\{\gamma_N\}}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

which is the operator from (4.6.1.7). $\square$

LEMMA 4.6.1.4. *Let $N\ge 1$ be an integer, and $b_1,\dots,b_N\in\mathbf{R}_{>0}$ real numbers. Assume $b_k>1$ for each $1\le k\le N$.*

*The following conditions on the set $\{b_1,\dots,b_N\}$ are equivalent:*

(1) *There exists $b\in\mathbf{R}_{>0}$ with $b>1$ and $b_k\in\mathbf{Q}\cdot\log(b)$ for all $1\le k\le N$.*

(2) *The set of nonzero complex numbers:*

(4.6.1.11)

$$
\{b_k^{\frac{2\pi im}{\log(b_h)}},1\le k,h\le N,m\in\mathbf{Z}\}
$$

is finite.

PROOF. Assume $\{b_k\}_{1\le k\le N}\subset\mathbf{Q}\cdot\log(b)$ for some $b\in\mathbf{R}_{>0}$ with $b>1$. Then $\log(b_k)=c_k\cdot\log(b)$ for each $1\le k\le N$, for rational numbers $c_k\in\mathbf{Q}$, $c_k\ne 0$.

We have, for each $1\le k\le N$, $b_k=b^{c_k}$, and hence:

$$
b_k^{\frac{2\pi im}{\log(b_h)}}=b^{\frac{2\pi im}{c_h\cdot\log(b)}c_k}=e^{\frac{2\pi imc_k}{c_h}}
$$

where $c_k/c_h$ is a nonzero rational number. Since for each $1\le k\le N$, there is a unique $c_k\in\mathbf{Q}$ such that $\log(b_k)=c_k\cdot\log(b)$, the set $F:=\{c_k/c_h,1\le h,k\le N\}$ is a finite subset of $\mathbf{Q}$.

It follows that we have $\mathbf{Z}(1)\cdot F\subset(1/M)\mathbf{Z}(1)$ for a large enough integer $M\ge 1$, and hence $\exp(\mathbf{Z}(1)\cdot F)$ is a finite set. It follows that so is the set of nonzero complex numbers in (4.6.1.11).

Conversely, if the set in (4.6.1.11) is finite, then, upon calling $F'$ the finite set $F':=\{\frac{\log(b_k)}{\log(b_h)},1\le h,k\le N\}\subset\mathbf{R}$, then $\exp(\mathbf{Z}(1)\cdot F')$ is a finite set.

For each $c\in F'$, $\exp(\mathbf{Z}(1)\cdot c)$ is a finite subgroup of $\mathrm{U}(1)$, which forces $\mathbf{Z}(1)\cdot c\subset(1/M_c)\mathbf{Z}(1)$ for an integer $M_c\ge 1$. It follows that $c$ is a nonzero rational number, and hence $F'\subset\mathbf{Q}$.

We define $b$ to be the any of the $b_k$'s, for instance one that minimizes their absolute value, and we have $\log(b_k)\in\mathbf{Q}\cdot\log(b)$ for each $1\le k\le N$. $\square$

## PDF page 212

**212** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

We now use Lemma 4.6.1.3 and Theorem 4.5.2.3 to prove the existence of absolute Schauder bases on the subquotients:

$$
\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

with $S = (\gamma_1,\dots,\gamma_N)$ for $N \ge 1$ an integer, and, for each $1 \le k \le N$, for $\gamma_k \in G$ such that $\lvert\gamma_k\rvert_G > 1$. We define $b_k := \log(\lvert\gamma_k\rvert_G)$ for each $1 \le k \le N$.

We will be assuming that the logarithms of the real numbers $b_k$, for $1 \le k \le N$, $\mathbf{Q}$-linearly generate a 1-dimensional $\mathbf{Q}$-linear subspace of $\mathbf{R}$.

THEOREM 4.6.1.5 (Sourcing Periodic Schauder Bases - V). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. Assume the conditions and choices from Situation 4.6.1.1 are in force. We denote by $S$ the finite set $S := (\gamma_1,\dots,\gamma_N)$. We define $b_k := \log(\lvert\gamma_k\rvert_G)$ for each $1 \le k \le N$.*

*Assume that there exists a real number $b \in \mathbf{R}_{>1}$ such that $\log(b_k) \in \mathbf{Q}\cdot\log(b)$ for every $1 \le k \le N$.*

*Let $\chi \in \widetilde{G^1}$ be a continuous character. We define the discrete subset:*

$$
\mathcal{U}_{G,S}(\chi) := \bigcup_{1\le k\le N}(\gamma_k^{\mathbf{Z}})_{\chi}^{\perp} \tag{4.6.1.12}
$$

*contained within the connected component of the Riemann surface $\Omega(G)$ parametrized by the continuous character $\chi|_{G^1}$. We define on $\mathcal{U}_{G,S}(\chi)$ the multiplicity function $N : \mathcal{U}_{G,S}(\chi) \to \mathbf{N}$:*

$$
N(\xi) := \sum_{1\le k\le N}1_{(\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}}(\xi). \tag{4.6.1.13}
$$

*For any element $\xi \in \mathcal{U}_{G,S}(\chi)$, we write, for $k$ any integer such that $1 \le k \le N$ and $\xi \in (\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$, $n_{\xi,k}$ for the unique integer such that we have $\xi = \chi\lvert\cdot\rvert_G^{\frac{2\pi i n_{\xi,k}}{\log(b_k)}-it_{0,k}(\chi)}$.*

*We define, for each $\xi \in \bigcup_{1\le k\le N}(\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$ and each integer $0 \le m \le N(\xi)-1$, the continuous functional:*

$$
D_{\xi,m} : \phi \mapsto \int_G \phi(g)\xi(g)(\log\lvert g\rvert_G)^m\,\mathrm{d}\mu(g) \tag{4.6.1.14}
$$

*on $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$.*

*The countable set*

$$
E_S(\chi|_{G^1}) := \{D_{\xi,m} : \xi \in \bigcup_{1\le k\le N}(\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}, 0 \le m \le N(\xi)-1\} \subset \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})'_{\beta} \tag{4.6.1.15}
$$

*is contained in $(\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}))'_{\beta}$ and any of its enumerations is an unconditional Schauder basis for $(\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}))'_{\beta}$, whose bi-orthogonal set*

$$
\{\psi_{\xi,m} : \xi \in \bigcup_{1\le k\le N}(\gamma_k^{\mathbf{Z}})^{\perp}, 0 \le m \le N(\xi)-1\} \subset \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \tag{4.6.1.16}
$$

*equipped with the induced enumeration, is an absolute Schauder basis.*

*It further satisfies the following conditions:*

*(1) Let $q$ be any continuous seminorm on $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$. Then there exists a polynomial $p \in \mathbf{C}[X]$ depending on $q$, such that, for any choice of integer $k$ such that $1 \le k \le N$ and $\xi \in (\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$:*

$$
q(\psi_{\xi,m}) \ll_{q,k} p(n_{\xi,k}) \tag{4.6.1.17}
$$

*uniformly with respect to $0 \le m \le N(\xi)-1$, as $\lvert n_{\xi,k}\rvert \to +\infty$.*

*(2) For any $\phi \in \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, for any fixed integer $0 \le m \le N-1$, and for any choice of integer $k$ such that $1 \le k \le N$ and such that at least an element $\xi$ of $(\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$ satisfies $N(\xi) \ge m$, the function $\xi \mapsto D_{\xi,m}(\phi)$ as a function of the integer $n_{\xi,k}$ as $\xi$ varies over the elements of $(\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$ of multiplicity at least $m$, is an element of $\mathcal{S}(\mathbf{Z})$.*

## PDF page 213

**4.6. PERIODIC SCHAUDER BASES IN THE PRESENCE OF MULTIPLICITY** · **213**

PROOF. We first construct a bi-orthogonal set to $E_S(\chi|_{G^1})$. We proceed as in the proof of Theorem 7.1.4.2.

We choose $\phi \in A\mathcal{S}(\mathbf{C})$ such that $\phi(z_m) \ne 0$ for all $m \in \mathbf{Z}$, with $z_m := \frac{2\pi i m}{\log(b_k)}-it_{0,k}(\chi)$ with $1 \le k \le N$ any $k$ such that $\chi\lvert\cdot\rvert_G^{z_m} \in (\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$.

We define:

$$
L_{G,S,\phi}(s) := \prod_{1\le k\le N}(1-\chi(\gamma_k)\lvert\gamma_k\rvert_G^{-s})\phi(s) \tag{4.6.1.18}
$$

an entire function with zeros at the zeros of $\prod_{1\le k\le N}(1-\chi(\gamma_k)\lvert\gamma_k\rvert_G^{-s})$, with exactly the same multiplicities (and possibly other zeros elsewhere).

We have

$$
\frac{\partial^j}{\partial s^j}\prod_{1\le k\le N}(1-\chi(\gamma_k)\lvert\gamma_k\rvert_G^{-s}) = \sum_{k_1+\dots+k_N=j}\frac{j!}{k_1!\cdots k_N!}\prod_{1\le k\le N}\partial_s^{k_r}(1-\chi(\gamma_k)\lvert\gamma_k\rvert_G^{-s})
$$

and since $\partial_s^{k_r}(1-\chi(\gamma_k)\lvert\gamma_k\rvert_G^{-s}) = (-1)^{k_r-1}\chi(\gamma_k)(\log\lvert\gamma_k\rvert_G)^{k_r}\lvert\gamma_k\rvert_G^{-s}$ is bounded on vertical strips of bounded width within the complex $s$-plane, we deduce that both $\prod_{1\le k\le N}(1-\chi(\gamma_k)\lvert\gamma_k\rvert_G^{-s})$ and its holomorphic derivatives of any order, are bounded uniformly over each vertical strip of bounded width of the complex $s$-plane.

It follows that $L_{G,S,\phi}$ is an element of $A\mathcal{S}(\mathbf{C})$. We fix an integer $m \in \mathbf{Z}$, and an integer $0 \le j \le N(\chi\lvert\cdot\rvert_G^{z_m})-1$. We have implicitly chosen an integer $1 \le k \le N$ such that $\chi\lvert\cdot\rvert_G^{z_m} \in (\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$.

We define the function:

$$
\lambda_{(\chi,m),j}(s) := \frac{1}{(s-z_m)^j}L_{G,S,\phi}(s) \tag{4.6.1.19}
$$

a meromorphic function with only one removable singularity at $s = z_m$, which is a zero of order $N(\chi\lvert\cdot\rvert_G^{z_m})-j$. Moreover, since the meromorphic function $\frac{s^M}{(s-z_m)^j}$ of $s \in \mathbf{C}$ has, for any integer $M \ge 0$, slow growth near its poles in the sense of Definition B.3.1.1, the Asymptotic Residue Theorem (see Theorem B.3.2.1) applied to it, upon integrating over two vertical lines bounding a large enough open vertical strip of bounded width containing $i\mathbf{R}$ in its interior, implies that the unique analytic continuation of $\lambda_{(\chi,m),j}$ to an entire function on the complex $s$-plane, which we also denote by $\phi_{(\chi,m),j}$, is Schwartz uniformly over the non-empty open vertical strips of bounded width of the complex $s$-plane, i.e. an element of $A\mathcal{S}(\mathbf{C})$.

There therefore exists a unique $\phi_{(\chi,m),j} \in \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ such that $\widetilde{M}(\phi_{(\chi,m),j})(\chi\lvert\cdot\rvert_G^s) = \lambda_{(\chi,m),j}(s)$, where $\widetilde{M}$ is the Mellin transform operator $\mathcal{S}_{\mathrm{E}}(G) \to A\mathcal{S}(\mathbf{C})$ defined as $\phi \mapsto \int_G \phi(g)\chi(g)\lvert g\rvert_G^s\,\mathrm{d}\mu(g)$ (see Discussion 4.4.1.1).

We note that we have $D_{\chi\lvert\cdot\rvert_G^{z_m},j'}(\phi_{(\chi,m),j}) \ne 0$ for all integers

$$
N(\chi\lvert\cdot\rvert_G^{z_m})-j \le j' \le N(\chi\lvert\cdot\rvert_G^{z_m})-1
$$

and $D_{\chi\lvert\cdot\rvert_G^{z_m},j}(\phi_{(\chi,m'),j'}) = 0$ otherwise.

This implies that a bi-orthogonal set to the set $E_S(\chi|_{G^1})$ exists, and, for each fixed $m \in \mathbf{Z}$, the unique element in $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ on which the value of $D_{\xi,m}$ is $1$, is the image of an element of $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ obtained as a finite $\mathbf{C}$-linear combination of the finitely many elements $\phi_{(\chi,m),j}$ only, as $j$ varies over the integers $1 \le j \le N(\xi)$.

Explicitly, we solve the $N(\xi) \times N(\xi)$ linear system, for $\xi = \chi\lvert\cdot\rvert_G^{z_m}$:

$$
\sum_{1\le j_0\le N(\xi)}c_{j_0,j}\cdot D_{\xi,j}(\phi_{(\chi,m),j_0}) = 1 \tag{4.6.1.20}
$$

$$
\sum_{1\le j_0\le N(\xi)}c_{j_0,j}\cdot D_{\xi,h}(\phi_{(\chi,m),j_0}) = 0,\quad 0 \le h \le N(\xi)-1, h \ne j. \tag{4.6.1.21}
$$

## PDF page 214

**214** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

To see that this system indeed has a solution, we observe that the system is triangular. On the diagonal, we find the complex numbers $D_{\xi,N(\xi)-j_0}(\phi_{(\chi,m),j_0})$, all nonzero for each $1 \le j_0 \le N(\xi)$, and hence the system has a unique solution $(c_{1,j},\dots,c_{N(\xi),j})$ (for instance, for $j = N(\xi)-1$, since $D_{\xi,N(\xi)-1}(\phi_{(\chi,m),1}) \ne 0$ and $D_{\xi,j'}(\phi_{(\chi,m),1}) = 0$ for all $0 \le j' \le N(\xi)-2$, we obtain $c_{1,N(\xi)-1} = 1/D_{\xi,N(\xi)-1}(\phi_{(\chi,m),1})$. The other coefficients $c_{2,N(\xi)-1},\dots,c_{N(\xi),N(\xi)-1}$ are uniquely determined by the remaining $N(\xi)-1$ equations. We therefore have and $\psi_{\xi,N(\xi)-1} := \sum_{1\le j_0\le N(\xi)}c_{j_0,N(\xi)-1}\cdot \phi_{(\chi,m),j_0}$, and it is such that $D_{\xi,N(\xi)-1}(\psi_{\xi,N(\xi)-1}) = 1$, and $D_{\xi,j}(\psi_{\xi,N(\xi)-1}) = 0$ for all $0 \le j \le N(\xi)-2$).

We choose $N = 2$ and discuss this special case first. In particular, we have $S = (\gamma_1,\gamma_2)$. We consider the following diagram whose top and middle rows are short linearly-exact sequences:

(4.6.1.22)

```latex
\begin{tikzcd}
P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{(\gamma_1,\gamma_2)}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] \arrow[d, "P_{\gamma_1}^{-1}"'] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{(\gamma_1,\gamma_2)}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] \arrow[d, equal] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[d, equal] \\
\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_2}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r, "P_{\gamma_1}"] \arrow[d, "\Phi_{\chi,\gamma_2}"'] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{(\gamma_1,\gamma_2)}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[d, "\Phi_{\chi,\gamma_1}"] \\
\mathcal{S}_{\chi}(G/\gamma_2^{\mathbf{Z}}) &  & \mathcal{S}_{\chi}(G/\gamma_1^{\mathbf{Z}})
\end{tikzcd}
```

We note that in fact the top and middle rows are topologically exact: the leftmost spaces are closed subspaces under the respective linear inclusions, and $P_{\gamma_1}^{-1}$ denotes the inverse linear topological isomorphism $Q$ from (4.6.1.7) provided by Lemma 4.6.1.3.

The leftmost horizontal arrow in the middle row of (4.6.1.22) is the linear topological isomorphism $Q$ from (4.6.1.7) of Lemma 4.6.1.3, followed by the continuous inclusion of $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{(\gamma_1,\gamma_2)}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ into $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{(\gamma_1,\gamma_2)}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, which is the leftmost horizontal arrow in (4.6.1.22): the former has closed range so long as the former does.

We note that the quotient topology and the subspace topology on $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{(\gamma_1,\gamma_2)}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ are equivalent by [NB, Thm.14.4.5(b)], since $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{(\gamma_1,\gamma_2)}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ is closed with respect to the subspace topology, hence a Fréchet space with respect to such topology, and it is a Fréchet space with respect to the quotient topology, both assertions following from Lemma 4.6.1.3(2).

The closed subspace $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$, for $\gamma \in G$ such that $\lvert\gamma\rvert_G > 1$, is the closed range of the continuous operator $\Psi_{\chi} : \phi \mapsto \frac{1}{\mu_1(G^1)}\int_{G^1}\chi(g)\phi(gx)\,\mathrm{d}\mu_1(g)$ as functions of $x \in G/\gamma^{\mathbf{Z}}$, where the continuous action of $G^1$ is by left-translation on the left $\gamma^{\mathbf{Z}}$-cosets (compare with the proof of Proposition 4.5.1.1(1), and note that indeed $\Psi_{\chi}$ is valued in $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ because the left-translation action by $G^1$ on $\mathcal{S}(G/\gamma^{\mathbf{Z}})$ is uniformly continuous, in the sense of Lemma 4.3.3.1, and the Lemma applies. $\mathcal{S}_{\chi}(G/\gamma^{\mathbf{Z}})$ agrees with the closed subspace of the $\chi|_{G^1}$-homogeneous elements under such continuous left-translation action by $G^1$).

We now define the subset:

$$
E_{S/\gamma_1}(\chi|_{G^1}) := \{D_{\xi,0} : \xi \in (\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}-(\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}\} \cup \{D_{\xi,1} : \xi \in (\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}\cap(\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}\} \subset \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})'_{\beta} \tag{4.6.1.23}
$$

and we observe that $E_{S/\gamma_1}(\chi|_{G^1})$ is contained in the closed range of the continuous adjoint of the quotient $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, and maps injectively into the strong dual of $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$.

This implies that the subset of the set in (4.6.1.16):

$$
F_{S/\gamma_1}(\chi|_{G^1}) := \{\psi_{\xi,0} : \xi \in (\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}-(\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}\} \cup \{\psi_{\xi,1} : \xi \in (\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}\cap(\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}\} \subset \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \tag{4.6.1.24}
$$

is, modulo $P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, contained in $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$. In fact, the very design of each $\psi_{\xi,m}$ ensures that $F_{S/\gamma_1}(\chi|_{G^1})$ is itself contained within $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ (i.e. not merely modulo $P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$).

Indeed, the construction of each $\psi_{\xi,m}$ exhibits $\psi_{\xi,m}$ as a finite linear combination of the $\phi_{(\chi,n_{\xi}),k}$'s for $N(\xi)-m \le k \le N(\xi)$. In particular, each $\psi_{\chi,m}$ in the subset $F_{S/\gamma_1}$, is such that its Mellin transform

## PDF page 215

**4.6. PERIODIC SCHAUDER BASES IN THE PRESENCE OF MULTIPLICITY** · **215**

$\widetilde{M}(\psi_{\xi,m})(\chi\lvert\cdot\rvert_G^s)$ is divisible by $1-\chi(\gamma_1)\lvert\gamma_1\rvert_G^{-s}$, and hence, since $M : \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \to A\mathcal{S}(\mathbf{C})$ is a linear topological isomorphism by Theorem D.3.3.13 and in light of the relation between $M$ and $\widetilde{M}$ explained in Discussion 4.4.1.1, we deduce that we have $F_{S/\gamma_1}(\chi|_{G^1}) \subset P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$.

For each $\xi \in (\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}$, there exists a unique $m \in \mathbf{Z}$ such that $\xi = \chi\lvert\cdot\rvert_G^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}-it_0(\chi)}$. We consider the functional $a_{\chi,m}$ from (4.4.2.6), which, recall, was defined as:

$$
a_{\chi,m}(\phi) := \frac{1}{\log(\lvert\gamma_2\rvert_G)\mu_1(G^1)}\int_{G/\gamma^{\mathbf{Z}}}\phi(g)\chi(g)\lvert g\rvert_G^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}-it_0(\chi)}\,\mathrm{d}\bar{\mu}_{\gamma_2}(g)
$$

for $\phi$ the arbitrary element in $\mathcal{S}(G/\gamma_2^{\mathbf{Z}})$, and $\bar{\mu}_{\gamma_2}$ is the unique Haar measure on $G/\gamma_2^{\mathbf{Z}}$ prescribed as per Theorem D.1.2.1 by the choice of $\mu$ on $G$ and the counting measure on the discrete closed subgroup $\gamma_2^{\mathbf{Z}} \subset G$.

Assume $\xi \in (\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}\cap(\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}$. Then, by L'Hospital's Rule, the image of $a_{\chi,m}(\cdot)$ under the continuous adjoint of the composition $P_{\gamma_1}^{-1}\circ\Phi_{\chi,\gamma_1}$, is the continuous functional on $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ which is the restriction to $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ of the continuous functional $-\frac{1}{\log(\lvert\gamma_1\rvert_G)}D_{\xi,1}$ in $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})'_{\beta}$, for $\xi = \chi\lvert\cdot\rvert_G^{\frac{2\pi i m}{\log(\lvert\gamma_1\rvert_G)}-it_0(\chi)}$.

If $\xi \in (\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}-(\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}$, then the image of $a_{\chi,m}$ is the continuous functional:

$$
\frac{1}{1-\chi(\gamma_1)\lvert\gamma_1\rvert_G^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}-it_{0,2}(\chi)}}D_{\xi,0}
$$

where $t_{0,1}(\chi) \in \mathbf{R}$ is the unique real number in $[0,\frac{2\pi}{\log(\lvert\gamma_1\rvert_G)})$ such that $\chi(\gamma_1)\lvert\gamma_1\rvert^{-it_{0,1}(\chi)} = 1$, and similarly for $t_{0,2}(\chi)$, for $\xi = \chi\lvert\cdot\rvert_G^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}-it_{0,2}(\chi)}$.

It follows from Lemma 4.4.2.6, that the image of $F_{S/\gamma_1}(\chi|_{G^1})$ in the quotient $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ is an absolute Schauder basis within its closure (because for each $\psi_{\xi,m}$, there exists a nonzero complex number $c_{\xi,m}$ such that $c_{\xi,m}\cdot\psi_{\xi,m}$ maps under the linear topological isomorphism $\Phi_{\chi,\gamma_1}\circ P_{\gamma_1}^{-1}$ to the absolute Schauder basis $e_{\chi,m}$ from (4.4.2.5)).

By Lemma 4.4.2.6, the countable subset:

$$
F_{\gamma_1}(\chi|_{G^1}) := \{\psi_{\xi,0} : \xi \in (\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}\} \subset \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

endowed with an arbitrary choice of enumeration, maps under the composition of the quotient $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, followed by $\Phi_{\chi,\gamma_1}$ to an absolute Schauder basis in $\mathcal{S}_{\chi}(G/\gamma_1^{\mathbf{Z}})$ (which, as a set, is the bi-orthogonal set to the set of functionals $a_{\chi,m}$ from (4.4.2.6) of Lemma 4.4.2.6, for $\psi_{\xi,0}$ mapping to the unique element $\psi$ such that, for $\xi = \chi\lvert\cdot\rvert_G^{\frac{2\pi i m}{\log(\lvert\gamma_1\rvert_G)}-it_{0,1}(\chi)}$, $a_{\chi,m}(\psi) = 1$ and $a_{\chi,m'}(\psi) = 0$ for all integers $m' \ne m$) and hence it maps to an absolute Schauder basis in $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, since $\Phi_{\chi,\gamma_1}$ is a linear topological isomorphism.

Since $\log(b_1),\log(b_2) \in \mathbf{Q}\cdot\log(b)$ for a real number $b > 1$, the set of complex numbers:

$$
\{\lvert\gamma_1\rvert^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}}\}_{m\in\mathbf{Z}} \tag{4.6.1.25}
$$

is finite by Lemma 4.6.1.4.

As a consequence, the following set of nonzero complex numbers:

$$
\left\{\frac{1}{1-\chi(\gamma_1)\lvert\gamma_1\rvert^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}-it_{0,2}(\chi)}}\right\}_{m\in A} \tag{4.6.1.26}
$$

is also finite, where $A \subset \mathbf{Z}$ is the countable subset of those integers such that $1-\chi(\gamma_1)\lvert\gamma_1\rvert^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}-it_{0,2}(\chi)}$ is nonzero, equivalently those integers such that $\chi\lvert\cdot\rvert_G^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}-it_{0,2}(\chi)} \in (\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}-(\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}$.

It follows that each continuous functional $a_{\chi,m}(\cdot) \in \mathcal{S}_{\chi}(G/\gamma_2^{\mathbf{Z}})'_{\beta}$ is mapped by the continuous adjoint $(P_{\gamma_1}^{-1}\circ\Phi_{\chi,\gamma_1})'$ of $P_{\gamma_1}^{-1}\circ\Phi_{\chi,\gamma_1}$ to $c_{\xi,h}\cdot D_{\xi,h}$ where $h$ is either $0$ or $1$, and where $c_{\xi,1} := -\frac{1}{\log(b_1)}$, and $c_{\xi,0}$ is an element

## PDF page 216

**216** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

of the finite set of nonzero complex numbers from (4.6.1.26), depending on whether $\xi = \chi\lvert\cdot\rvert_G^{\frac{2\pi i m}{\log(\lvert\gamma_2\rvert_G)}-it_{0,2}(\chi)}$ is either in $(\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}\cap(\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}$, or in $(\gamma_1^{\mathbf{Z}})_{\chi}^{\perp}-(\gamma_2^{\mathbf{Z}})_{\chi}^{\perp}$.

For every continuous seminorm $q$ on $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, its restriction to the closed subspace $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ is also a continuous seminorm on such subspace, and since $\Phi_{\chi,\gamma_2}\circ P_{\gamma_1}^{-1}$ is a linear topological isomorphism, and the set in (4.6.1.25) is finite, we can maximize the implied constants provided by Lemma 4.4.2.6 over it, to incorporate the finitely many values of the multiplicative constants $c_{\xi,h}$, obtaining from Lemma 4.4.2.6(2) that for each $\psi_{\xi,m} \in F_{S/\gamma_1}(\chi|_{G^1})$, and denoting by $\psi_{\xi,m}$ also its image in the quotient $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, there exists a polynomial $p \in \mathbf{C}[X]$ depending on $q$ such that the estimate:

$$
q(\psi_{\xi,m}) \ll_q p(n_{\xi,k}) \tag{4.6.1.27}
$$

as $\lvert n_{\xi,k}\rvert \to +\infty$, for $n_{\xi,k}$ the unique integer such that $\xi = \chi\lvert\cdot\rvert_G^{\frac{2\pi i n_{\xi,k}}{\log(\lvert\gamma_k\rvert_G)}-it_{0,k}(\chi)}$, $k = 1,2$.

Changing the choice of $k$ such that $\xi \in (\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$, changes $n_{\xi,k}$ by a single integer translator (since the set of zeros of $1-\chi(\gamma_k)b_k^{s-it_{0,k}(\chi)}$ is a torsor under the action by vertical translation by $\frac{2\pi i\mathbf{Z}}{\log(b_k)}$), and up to rendering the implied constant (4.6.1.27) dependent on $k$ (by enlarging it at most $N$ times, which in this special case $N = 2$ means at most twice), the estimate in (4.6.1.27) holds for any such choice of $k$.

We further obtain that the sequence of coefficients $D_{\xi,m}(\phi)$ is of rapid decay as a function of $n_{\xi,k}$, for each $\phi \in \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, and hence it remains so upon changing the choice of $k$ such that $\xi \in (\gamma_k^{\mathbf{Z}})_{\chi}^{\perp}$, and so it is also when renormalized by a sequence valued in the set of any of the finitely many nonzero complex numbers from (4.6.1.26).

In particular, (1) and (2) hold for the image in $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ of the countable set $F_{S/\gamma_1}(\chi|_{G^1})$.

For any choice of enumeration of the countable set $F_{S/\gamma_1}(\chi|_{G^1})$ from (4.6.1.24), the finite rank continuous operators on $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ defined as:

$$
P_M := \sum_{0\le k\le M}D_{\xi_k,m_k}\cdot\psi_{\xi_k,m_k}
$$

converge pointwise on $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$: indeed, for any $\phi \in \mathcal{S}_{\mathrm{E}}(G)$, $D_{\xi_k,m_k}(\phi)$ is a sequence of rapid decay, since the integers $m_k$ are at most finitely many, and the at most $N$ holomorphic derivatives of the Mellin transform $\widetilde{M}(\phi)(\chi\lvert\cdot\rvert_G^s)$ are Schwartz uniformly on every vertical strip of bounded width of the complex $s$-plane, and hence in particular their values on the points $\xi_k = \chi\lvert\cdot\rvert_G^{\frac{2\pi i n_k}{\log(b_{h_k})}-it_{0,h_k}(\chi)}$ decay rapidly.

Using (4.6.1.27), applied to the restriction to the closed subspace

$$
P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \subset \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

of an arbitrary continuous seminorm $q$ on $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, we obtain that the sums:

$$
\sum_{0\le k\le M}\lvert D_{\xi_k,m_k}(\phi)\rvert\cdot q(\psi_{\xi_k,m_k})
$$

converge as $M \to +\infty$, for each $\phi \in \mathcal{S}_{\mathrm{E}}(G)$, and hence in particular the sequence $\{P_M\}_{M\ge 1}$ converges pointwise on the Fréchet space

$$
\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}).
$$

The pointwise limit $P$ is therefore a linear idempotent operator on $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ valued in $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$.

By [Ru-3, Part I,Ch.2,Thm.2.8,p.46], a form of the Uniform Boundedness Principle for Fréchet spaces, which applies since $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ is a Fréchet space, $P$ is continuous.

## PDF page 217

**4.6. PERIODIC SCHAUDER BASES IN THE PRESENCE OF MULTIPLICITY** · **217**

Since $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \subset \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ is therefore linearly and topologically complemented, with $\ker(P)$ linearly and topologically isomorphic to $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, we deduce that the image in $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ of the union of $F_{S/\gamma_1}(\chi|_{G^1})$ and $F_{\gamma_1}(\chi|_{G^1})$ in $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, is an absolute Schauder basis, satisfying (1) and (2).

It follows that its bi-orthogonal sequence, which, as a set, is the set $E_S(\chi|_{G^1})$ from (4.6.1.15), is an unconditional Schauder basis for the strong dual of $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$.

This finishes the proof in the special case $S = (\gamma_1,\gamma_2)$.

We now discuss the case of general $N \ge 1$. We define $S_1 := (\gamma_2,\dots,\gamma_N) \subset S$.

The following diagram of continuous linear maps:

(4.6.1.28)

```latex
\begin{tikzcd}
P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] \arrow[d, "P_{\gamma_1}^{-1}"'] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] \arrow[d, equal] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[d, equal] \\
\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r, "P_{\gamma_1}"] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
\end{tikzcd}
```

has topologically exact rows, and $P_{\gamma_1}^{-1}$ is the inverse of the linear topological isomorphism $Q$ from (4.6.1.7) provided by Lemma 4.6.1.3 (up to relabelling the elements of $S$).

On both $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ and $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$, the assertions on the images of $E_{(\gamma_1)}(\chi|_{G^1})$, respectively $E_{S_1}(\chi|_{G^1})$, and their respective bi-orthogonal sets, hold by inductive hypothesis.

Moreover, the image of the continuous functionals in $E_{S_1}(\chi|_{G^1})$ under the continuous adjoint of $P_{\gamma_1}$, is itself a Schauder basic sequence and a subset of $E_S(\chi|_{G^1})$ up to renormalizing each element by a sequence of nonzero complex numbers which again takes values in a finite set of complex numbers of the form $(\log(b_k))^r$ for integers $2 \le k \le N$, and $0 \le r \le N$, or special values of $(1-\chi(\gamma_1)\lvert\gamma_1\rvert_G^s)$ at imaginary numbers of the form $\frac{2\pi i m}{\log(b_k)}-it_{0,k}(\chi)$ for $2 \le k \le N$ and for integers $m \in \mathbf{Z}$ such that the resulting special value of $(1-\chi(\gamma_1)\lvert\gamma_1\rvert_G^s)$ is nonzero: this set of complex numbers is finite, by another application of Lemma 4.6.1.4.

In particular, upon changing the implied constants, the estimate in (4.6.1.17) is inherited by the elements of the set in (4.6.1.16) from the analogous estimate for $S_1$ in place of $S$ and $(\gamma_1)$ in place of $S$, respectively, both of which hold by inductive hypothesis.

To assemble the resulting basic sequence in $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ and $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ into the desired basic sequence, we repeat the argument for the construction of a continuous projector onto the former closed subspace, resting on the Uniform Boundedness Principle in its form from [Ru-3, Part I,Ch.2,Thm.2.8,p.46].

$\square$

We illustrate Theorem 4.6.1.5 on an example:

EXAMPLE 4.6.1.6. Let $\gamma \in \mathbf{R}_{>0}$ such that $\gamma > 1$. We describe the absolute Schauder basis provided by Theorem 4.6.1.5, in the special case $G = \mathbf{R}_{>0}$, and $S = (\gamma,\gamma)$ with $P_S = P_{\gamma}^2$.

The Mellin transform $\widetilde{M} = M$ (in this special case; see Discussion 4.4.1.1) sends $P_{\gamma}^2\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ onto the closed subspace $(1-\gamma^{-s})^2A\mathcal{S}(\mathbf{C}) \subset A\mathcal{S}(\mathbf{C})$.

The following short exact sequence:

$$
0 \to (1-\gamma^{-s})A\mathcal{S}(\mathbf{C})/(1-\gamma^{-s})^2A\mathcal{S}(\mathbf{C}) \to A\mathcal{S}(\mathbf{C})/(1-\gamma^{-s})^2A\mathcal{S}(\mathbf{C}) \to A\mathcal{S}(\mathbf{C})/(1-\gamma^{-s})A\mathcal{S}(\mathbf{C}) \to 0 \tag{4.6.1.29}
$$

is obtained under Mellin transform from (4.6.1.7) of Lemma 4.6.1.3, applied to $G = \mathbf{R}_{>0}$, $\chi = 1$, $S_0 = (\gamma,\gamma)$ and $\gamma_N = \gamma$.

It is topologically exact, i.e. the leftmost quotient in (4.6.1.29) equipped with the quotient topology, carries the subspace topology.

## PDF page 218

**218** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

The linear topological isomorphism $Q$ provided by Lemma 4.6.1.3 is, in this special case, the linear topological isomorphism:

$$
P_{\gamma}^{-1}:(1-\gamma^{-s})A\mathcal{S}(\mathbf{C})/(1-\gamma^{-s})^2A\mathcal{S}(\mathbf{C})\to A\mathcal{S}(\mathbf{C})/(1-\gamma^{-s})A\mathcal{S}(\mathbf{C}) \tag{4.6.1.30}
$$

and the operator $\Phi_{\gamma}$ from (4.2.1.1) identifies the right side in (4.6.1.30) with $\mathcal{S}(\mathbf{R}_{>0}/\gamma^{\mathbf{Z}})$. This provides an absolute Schauder basis for $A\mathcal{S}(\mathbf{C})/(1-\gamma^{-s})A\mathcal{S}(\mathbf{C})$: the pre-image under $\Phi_{\gamma}$ of the exponential system, and an unconditional Schauder basis for the strong dual $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})/P_{\gamma}\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, as the image of the dual basis under $\Phi_{\gamma}'$.

The pre-image under $P_{\gamma}^{-1}$ from (4.6.1.30) and the image of the dual basis under its continuous adjoint, involves renormalizing the basis elements by the nonzero complex number $\log(\gamma)$ and its reciprocal. Indeed, $P_{\gamma}^{-1}$ sends $\phi\in (1-\gamma^{-s})A\mathcal{S}(\mathbf{C})$ to the unique analytic continuation of $\frac{\phi(s)}{1-\gamma^{-s}}$, an element of $A\mathcal{S}(\mathbf{C})$, and point-evaluation at any $z_m:=\frac{2\pi im}{\log(\gamma)}$ gives, in terms of $\phi$:

$$
\delta_{z_m}\left(\frac{\phi(s)}{1-\gamma^{-s}}\right)=\frac{\phi'(z_m)}{\log(\gamma)\gamma^{-z_m}}=\frac{\phi'(z_m)}{\log(\gamma)}
$$

which is the image of the dual basis element $a_m(\cdot)$ from (4.2.1.4) of Lemma 4.2.1.2 under the composition of $\Phi_{\gamma}'$ and $(P_{\gamma}^{-1})'$.

**4.6.2. Support conditions in the presence of multiplicity.** The following Proposition will allow us to source absolute Schauder bases comprised of compactly supported smooth functions on $G$, with some degree of control on the location of the support.

THEOREM 4.6.2.1 (Sourcing Compactly Supported Absolute Schauder Bases). *Let $G$ be an $\mathbf{R}_{>0}$-modulated group. Assume the conditions and choices from Situation 4.6.1.1 are in force.*

*Let $N\ge 1$ be an integer, and $S=(\gamma_1,\dots,\gamma_N)$ an $N$-tuple of elements of $G$ such that for every integer $1\le k\le N$, we have $\lvert\gamma_k\rvert_G>1$.*

*For each $\chi\in\widetilde{G^1}$, there exists a compact subset $K_S\subset G$ satisfying the following properties:*

(1) $G^1\cdot K_S=K_S$.

(2) $\lvert K_S\rvert_G\subset (0,1)$.

(3) *The continuous linear map:*

$$
\mathcal{S}_{K_S}(G)(\chi|_{G^1})\to\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \tag{4.6.2.1}
$$

*is surjective. In particular, the induced continuous linear map:*

$$
\mathcal{S}_{K_S}(G)(\chi|_{G^1})/(\mathcal{S}_{K_S}(G)(\chi|_{G^1})\cap P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}))\to\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \tag{4.6.2.2}
$$

*is a linear topological isomorphism.*

PROOF. The following diagram:

(4.6.2.3)

```latex
\begin{tikzcd}
P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] \arrow[d, "P_{\gamma_1}^{-1}"'] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] \arrow[d, equal] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[d, equal] \\
\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r, "P_{\gamma_1}"] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \arrow[r] & \mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
\end{tikzcd}
```

of continuous linear operators, with topologically exact rows and where $P_{\gamma_1}^{-1}$ is the inverse of the linear topological isomorphism $Q$ from (4.6.1.7) provided by Lemma 4.6.1.3 (up to relabelling the elements of $S$) enables the following inductive argument.

## PDF page 219

**4.6. PERIODIC SCHAUDER BASES IN THE PRESENCE OF MULTIPLICITY** · **219**

We call $K_{(\gamma_1)}:=\tau([1/b_1',b_1'])\cdot G^1$ for a choice of $b_1'>b_1=\log(\lvert\gamma_1\rvert_G)$, and deduce from Proposition 4.5.2.1(2) and Proposition 4.5.1.1(4) and (6), that the continuous linear map:

$$
\mathcal{S}_{K_{(\gamma_1)}}(G)(\chi|_{G^1})/(P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\cap\mathcal{S}_{K_{(\gamma_1)}}(G)(\chi|_{G^1}))\to\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \tag{4.6.2.4}
$$

is a linear topological isomorphism. By induction on $N\ge 1$, we may and do assume that a compact subset $K_{S_1}\subset G$ exists such that $G^1\cdot K_{S_1}=K_{S_1}$, and such that the continuous linear map:

$$
\mathcal{S}_{K_{S_1}}(G)(\chi|_{G^1})/(P_{S_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\cap\mathcal{S}_{K_{S_1}}(G)(\chi|_{G^1}))\to\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \tag{4.6.2.5}
$$

is a linear topological isomorphism. The linear topological isomorphisms from (4.6.2.5) and from (4.6.2.4) hold upon replacing $K_{(\gamma_1)}$, respectively $K_{S_1}$, with larger compact subsets.

The operator $P_{\gamma_1}$ maps $\mathcal{S}_{K_{S_1}}(G)(\chi|_{G^1})$ into $\mathcal{S}_{K_{S_1}'}(G)(\chi|_{G^1})$ for $K_{S_1}'$ the compact subset $K_{S_1}':=K_{S_1}\cup\bigcup_{2\le k\le N}\gamma_k^{-1}\cdot K_{S_1}$. We therefore define $K_S':=K_{S_1}'\cup K_{(\gamma_1)}$ and replace $K_{(\gamma_1)}$ with $K_S'$.

The linear operator $P_{\gamma_1}^{-1}$ in the leftmost vertical arrow in (4.6.2.3) induces a linear topological isomorphism:

$$
(P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\cap\mathcal{S}_{K_S'}(G)(\chi|_{G^1}))/(P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\cap\mathcal{S}_{K_S'}(G)(\chi|_{G^1}))\to\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})/P_{S_1}\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1}) \tag{4.6.2.6}
$$

because its range contains the image of the linear topological isomorphism from (4.6.2.5), by design of $K_{S_1}'$ and $K_S'$. It follows that (4.6.2.6), is a continuous bijection, and since source and target are Fréchet spaces, it is a linear topological isomorphism by [NB, Thm.14.4.5(b)].

Since all the quotients in (4.6.2.3) are continuous representations under the continuous left-translation action by $G$ on all function spaces and their quotients, we choose $t\in (0,1)$ and call $\gamma^{-1}:=\tau(t)$, and the left-translation action by $\gamma^M$ on $\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$ sends $\mathcal{S}_{K_S'}(G)(\chi|_{G^1})$ linearly and topologically isomorphically onto $\mathcal{S}_{\gamma^M K_S'}(G)(\chi|_{G^1})$, compatibly with the closed subspace $\mathcal{S}_{K_S'}(G)(\chi|_{G^1})\cap P_S\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})$.

We choose $M\ge 1$ large enough so as to have $\gamma^M\cdot K_S'\subset\tau((0,1))\cdot G^1$, and rename this compact subset as $K_S$.

We have shown that $K_S$ satisfies (3).

Since $K_{S_1}$ is $G^1$-stable, as is $K_{(\gamma_1)}$ by construction, so is $K_S$, since the action of $G^1$ by left-translation commutes with the action of $\gamma_k^{\mathbf{Z}}$ for each $2\le k\le N$, and $\gamma^{\mathbf{Z}}$. It follows that $K_S$ satisfies (1) and (2). $\square$

**4.6.3. The case of $\mathcal{S}_I(G)$.**

COROLLARY 4.6.3.1. *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is $\mathbf{R}_{>0}$-modulated. Let $\gamma\in G$ be such that $\lvert\gamma\rvert_G>1$. Assume the choices and assumptions from Situation 4.6.1.1 are in force.*

*Let $I\subset\mathbf{R}$ be a non-empty open connected interval. Assume $0\in I$.*

*Upon denoting $S=(\gamma_1,\dots,\gamma_N)$ for $N\ge 1$ an integer and $\gamma_k\in G$ with $\lvert\gamma_k\rvert_G>1$ for each $1\le k\le N$ as in Situation 4.6.1.1, we write $P_S$ for the composition of the operators $P_{\gamma_k}$ from (4.5.3.3) on $\mathcal{S}_I(G)$ and $\mathcal{S}(G)$.*

*The canonical continuous linear operators:*

$$
\mathcal{S}_{\mathrm{E}}(G)/P_S\mathcal{S}_{\mathrm{E}}(G)\to\mathcal{S}_I(G)/P_S\mathcal{S}_I(G)\to\mathcal{S}(G)/P_S\mathcal{S}(G) \tag{4.6.3.1}
$$

*are linear topological isomorphisms, compatible with passage to $G^1$-isotypes.*

PROOF. We write $S=(\gamma_1)\cup S_0$ with $S_0=(\gamma_2,\dots,\gamma_N)$.

Recall from Situation 4.6.1.1 that the notation $(\gamma_2,\dots,\gamma_N)$ means the set $\{\gamma_2,\dots,\gamma_N\}$ whose elements are counted with multiplicity. For example, for $N=2$ and $\gamma_1=\gamma_2=\gamma$, $P_{(\gamma,\gamma)}=P_{\gamma}^2$ (see Example 4.6.1.6).

## PDF page 220

**220** · **CHAPTER 4. PERIODIC SCHAUDER BASES ON MODULATED GROUPS**

The following commutative diagram of continuous linear operators:

(4.6.3.2)

```latex
\begin{tikzcd}
P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)/P_S\mathcal{S}_{\mathrm{E}}(G) \arrow[r] \arrow[d] & \mathcal{S}_{\mathrm{E}}(G)/P_S\mathcal{S}_{\mathrm{E}}(G) \arrow[r] \arrow[d] & \mathcal{S}_{\mathrm{E}}(G)/P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G) \arrow[d] \\
P_{\gamma_1}\mathcal{S}_I(G)/P_S\mathcal{S}_I(G) \arrow[r] \arrow[d] & \mathcal{S}_I(G)/P_S\mathcal{S}_{\mathrm{E}}(G) \arrow[r] \arrow[d] & \mathcal{S}_I(G)/P_{\gamma_1}\mathcal{S}_I(G) \arrow[d] \\
P_{\gamma_1}\mathcal{S}(G)/P_S\mathcal{S}(G) \arrow[r] & \mathcal{S}(G)/P_S\mathcal{S}(G) \arrow[r] & \mathcal{S}(G)/P_{\gamma_1}\mathcal{S}(G)
\end{tikzcd}
```

is induced by the continuous linear inclusions $\mathcal{S}_{\mathrm{E}}(G)\to\mathcal{S}_I(G)\to\mathcal{S}(G)$ and by the linear topological embeddings $P_{\gamma_1}\mathcal{S}_{\mathrm{E}}(G)\subset\mathcal{S}_{\mathrm{E}}(G)$, $P_{\gamma_1}\mathcal{S}_I(G)\subset\mathcal{S}_I(G)$, and $P_{\gamma_1}\mathcal{S}(G)\subset\mathcal{S}(G)$.

By Corollary 4.5.3.1, the rightmost vertical arrows in (4.6.3.2) are linear topological isomorphisms.

The operators $P_{\gamma_1}$ are continuous and with closed range by Proposition 4.5.1.1(5),(6) and Corollary 4.5.3.1.

Let $E$ be any of the three Hausdorff locally convex topological $\mathbf{C}$-vector spaces $\mathcal{S}_{\mathrm{E}}(G)$, $\mathcal{S}_I(G)$ and $\mathcal{S}(G)$.

Let $\phi\in E$ be such that $P_{\gamma_1}(\phi)\in P_S(E)$. Following the same argument provided in Lemma 4.6.1.3 (applied upon relabelling $\gamma_1$ as $\gamma_N$) shows that we have $\phi\in P_S(E)$, from which we deduce that the leftmost, and hence the middle, vertical arrows are continuous linear bijections, by replacing $S$ with $S_0$ and inducting on the integer $N\ge 1$, and by another application of Corollary 4.5.3.1 to treat the base case of the induction.

To see this, we observe that the canonical continuous linear operator $E\to\prod_{\chi\in\widetilde{G^1}}E(\chi|_{G^1})$, the target being endowed with the product locally convex topology, induced by the operators $\phi\mapsto\int_{G^1}\chi(gx)\phi(x)\,\mathrm{d}\mu_1(g)$ (each continuous and with closed range by an application of Lemma 4.3.3.1) is injective (by Fourier Inversion, since the vanishing of an element of $E$ under $E\to\prod_{\chi\in\widetilde{G^1}}E(\chi|_{G^1})$ implies the vanishing of its Fourier transform, and hence $\phi=0$; see the proof of Proposition 5.2.3.2 for a similar, related argument).

It follows that the continuous surjective linear operator $E/P_{S_0}(E)\to P_{\gamma_1}(E)/P_S(E)$ is also injective, since it is so on $G^1$-isotypes by the same argument from Lemma 4.6.1.3 applied to each $E(\chi|_{G^1})$.

We deduce that the middle vertical arrows in (4.6.3.2) are continuous linear bijections.

Since, by Theorem D.3.3.7(3), the bornological topology on $\mathcal{S}_{\mathrm{E}}(G)$ and $\mathcal{S}_I(G)$ is strict-LF (see Remark D.3.3.11), and since $\mathcal{S}(G)$, and hence $P_S\mathcal{S}(G)$, is itself a strict LF-space, the inverses of the continuous linear bijections which are the middle vertical arrows in (4.6.3.2) are bounded by Köthe's Open Mapping Theorem (see [Gro-f, Ch.4,§5,Thm.2(1),p.148], and [SN, §2,Cor.3,p.8], applied to $E/P_S(E)$ re-topologized with its bornological topology, with respect to which $P_S(E)$ remains closed, since $P_S(E)$ is the kernel of the continuous operators $\Phi_{\gamma}$, which remain continuous upon refinement of the topology of their source).

Since $\mathcal{S}(G)$ is bornological (by [Scha, Ch.II,§8,8.2,Cor.2,p.62]) so are all its quotients by its closed subspaces by [Scha, Ch.II,§8,8.2,Cor.1,p.62], and hence so is $\mathcal{S}(G)/P_S\mathcal{S}(G)$. It follows that the inverses to the continuous linear bijections $\mathcal{S}_{\mathrm{E}}(G)/P_S\mathcal{S}_{\mathrm{E}}(G)\to\mathcal{S}(G)/P_S\mathcal{S}(G)$ and $\mathcal{S}_I(G)/P_S\mathcal{S}_I(G)\to\mathcal{S}(G)/P_S\mathcal{S}(G)$ from (4.6.3.2), both bounded by the foregoing, are linear topological isomorphisms by [NB, Thm.3.2.7(a)].

It follows that the continuous linear bijection $\mathcal{S}_{\mathrm{E}}(G)/P_S\mathcal{S}_{\mathrm{E}}(G)\to\mathcal{S}_I(G)/P_S\mathcal{S}_I(G)$ is also a linear topological isomorphism.

Compatibility with passage to $G^1$-isotypes on source and target follows from commutation of the continuous left-translation actions on $G$ by $\gamma_k^{\mathbf{Z}}$ for each $1\le k\le N$, and $G^1$. $\square$
