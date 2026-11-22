## PDF page 117

**CHAPTER 3**

**Idelic Zeta Functions**

In this Chapter we collect results on how to recover the global idelic Zeta integrals in [CF, Ch.XV,§4] as transforms of functions on the idele class group and on the positive reals, as opposed to integrals of Schwartz-Bruhat functions on the adeles restricted to the idele group.

We will further discuss the $S$-idelic analog of the global idelic Zeta functions from [CF, Ch.XV,§4]. Equivalently, we will be discussing in general, the paradigm envisioned by Riemann in his paper “On the Number of Primes Less Than a Given Magnitude” (for which we refer the reader to [Riemann]) where he used the Jacobi $\theta$-function to prove the functional equation and existence of the analytic continuation to the Riemann Zeta function.

We will be using the global and $S$-local adelic $\theta$-functions constructed in the previous Chapter and whose study we initiated therein, to a similar effect. This Chapter will therefore consist in a reformulation of several of the results contained in Tate's dissertation from [CF, Ch.XV], with a few complements being discussed.

Subsequently, we will be viewing global and $S$-local adelic $\theta$-functions as their own function space, i.e. we will be topologizing the $\mathbf{C}$-linear space of all global adelic $\theta$-functions, and all $S$-local adelic $\theta$-functions, respectively.

The reason for doing this is that certain operators on the spaces of global and $S$-local adelic $\theta$-functions will enable us to read off non-trivial information about the zeros of Hecke $L$-functions through trace formulas. The reader familiar with Selberg's classical trace formula and subsequent refinements will know how powerful trace formulas are. They are a pivotal instrument throughout the literature on automorphic representations and the Langlands program.

Trace calculations will be made accessible to us by promoting each of the spaces of adelic $\theta$-functions to Hausdorff locally convex topological $\mathbf{C}$-vector spaces. The trace calculation that is the subject of this work takes place on Sobolev spaces (hence *normed*) but, leading to the main calculation, finer locally convex topologies are also necessary for reasons that will become clear by Chapter 7. They will give us Schauder bases, which will enable us to compute “large pieces” of the trace that interests us.

This is a good time to anticipate for the reader what “local convexity” does for us: it is a condition on bases of 0-neighborhoods in topological vector spaces leading to robust control on several conditions through the machinery of “duality”. There is, in other words, good reason to appeal to this side of functional analysis, on which profound and expressive literature is available. Those elements that are relevant to us are discussed in Appendix C.

Topologizing the spaces of $S$-local and global adelic $\theta$-functions will be the job that the next two Chapters (Chapters 4 and 5 of this work) are tasked with. The linear topologies arising throughout this work will all originate from spaces of Schwartz-Bruhat functions (such as $\mathcal{S}(\mathbf{A}_F)$ and $\mathcal{S}(\mathbf{A}_{F,S})$) and normed completions.

The topological vector spaces of adelic $\theta$-functions will be identified via Mellin transforms with topological vector spaces of meromorphic and holomorphic functions on the Riemann surfaces of continuous quasi-characters of $J_{F,S}$, respectively $C_F$. The Mellin transform will recover Tate's idelic Zeta integrals in much the same way as the classical Mellin transform of the Jacobi $\theta$-function recovers the Riemann Zeta function, completed with its own $\Gamma$-factor.

**117**

## PDF page 118

**118** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

One of the purposes of Chapter 4 of this work is to describe the image of the Mellin transform as an operator between two Hausdorff locally convex topological $\mathbf{C}$-vector spaces (a space of $\theta$-functions, on the source, and a space of $Z$-functions, on the target), promoting it to a linear topological isomorphism between a space of $\theta$-functions and a space of meromorphic functions satisfying growth conditions over vertical strips of bounded width and a functional equation, in a similar vein as the Converse Theorems from [CPS, Thm.1,p.165] for $\mathrm{GL}_n$.

So far we have only defined the adelic $\theta$-functions, both $S$-local and global. This is what we have done in Chapter 2. We will be calling the $\theta$-functions the “backward side” of the Mellin transform.

This Chapter, instead, defines the $Z$-functions. It provides the terminology and basic results to define and study the “forward side” of the Mellin transform, i.e. spaces of meromorphic functions on the Riemann surfaces of idelic and $S$-idelic quasi-characters.

3.1. Riemann surfaces of continuous quasi-characters 118

3.1.1. Generalities 118

3.1.2. Examples: Riemann surfaces of idelic quasi-characters 120

3.1.2.1. Local quasi-characters. 120

3.1.2.2. Global-local holomorphic submersions 121

3.1.2.3. Open convering of $\Omega(C_F)$ by analytic covers of the $S$-local Riemann surfaces 121

3.2. Global Idelic Zeta Functions 122

3.2.1. Recollections on Hecke $L$-functions 122

3.2.2. Global Idelic Zeta Functions 124

3.3. $S$-Local Idelic Zeta Functions 128

3.3.1. $S$-local Idelic $Z$-functions 128

3.3.1.1. Estimates on the correcting factor $\rho_S$ from the $S$-local functional equation 132

3.3.1.2. $\epsilon_S$-factors and the $S$-local functional equation 135

3.3.2. Poles and Residues of local $L$-functions 137

3.3.2.1. Poles and residues of the local $Z$-functions at the Archimedean places 138

3.3.2.2. Poles and residues of the local $Z$-functions at the non-Archimedean places 141

3.4. Eigendistributions and Weil's Identity 141

3.4.1. Weil's Identity: the unramified case 142

3.4.2. Applications of the unramified case of Weil's Identity 144

3.4.2.1. Convergence on the relative 1-line 145

3.4.2.2. Estimates on adelic $\theta$-functions, uniformly on Schwartz-Bruhat-bounded subsets 145

3.4.3. Eigendistributions and Weil's Identity: the general case 151

3.4.3.1. Standard Gaussians local and global Schwartz-Bruhat functions 152

3.4.3.2. Weil's Identity: the general case 152

**3.1. Riemann surfaces of continuous quasi-characters**

**3.1.1. Generalities.** For $G$ a Hausdorff locally compact abelian group, we denote by $\Omega(G)$ the set of all continuous homomorphisms $G\to\mathbf{C}^{\times}$. These are called *quasi-characters*. We make $\Omega(G)$ into a topological space via the compact-open topology.

If $G$ is modulated, meaning (as in Definition D.2.1.1) that it is equipped with a continuous proper non-trivial homomorphism $|\cdot|_G:G\to\mathbf{R}_{>0}$ (often called a “module”) then the kernel $G^1$ of the module is compact. There are only two cases:

- $|\cdot|_G$ is surjective, in which case we say that $G$ is $\mathbf{R}_{>0}$-*modulated*.

## PDF page 119

**3.1. RIEMANN SURFACES OF CONTINUOUS QUASI-CHARACTERS** · **119**

- $\Gamma:=|G|_G\subset\mathbf{R}_{>0}$ is a non-trivial discrete subgroup, hence of the form $\gamma^{\mathbf{Z}}$ for a unique $\gamma\in\mathbf{R}_{>0}$ with $\gamma>1$, in which case we say that $G$ is *discretely modulated*.

The topological space $\Omega(G)$ is equipped with the structure of a Riemann surface (with possibly uncountably many connected components). Indeed, the natural continuous map

$$
\pi:\Omega(G)\to\Omega(G^1)=\widehat{G^1} \tag{3.1.1.1}
$$

defined by $c\mapsto c|_{G^1}$ is surjective (characters lift) with discrete target has its open and closed fibres given by:

- ($\mathbf{R}_{>0}$-modulated case)

$$
\{\chi|\cdot|_G^s:s\in\mathbf{C}\}
$$

for $\chi\in\widehat{G}$. Here we use that $G/G^1\simeq\mathbf{R}_{>0}$ via $|\cdot|_G$, and it is a torsor under $\Omega(\mathbf{R}_{>0})=\mathbf{C}$ (identification via $t\mapsto t^s$).

- (discretely modulated case)

$$
\left\{\chi|\cdot|_G^s:s\in\mathbf{C}/\frac{2\pi i\mathbf{Z}}{\log(\gamma)}\right\}
$$

where we use the isomorphism $G/G^1\simeq\gamma^{\mathbf{Z}}$ via $|\cdot|_G$ (with $\gamma>1$), and it is a torsor under $\Omega(\gamma^{\mathbf{Z}})=\mathbf{C}/\frac{2\pi i\mathbf{Z}}{\log(\gamma)}$ (identification via $\gamma\mapsto\gamma^s$).

We denote by

$$
\Omega(G)(c)
$$

the connected component of $c\in\Omega(G)$, and if $\omega\in\widehat{G^1}$ is a continuous character then we write $\Omega(G)(\omega)$ for the connected component $\pi^{-1}(\omega)$ (i.e. the connected component of any $c\in\Omega(G)$ such that $c|_{G^1}=\omega$). These connected components do not have a natural unitary base-point, but they have a well-defined continuous surjective “abscissa” function $\sigma:\Omega(G)\to\mathbf{R}$ defined by

$$
\sigma(\chi|\cdot|_G^s):=\mathrm{Re}(s) \tag{3.1.1.2}
$$

(which is independent of the choice of unitary base-point $\chi$). We refer the reader to [CF, Ch.XV,§4.4,p.339] and [RV, §7.3,p.271] for a discussion on the connected components of $\Omega(G)$ in the special case of $G=C_F$ (with module homomorphism given by the idelic norm).

DEFINITION 3.1.1.1 (Abscissa of a quasi-character). Let $G$ be a modulated group. For any $c\in\Omega(G)$, we define the *abscissa*, or *exponent* of $c$ to be $\sigma(c)$ defined in (3.1.1.2).

We introduce notation for certain loci in the Riemann surfaces $\Omega(G)$.

DEFINITION 3.1.1.2 (Relative vertical strips). Let $G$ be a modulated group.

(1) For an interval $I\subset\mathbf{R}$ let $\Omega(G)_I$ be the subset of $\Omega(G)$ defined as

$$
\Omega(G)_I:=\{c\in\Omega(G):\sigma(c)\in I\} \tag{3.1.1.3}
$$

endowed with the subspace topology.

(2) For $I=(a,+\infty)$ we write $\Omega(G)_{>a}$ to denote the open subset $\Omega(G)_I\subset\Omega(G)$.

(3) For any $\omega\in\widehat{G^1}$, we define $\Omega(G)(\omega)_I=\Omega(G)_I\cap\Omega(G)(\omega)$.

For any $c\in\Omega(G)$, we denote by $\widehat{c}$ the quasi-character

$$
\widehat{c}=|\cdot|_G\,c^{-1}. \tag{3.1.1.4}
$$

The map $c\mapsto\widehat{c}$ is an analytic automorphism of $\Omega(G)$ exchanging the relative strips $\Omega(G)_I$ and $\Omega(G)_{1-I}$ (and so preserving $\Omega(G)_{[0,1]}$). We note that $c\mapsto\widehat{c}$ exchanges the connected components $\Omega(G)(\omega)$ and $\Omega(G)(\overline{\omega})$ for $\omega\in\widehat{G^1}$.

## PDF page 120

**120** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

**3.1.2. Examples: Riemann surfaces of idelic quasi-characters.** Let $F$ be a number field and $S$ be a finite set of places of $F$ containing all the Archimedean places.

Recall that the ring of $S$-integers $\mathcal{O}_{F,S}$ has unit group $\mathcal{O}_{F,S}^{\times}$ finitely generated of rank $|S|-1$ (see Theorem A.1.5.2) and the Hausdorff locally compact quotient

$$
J_{F,S}:=\mathrm{GL}_1(\mathbf{A}_{F,S})/\mathcal{O}_{F,S}^{\times} \tag{3.1.2.1}
$$

contains $J_{F,S}^1:=\ker(|\cdot|_{F,S})$ (the kernel of the $S$-idelic norm $|\cdot|_{F,S}:=\prod_{v\in S}|\cdot|_v$) as a closed compact (see Theorem A.1.5.2) abelian subgroup. As recalled at the beginning of §3.1.2, $(J_{F,S},|\cdot|_{F,S})$ is $\mathbf{R}_{>0}$-modulated.

We will be specializing to the cases $G=C_F,J_{F,S}$ and $C_{F,S}$, all equipped with compatible modules given by the idelic norm for $C_F$ and $C_{F,S}$, and the $S$-idelic norm for $J_{F,S}$ (descended from the idelic norm on $C_{F,S}$). Another important case is that of the modulated groups $F_v^{\times}$ ($\mathbf{R}_{>0}$-modulated for $v$ Archimedean, discretely modulated for $v$ non-Archimedean), we call their quasi-characters *local*.

For $c\in\Omega(C_F)$, i.e. for $c$ a quasi-character of the idele class group $C_F$, we denote by $c_v$ the restriction of $c$ to $F_v^{\times}\subset C_F$ where $F_v^{\times}$ is embedded as a closed subgroup under the insertion into the $v$-adic “coordinate” $F_v^{\times}\to\mathrm{GL}_1(\mathbf{A}_F)$ followed by the quotient homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to C_F$. By [CF, Ch.XV,Lemma 3.2.1], we have

$$
c=\bigotimes_{v\in\Sigma_F}c_v
$$

which means for all $g\in\mathrm{GL}_1(\mathbf{A}_F)$:

$$
c(g)=\prod_{v\in\Sigma_F}c_v(g_v)
$$

where $g_v$ denotes the projection of $g$ onto the $v$-indexed “coordinate” (a continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to F_v^{\times}$).

A similar description as a tensor product of local quasi-characters holds for the quasi-characters of $J_{F,S}$. We refer the reader to [CF, Ch.XV,§2.3] and [RV, Ch.5,§5.1,p.182], for a discussion on local, idelic and $S$-idelic quasi-characters. Moreover we refer the reader to [CF, Ch.XV,§4.5,p.342] for a concrete description of quasi-characters of $C_F$ in terms of ideal characters, and especially to [CF, Ch.XV,§4.5,p.342] on how to construct examples by a method (explained therein) resting on Dirichlet's $S$-Unit Theorem, to ensure the existence of solutions to certain systems of linear conditions on the complex parameters of a generic collection of local quasi-characters with the aim of arranging their tensor product (a continuous homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to\mathbf{C}^{\times}$) to be trivial on $F^{\times}$.

Throughout the rest of this section we will be making examples: we will describe the Riemann surfaces of local and $S$-local quasi-characters and recipes to relate them to $\Omega(C_F)$ for later use.

3.1.2.1. *Local quasi-characters.* We begin with the case of a finite place $v$ of $F$. Let $F_v$ be the resulting non-Archimedean local field. The normalized absolute value $|\cdot|_v$ on $F_v^{\times}$ promotes $G=F_v^{\times}$ to a discretely modulated group whose discrete value group is $q_v^{\mathbf{Z}}\subset\mathbf{R}_{>0}$, for $q_v:=|\pi_v|_v^{-1}$ for any choice of uniformizer $\pi_v$ at $v$. The kernel (which we denoted by $G^1$ for general modulated groups) of $|\cdot|_v$ is the group of units $\mathcal{O}_{F_v}^{\times}$ of the complete discrete valuation ring $\mathcal{O}_{F_v}$. This is a compact open subgroup of $F_v^{\times}$.

If $v$ is Archimedean, then $F_v^{\times,1}$ is $\mu_2$ if $v$ is real, and $\mathrm{U}(1)$ if $v$ is complex. In both cases, $\Gamma_v$ is isomorphic under $|\cdot|_v$ to $\mathbf{R}_{>0}$ as a Hausdorff locally compact abelian group.

In a manner similar to what was done for $\Omega(G)$ in §3.1.1, any choice of continuous homomorphic section to $|\cdot|_v$ and any choice of continuous quasi-character of $q_v^{\mathbf{Z}}$ induces a bi-holomorphism

$$
\Omega(F_v^{\times})\simeq\mathbf{C}/\frac{2\pi i\mathbf{Z}}{\log(q_v)}\times\widehat{\mathcal{O}_{F_v}^{\times}}. \tag{3.1.2.2}
$$

## PDF page 121

**3.1. RIEMANN SURFACES OF CONTINUOUS QUASI-CHARACTERS** · **121**

For $v$ Archimedean, the Archimedean absolute value $\lvert\cdot\rvert_v$ (which, recall, for $v$ complex is the *square* of the complex Euclidean norm) promotes $F_v^{\times}$ to an $\mathbf{R}_{>0}$-modulated group. The kernel of $\lvert\cdot\rvert_v$ is either a copy of $\mu_2$ (so a finite group of order 2) or $\mathrm{U}(1)$, the circle group. We therefore have a bi-holomorphism

$$
\Omega(F_v^{\times}) \simeq \mathbf{C} \times \widehat{\mathcal{O}_{F_v}^{\times}} \tag{3.1.2.3}
$$

induced by a choice of continuous homomorphic section to $\lvert\cdot\rvert_v$, to realize $F_v^{\times}$ as a product $\mathbf{R}_{>0}\times G^1$, with $G^1=\mu_2$ if $v$ is real and $G^1=\mathrm{U}(1)$ if $v$ is complex.

We refer the reader to the discussion on the global holomorphic parametrization of each $\Omega(F_v^{\times})$ from [CF, Ch.XV,Thm.2.3.1].

3.1.2.2. *Global-local holomorphic submersions.* The injective continuous insertion homomorphisms $j_v:F_v^{\times}\to C_F$ for each place $v$ of $F$ induce continuous maps

$$
\psi_v:\Omega(C_F)\to\Omega(F_v^{\times}) \tag{3.1.2.4}
$$

defined by composition, i.e. $\psi_v(c):=c_v=c\circ j_v$.

We will collect the following basic facts into a Lemma for future reference:

LEMMA 3.1.2.1. *Let $F$ be a number field. For every $v\in\Sigma_F$ the continuous map $\psi_v$ is a local analytic isomorphism.*

3.1.2.3. *Open convering of $\Omega(C_F)$ by analytic covers of the $S$-local Riemann surfaces.* We now fix a finite set $S$ of places of $F$ containing all of the Archimedean places. As for $C_F$, the quasi-characters of $J_{F,S}$ are a Riemann surface whose (countably many, since $J_{F,S}^1$ is second-countable) connected components are copies of the complex plane. Fixing a continuous homomorphic section to the $S$-idelic norm gives a bi-holomorphism

$$
\Omega(J_{F,S})\simeq\mathbf{C}\times\widehat{J_{F,S}^1} \tag{3.1.2.5}
$$

We now relate $\Omega(C_F)$ and $\Omega(J_{F,S})$. We define:

$$
\Omega_S(C_F)\subset\Omega(C_F) \tag{3.1.2.6}
$$

to be the subset of those idelic quasi-characters $c$ such that $c_v|_{\mathcal{O}_{F_v}^{\times}}=1$ for every $v\notin S$. We refer to $\Omega_S(C_F)$ as the subset of the idelic quasi-characters that are *unramified* outside $S$. Clearly $\Omega_S(C_F)$ is open in $\Omega(C_F)$ since the defining condition of $\Omega_S(C_F)$ only concerns the restriction of the idelic quasi-character $c$ to $C_F^1$, i.e. the image of the point $c\in\Omega(C_F)$ in the discrete parameter space $\widehat{C_F^1}$ over which $\Omega(C_F)$ is fibred, and hence $\Omega_S(C_F)$ is a disjoint union of fibres. It therefore inherits a unique Riemann surface structure promoting the open immersion to a bi-holomorphism onto its image.

The closed continuous homomorphism

$$
j_{F,S}:\mathrm{GL}_1(\mathbf{A}_{F,S})\to\mathrm{GL}_1(\mathbf{A}_F) \tag{3.1.2.7}
$$

defined as

$$
j_{F,S}(g_S):=(g_v)_{v\in\Sigma_F} \tag{3.1.2.8}
$$

where $g_v:=(g_S)_v$ for $v\in S$, and $g_v=1$ otherwise, induces continuous maps:

$$
\psi_{F,S}:\Omega_S(C_F)\to\Omega(J_{F,S}). \tag{3.1.2.9}
$$

We record the following basic facts about $\psi_{F,S}$ in a lemma for future reference:

LEMMA 3.1.2.2. *Let $F$ be a number field $S$ a finite set of places containing all the Archimedean places. The continuous map $\psi_{F,S}$ of (3.1.2.9) is a surjective local analytic isomorphism.*

## PDF page 122

**122** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

We note that $\{\Omega_S(C_F)\}_{S\subset\Sigma_F}$ is an open cover of $\Omega(C_F)$ as $S$ varies over all the finite sets of places of $F$ containing all the Archimedean places.

**3.2. Global Idelic Zeta Functions**

The correspondence between $\theta$-functions and Zeta functions goes back to Riemann's paper [Riemann] on the distribution of prime numbers, where he established the functional equation and existence of the analytic continuation for the Riemann Zeta function by exhibiting it as the Mellin transform of the Jacobi $\theta$-function.

Tate's dissertation from [CF, Ch.XV] mirrored Riemann's $\theta$-function approach to the study of the analytic properties of abelian $L$-functions. Therein, however, the focus is mostly on the global Zeta integrals arising as the Fourier-Mellin transforms of Schwartz-Bruhat functions on the adeles.

Chapter 2 of this work initiated the systematic study of their $\theta$-functions. This will be continued throughout the next three Chapters, by studying the linear spaces comprising of those $\theta$-functions, both global and $S$-local, as topological vector spaces.

The Mellin transform will produce idelic $Z$-functions from adelic $\theta$-functions, and these too are going to be studied by packaging them into a topological vector space, with the Mellin transform promoted to a linear topological isomorphism.

While the previous Chapter was tasked with defining and studying the first properties of the adelic $\theta$-functions, short of collecting them into a topological vector space, this Chapter is tasked with doing the same for the resulting idelic $Z$-functions, to be defined and studied herein.

We will be referring to the spaces of adelic $\theta$-functions as the “backward side” of the Mellin transform, and to the spaces of Idelic $Z$-fuctions as the “forward side” of the Mellin transform.

To paraphrase further, while the previous Chapter was tasked with introducing the main elements comprising the backward side of the Mellin transform, this Chapter is tasked with doing the same for the forward side of the Mellin transform, so that in the subsequent Chapters we can study both sides systematically through the lens of functional and harmonic analysis.

**3.2.1. Recollections on Hecke $L$-functions.** Let $F$ be a number field. We consider the family of idelic quasi-characters

$$
c:=\chi\lvert\cdot\rvert_F^s
$$

with $\chi\in\widehat{C_F}$ a fixed continuous character, and $s\in\mathbf{C}$. Every connected component of $\Omega(C_F)$ has a unitary point, i.e. whose abscissa is $\sigma=0$. For any place $v$ of $F$, we thus have

$$
c_v=\chi_v\lvert\cdot\rvert_v^s
$$

as continuous quasi-characters of $F_v^{\times}$ (where $c_v$ is the restriction of $c$ to $F_v^{\times}$).

We denote by $S_{\chi}$ the finite set of finite places of $F$ at which $\chi$ is ramified. For any place $v\in\Sigma_F-(S_{\chi}\cup S_{\infty})$, $v$ is non-Archimedean and hence we may choose a uniformizer $\pi_v\in\mathcal{O}_{F_v}$ and evaluate $\chi_v$ at $\pi_v$. The value $\chi_v(\pi_v)$ is independent of the choice of $\pi_v$. We denote it $\chi(\mathfrak{p}_v)$ where $\mathfrak{p}_v\subset\mathcal{O}_F$ is the unique prime ideal corresponding to the finite place $v$.

Since $\lvert\cdot\rvert_v$ is normalized, there exists a unique $s\in\mathbf{C}/(2\pi i\mathbf{Z}/\log(q_v))$ such that $c_v(\pi_v)=\chi_v(\mathfrak{p}_v)q_v^{-s}$, and so we see that we have

$$
1-\chi(\mathfrak{p}_v)q_v^{-s}=1-c_v(\pi_v) \tag{3.2.1.1}
$$

as holomorphic functions on the Riemann surface $\Omega(F_v^{\times})(1)$, the connected component over $1\in\widehat{\mathcal{O}_{F_v}^{\times}}$.

We recall the the following classical fact:

## PDF page 123

**3.2. GLOBAL IDELIC ZETA FUNCTIONS** · **123**

LEMMA 3.2.1.1. *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. The following product is absolutely convergent over $\Omega(C_F)(\chi|_{C_F^1})_{>1}$, uniformly on compact subsets:*

$$
\Gamma_F(s,\chi)\prod_{v\in\Sigma_F-(S_{\chi}\cup S_{\infty})}(1-c_v(\pi_v))^{-1} \tag{3.2.1.2}
$$

where:

$$
\Gamma_F(s,\chi):=\prod_{v\in S_{\infty}}L(\chi_v\lvert\cdot\rvert_v^s) \tag{3.2.1.3}
$$

with, for $v$ real:

$$
L(\lvert\cdot\rvert_v^s):=\pi^{-s/2}\Gamma(s/2),\; L(\mathrm{sgn}\lvert\cdot\rvert_v^s)=\pi^{-(s+1)/2}\Gamma\left(\frac{s+1}{2}\right) \tag{3.2.1.4}
$$

*and, for $v$ complex and $\chi_v\lvert\cdot\rvert_v^s=\chi_{n,s}$, for $n\in\mathbf{Z}$, the continuous quasi-character character of $\mathbf{C}^{\times}$ defined as $(r,\theta)\mapsto r^se^{in\theta}$*

$$
L(\chi_v\lvert\cdot\rvert_v^s):=(2\pi)^{-(s+\frac{|n|}{2})}\Gamma\left(s+\frac{|n|}{2}\right). \tag{3.2.1.5}
$$

The proof is by comparison with the convergence of the Euler product for the Riemann $\zeta$-function over the half-plane of absolute convergence. We refer the reader to [RV, Ch.7,Lemma 7.18].

DEFINITION 3.2.1.2. Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. We define the *Hecke $L$-function* of character $\chi$ to be the function $L(s,\chi)$ over $\Omega(C_F)(\chi)_{>1}$ defined by the absolutely and locally uniformly convergent product in (3.2.1.2).

We recall here below the key properties of Hecke $L$-functions.

PROPOSITION 3.2.1.3 (Regularity and symmetries of Hecke $L$-functions). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. The function $L(s,\chi)$ defined on $\mathbf{C}_{>1}$ in (3.2.1.2) admits a meromorphic continuation to the complex $s$-plane, satisfying the following conditions:*

(1) *If $\chi|_{C_F^1}$ is non-trivial, $L(s,\chi)$ is entire.*

(2) *If $\chi|_{C_F^1}$ is trivial, $L(s,\chi)$ is meromorphic with simple poles at $s=it_0,1+it_0$, for a unique real number $t_0\in\mathbf{R}$ such that $\chi=\lvert\cdot\rvert_F^{-it_0}$, whose residues are, respectively, $-\bar{\mu}_1(C_F^1)$ and $|N(\mathfrak{d}_{F/\mathbf{Q}})|^{-1/2}\bar{\mu}_1(C_F^1)$.*

(3) *As meromorphic functions on the complex $s$-plane, $L(s,\chi)$ and $L(s,\bar{\chi})$ are related by the following functional equation:*

$$
L(1-s,\bar{\chi})=\epsilon(s,\chi)L(s,\chi) \tag{3.2.1.6}
$$

*where $\epsilon(s,\chi)$ is a nowhere vanishing entire function.*

(4) *The only zeros of $L(s,\chi)$ over $\mathbf{C}_{>0}$ are contained in the open vertical strip $\mathbf{C}_{(0,1)}$.*

The Proposition is proved upon combining [RV, Thm.7.2(iii)] (throughout whose proof the $\epsilon$-factor is seen to be of the form

$$
\epsilon(s,\chi)=\prod_{v\in\Sigma_F}\epsilon(\chi_v\lvert\cdot\rvert_v^s)
$$

with $\epsilon(\chi_v\lvert\cdot\rvert_v^s)$ computed explicitly in [RV, Ch.7,§7.1,p.250,251] for $v$ real, [RV, Ch.7,§7.1p.253] for $v$ complex, [RV, Ch.7,§7.1,p.258] for $v$ non-Archimedean, with the infinite product having all but finitely many factors equal to 1) with [RV, Thm.7.19]. Also, (4) uses the classical zero-free region for $L(s,\chi)$ (see Proposition B.6.1.1) or weaker versions that focus on the right edge of the critical strip.

DEFINITION 3.2.1.4. Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. We define the *finite Hecke $L$-function* of character $\chi$ to be the function over $\Omega(C_F)(\chi|_{C_F^1})_{>1}$ defined by the absolutely and locally

## PDF page 124

**124** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

uniformly convergent product

$$
L_f(s,\chi):=\prod_{v\in\Sigma_{F,f}-S_{\chi}}\frac{1}{1-\chi(\mathfrak{p}_v)(N\mathfrak{p}_v)^{-s}}. \tag{3.2.1.7}
$$

By Proposition 3.2.1.3, the finite Hecke $L$-function $L_f(s,\chi)$ extends to a meromorphic function on the complex $s$-plane, and satisfies the functional equation

$$
L_f(s,\chi)=W(s,\chi)L_f(1-s,\bar{\chi}). \tag{3.2.1.8}
$$

where

$$
W(s,\chi):=\frac{1}{\epsilon(s,\chi)}\frac{\Gamma_F(1-s,\bar{\chi})}{\Gamma_F(s,\chi)} \tag{3.2.1.9}
$$

with $\epsilon(s,\chi)$ entire and nowhere-vanishing and $\Gamma_F(1-s,\bar{\chi})$ and $\Gamma_F(s,\chi)$ meromorphic.

By Stirling's Approximation, we have the estimate, for every $0\le\alpha\le\beta$ and $0\le\alpha\le\sigma\le\beta$, in light of (3.2.1.4) and and (3.2.1.5):

$$
|W(s,\chi)|\ll |t|^{[F:\mathbf{Q}](\frac12-\sigma)} \tag{3.2.1.10}
$$

as $s=\sigma+it$ satisfies $|t|\to+\infty$, where the implied constant depends on $\alpha,\beta$. We refer the reader to [IK, Ch.5, §A.4, (5.114)] for the estimate from (3.2.1.10), we further refer the reader to §B.1.

On the definition and properties of $\epsilon$-factors, which, for abelian $L$-functions, we will be reviewing throughout this Chapter, we further refer the reader to Tate's [Tate, §3, (3.6), p.17], to Deligne's [Del, §4.11], and to Langlands' [Langlands], with the caveat of differing normalizations in the latter two references. We further refer the reader to §14.1.1 of this work.

**3.2.2. Global Idelic Zeta Functions.** For $a,b\in\mathbf{R}_{>0}$ with $a\le b$, we adopt the standard notation

$$
\mathrm{GL}_1(\mathbf{A}_F)^{[a,b]}:=\{g\in\mathrm{GL}_1(\mathbf{A}_F):|g|_F\in[a,b]\}.
$$

The following Theorem is partly contained within [CF, Ch.XV,Thm.4.4.1].

THEOREM 3.2.2.1 (Idelic Mellin transform of global adelic $\theta$-functions). *We let $f\in\mathcal{S}(\mathbf{A}_F)$ be a Schwartz-Bruhat function and $c\in\Omega(C_F)$. Then:*

(1) *the integral*

$$
Z(f,c):=\int_{\mathrm{GL}_1(\mathbf{A}_F)}f(g)c(g)\,\mathrm{d}\mu(g) \tag{3.2.2.1}
$$

*converges absolutely over $\Omega(C_F)_{>1}$, uniformly on compact subsets as a function of $c\in\Omega(C_F)_{>1}$ and it is holomorphic over $\Omega(C_F)_{>1}$.*

(a) *It extends to a meromorphic function on $\Omega(C_F)$ with at most simple poles at $c=1$ and $c=\lvert\cdot\rvert_F$, with residues $-\bar{\mu}_1(C_F^1)f(0)$, respectively $\bar{\mu}_1(C_F^1)\widehat{f}(0)$.*

(b) *It satisfies the functional equation*

$$
Z(f,c)=Z(\widehat{f},\widehat{c}). \tag{3.2.2.2}
$$

(2) *The integral*

$$
L(f,c):=\int_{C_F}\Phi_F(f)(g)c(g)\,\mathrm{d}\bar{\mu}(g) \tag{3.2.2.3}
$$

*is absolutely convergent over $\Omega(C_F)_{>1}$, uniformly on compact subsets as a function of $c\in\Omega(C_F)_{>1}$ (see Remark 3.2.2.2 for the meaning of such uniformity).*

(a) *If $f(0)=\widehat{f}(0)=0$, then the integral defining $L(f,c)$ in (3.2.2.3) is absolutely convergent over $\Omega(C_F)$, uniformly on compact subsets. Under these assumptions, $L(f,c)$ is an entire function.*

## PDF page 125

**3.2. GLOBAL IDELIC ZETA FUNCTIONS** · **125**

(b) *Over all the connected components of $\Omega(C_F)$ other than $\Omega(C_F)(1)$, the integral defining $L(f,c)$ in (3.2.2.3) is, with no further assumptions on $f$, absolutely convergent, uniformly on compact subsets, so $L(f,c)$ is entire on all the connected components of $\Omega(C_F)$ other than $\Omega(C_F)(1)$ and it is meromorphic with at most simple poles at $1$ and $\lvert\cdot\rvert_F$, over $\Omega(C_F)(1)$.*

(3) *We fix a continuous character $\omega\in\widehat{C_F^1}$, equivalently a connected component $\Omega(C_F)(\omega)$ of $\Omega(C_F)$. Let $\tau:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)$ be a continuous homomorphic section to the idelic norm. The integral*

$$
\int_{\mathbf{R}_{>0}}\Phi_{F,\omega}(f)(\tau(t))c(\tau(t))\,\frac{\mathrm{d}t}{t} \tag{3.2.2.4}
$$

*is absolutely convergent over $\Omega(C_F)(\omega)_{>1}$, uniformly on compact subsets as a function of $c\in\Omega(C_F)_{>1}$.*

(a) *If $\omega=1$ and $f(0)=\widehat{f}(0)=0$, then the integral in (3.2.2.4) is absolutely convergent over $\Omega(C_F)(1)$, uniformly on compact subsets. Under these assumptions, its value is an entire function of $c\in\Omega(C_F)(1)$.*

(b) *If $\omega\ne 1$, the integral in (3.2.2.4) is absolutely convergent on $\Omega(C_F)(\omega)$, uniformly on compact subsets, and its value is an entire function of $c\in\Omega(C_F)(\omega)$.*

*For any $\omega\in\widehat{C_F^1}$, the following identity holds:*

$$
L(f,c)=\int_{\mathbf{R}_{>0}}\Phi_{F,\omega}(f)(\tau(t))c(\tau(t))\,\frac{\mathrm{d}t}{t} \tag{3.2.2.5}
$$

*as meromorphic functions of $c\in\Omega(C_F)(\omega)$, with both sides being, in turn, equal to $Z(f,c)$ from (3.2.2.1) over $\Omega(C_F)(\omega)$. In particular, under these assumptions on $f$, $Z(f,c)$ is entire over all the connected components of $\Omega(C_F)$ parametrized by non-trivial characters of $C_F^1$, meromorphic over $\Omega(C_F)(1)$ with at most simple poles at $1$, $\lvert\cdot\rvert_F$, and, under the additional assumption $f(0)=\widehat{f}(0)=0$, it is holomorphic everywhere over $\Omega(C_F)$.*

REMARK 3.2.2.2. Uniform convergence of the integral in (3.2.2.1) on compacts as a function of $c$ means that the sequence of truncated integrals

$$
\int_{\mathrm{GL}_1(\mathbf{A}_F)^{[1/n,n]}}f(g)c(g)\,\mathrm{d}\mu(g)
$$

converges uniformly as $c$ varies in any compact subset of $\Omega(C_F)_{>1}$. The same holds with $[1/n,n]$ replaced by any growing sequence of intervals $\{[1/a_n,a_n]\}$ with real numbers $\{a_n\}_{n\ge 0}\subset[1,+\infty)$ such that $\lim_{n\to+\infty}a_n=+\infty$. These truncated integrals are holomorphic in $c$, by compactness of the domain of integration, so local uniformity of convergence ensures the limiting integral is holomorphic in $c$.

We briefly digress to discuss continuity of the formation of $Z(f,c)$ for each fixed $c\in\Omega(C_F)_{>1}$, as $f$ varies over $\mathcal{S}(\mathbf{A}_F)$.

LEMMA 3.2.2.3 ($Z(\cdot,c)$ is valued in tempered distributions for each $c\in\Omega(C_F)_{>1}$). *Let $F$ be a number field. Then for each fixed $c\in\Omega(C_F)_{>1}$, formation of $Z(f,c)$ is continuous in $f$ with respect to the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{A}_F)$.*

PROOF. We prove that for any Cauchy sequence $\{f_k\}_{k\ge 0}$ with limit $f$, $Z(f_k,c)\to Z(f,c)$, i.e. $Z(\cdot,c)$ is sequentially continuous as a linear form on $\mathcal{S}(\mathbf{A}_F)$. Although $\mathcal{S}(\mathbf{A}_F)$ is not second-countable, sequential continuity on it still implies continuity because such an implication is a property of continuous linear functionals on bornlogical locally convex spaces [Scha, Ch.II, 8.3] and $\mathcal{S}(\mathbf{A}_F)$ is an LF-space (by Lemma 2.1.3.2(1)) so it is also bornological (see [Scha, Ch.II, Cor. 2 to 8.2]).

Since $\mathcal{B}:=\{f_k\}_{k\ge 0}\cup\{f\}$ is a Cauchy sequence with its limit point, it is a bounded subset in $\mathcal{S}(\mathbf{A}_F)$. By Theorem 2.2.3.4(5), for any integer $N>1$ there exist real numbers $C_{\mathcal{B},N},C'_{\mathcal{B},N}>0$ such that for all $u\in\mathcal{B}$.

$$
\lvert\Phi_F(u)(g)-1_{C_F^{(0,1]}}(g)\cdot\lvert g\rvert_F^{-1}\widehat{u}(0)+1_{C_F^{(0,1]}}(g)\cdot u(0)\rvert\le C_{\mathcal{B},N}\lvert g\rvert_F^{-N}\cdot 1_{C_F^{[1,+\infty)}}+C'_{\mathcal{B},N}\lvert g\rvert_F^{N}\cdot 1_{C_F^{(0,1]}}(g)
$$

## PDF page 126

**126** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

as functions on $C_F$. By Dominated Convergence, we have $Z(f_k,c)\to Z(f,c)$ as $k\to+\infty$, noting that $u\mapsto u(0)$ and $u\mapsto\widehat{u}(0)$ are also continuous functionals (they are $\delta_0$ and $\widehat{\delta}_0$). $\square$

PROOF OF THEOREM 3.2.2.1. (1): By Lemma 2.2.2.1 and continuity of Schwartz-Bruhat functions on $\mathbf{A}_F$, along with preservation of $\mathcal{S}(\mathbf{A}_F)$ under the adelic Fourier transform and Fourier inversion on $\mathcal{S}(\mathbf{A}_F)$ (both consequences of [DE, Thm.3.5.8] and Dominated Convergence), the complex vector space of Schwartz-Bruhat functions on $\mathbf{A}_F$ is a linear subspace of the complex vector space $\mathfrak{z}$ from [CF, Ch.XV,§4.4,p.338] comprised of complex-valued continuous functions on $\mathbf{A}_F$ for which the main global results in Tate's dissertation all hold (see [CF, Ch.XV,§4.4]).

To check that Tate's integrability conditions in $\mathfrak{z}_3$ from [CF, Ch.XV,§4.4,p.338] (i.e. that for any $\sigma>1$, $f\cdot\lvert\cdot\rvert_F^{\sigma}$ and $\widehat{f}\cdot\lvert\cdot\rvert_F^{\sigma}$ are absolutely $\mu$-integrable over $\mathrm{GL}_1(\mathbf{A}_F)$), we proceed as follows. By Lemma 2.1.3.2(3), it is enough to show this for $f\in\mathcal{S}(\mathbf{A}_F)$ of the special form

$$
f=f_{\infty}\otimes\bigotimes_{v\in\Sigma_{F,f}}1_{K_v}
$$

for $K_v\subset F_v$ a compact open subset for every finite place $v$ of $F$, with $K_v=\mathcal{O}_{F_v}$ for all but finitely many $v$. By [RV, Prop.5.6(ii), p.186] we have

$$
\int_{\mathrm{GL}_1(\mathbf{A}_F)}\lvert f(g)\rvert\lvert g\rvert_F^{\sigma}\,\mathrm{d}\mu(g)=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})}\lvert f_{\infty}(g_{\infty})\rvert\lvert g_{\infty}\rvert_{F,S_{\infty}}^{\sigma}\,\mathrm{d}\mu_{S_{\infty}}(g_{\infty})\prod_{v\in\Sigma_{F,f}}\int_{K_v}\lvert g_v\rvert_v^{\sigma}\,\mathrm{d}\mu_v(g_v) \tag{3.2.2.6}
$$

where the product on the right side is allowed to diverge. By Proposition 2.4.3.1, the integral over $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ converges since $f_{\infty}$ is Schwartz-Bruhat over $\mathbf{A}_{F,S_{\infty}}$. By absolute convergence of the Euler product of the Riemann zeta function, the product of the integrals $\int_{\mathcal{O}_{F_v}}\lvert g_v\rvert_v^{\sigma}\,\mathrm{d}\mu_v(g_v)$ for all finite places $v$ of $F$ such that $K_v=\mathcal{O}_{F_v}$ converges and so the integral in (3.2.2.6) converges too. The same reasoning applies to $\widehat{f}$ in place of $f$.

In particular, the integral in (3.2.2.1) defining $Z(f,c)$ converges absolutely for $c\in\Omega(C_F)_{>1}$, and uniformly on the compact subsets of $\Omega(C_F)_{>1}$, therefore defining a holomorphic function of $c$ there. By [CF, Ch.XV,Thm.4.4.1] (see also [RV, Thm.7.16]), the function $Z(f,c)$ of $c\in\Omega(C_F)_{>1}$ extends to a meromorphic function on the Riemann surface $\Omega(C_F)$ with at most simple poles at $c=1$ and $c=\lvert\cdot\rvert_F$, whose residues are, respectively, $-\bar{\mu}_1(C_F^1)f(0)$ and $\bar{\mu}_1(C_F^1)\widehat{f}(0)$.

The meromorphic function $Z(f,c)$ of $c\in\Omega(C_F)$ further satisfies the functional equation in (3.2.2.2).

(2): The first convergence assertion (without assuming $f(0)=\widehat{f}(0)=0$) follows from the first two parts of Theorem 2.2.3.4 noting $\lvert\cdot\rvert_F^{\sigma-1}$ has, for $\sigma>1$, an $\bar{\mu}$-integrable singularity as $\lvert g\rvert_F\to 0$.

By Theorem 2.2.3.4(3), since $\lvert c\rvert=\lvert\cdot\rvert_F^{\sigma(c)}$, upon choosing an integer $N>0$, there exists a constant $C_N>0$ depending on $N$ and $f$ but not on $c$, such that

$$
\lvert c(g)\Phi_F(f)(g)\rvert\le C_N e^{-N\lvert\log\lvert g\rvert_F\rvert+\sigma(c)\log\lvert g\rvert_F} \tag{3.2.2.7}
$$

and since $\sigma(c)\log\lvert g\rvert_F\le\lvert\sigma(c)\rvert\,\lvert\log\lvert g\rvert_F\rvert$, we have:

$$
\lvert c(g)\Phi_F(f)(g)\rvert\le C_N e^{-N\lvert\log\lvert g\rvert_F\rvert+\sigma(c)\log\lvert g\rvert_F}\le C_N e^{(\lvert\sigma(c)\rvert-N)\lvert\log\lvert g\rvert_F\rvert} \tag{3.2.2.8}
$$

being the exponential function $\exp:\mathbf{R}\to\mathbf{R}_{>0}$ strictly increasing.

We choose a bounded interval $I=[a,b]\subset\mathbf{R}$ and an integer $N>\max\{\lvert a\rvert,\lvert b\rvert\}$, and consider the resulting constant $C_N>0$ from Theorem 2.2.3.4(3).

Upon calling $\bar{\mu}'$ the unique Haar measure on

$$
C_F/C_F^1\overset{\lvert\cdot\rvert_F}{\simeq}\mathbf{R}_{>0}
$$

## PDF page 127

**3.2. GLOBAL IDELIC ZETA FUNCTIONS** · **127**

prescribed $C_F/C_F^1$ by Theorem D.1.2.1 by the choices of the Haar measure $\bar{\mu}$ on $C_F$ and the Haar measure $\bar{\mu}_1$ induced by $\mu_1$ on $\mathrm{GL}_1(\mathbf{A}_F)^1$ constructed in Definition A.3.2.1 and the counting measure on $F^{\times}$, we have $\bar{\mu}'=\mathrm{d}t/t$.

We have, by (3.2.2.7), the bound

$$
\int_{\mathbf{R}_{>0}}\left(\int_{C_F^1}\lvert c(\tau(t))\Phi_F(f)(\tau(t)g_0)\rvert\,\mathrm{d}\bar{\mu}_1(g_0)\right)\frac{\mathrm{d}t}{t}\le C_N\bar{\mu}_1(C_F^1)\int_{\mathbf{R}_{>0}}e^{(\lvert\sigma(c)\rvert-N)\lvert\log(t)\rvert}\,\frac{\mathrm{d}t}{t}=2\,C_N\bar{\mu}_1(C_F^1)\int_0^{+\infty}e^{(\lvert\sigma(c)\rvert-N)x}\,\mathrm{d}x. \tag{3.2.2.9}
$$

Since $N>\lvert\sigma(c)\rvert$ for every $c\in\Omega(C_F)_{[a,b]}$, the leftmost integral in (3.2.2.9) converges for such $c$ since the rightmost integral does.

The integral in the leftmost side of (3.2.2.9) reads

$$
\int_{C_F/C_F^1}\left(\int_{C_F^1}\lvert c(\tau(t))\Phi_F(f)(\tau(t)g_0)\rvert\,\mathrm{d}\bar{\mu}_1(g_0)\right)\mathrm{d}\bar{\mu}'(g) \tag{3.2.2.10}
$$

which therefore converges.

By Lemma D.1.2.3 (see also [DE, Cor.1.5.4]), we conclude that the integral in (3.2.2.3) converges absolutely and uniformly over $\Omega(C_F)_{[a,b]}$. The point is that the integrals over $1/n\le\lvert g\rvert_F\le n$ in $C_F/C_F^1$ converge uniformly with respect to $c\in\Omega(C_F)_{[a,b]}$ as $n\to+\infty$ (by an analog of the inequality in (3.2.2.9) for such integrals and observing that for $b>0$, $\int_M^{+\infty}e^{-bx}\,\mathrm{d}x\to 0$ as $M\to+\infty$).

Since the interval $[a,b]$ is an arbitrary compact interval in the real line, we deduce that the integral in (3.2.2.3) converges absolutely and uniformly on the compact subsets of $\Omega(C_F)$ (in fact, on the closed vertical strips of $\Omega(C_F)$ of bounded width and non-empty interior), and the function $L(f,c)$ of $c\in\Omega(C_F)$ it defines is holomorphic over $\Omega(C_F)$. By Theorem D.1.2.1 (see also [DE, Thm.1.5.3]), which applies by Lemma D.1.2.3 (see also [DE, Cor.1.5.4]), the following identity holds pointwise on $\Omega(C_F)$:

$$
\int_{\mathbf{R}_{>0}}\Phi_{F,\omega}(f)(\tau(t))c(\tau(t))\,\frac{\mathrm{d}t}{t}=\int_{C_F}\Phi_F(g)\,c(g)\,\mathrm{d}\bar{\mu}(g)
$$

which gives (3.2.2.5).

Since the integral in (3.2.2.1) defining $Z(f,c)$ is absolutely convergent over $\Omega(C_F)_{>1}$, then by Theorem D.1.2.1 again we have the indentity, pointwise over $\Omega(C_F)_{>1}$:

$$
\int_{C_F}\Phi_F(f)(g)c(g)\,\mathrm{d}\bar{\mu}(g)=\int_{C_F}\sum_{\xi\in F^{\times}}f(\xi g)c(g)\,\mathrm{d}\bar{\mu}(g)=\int_{\mathrm{GL}_1(\mathbf{A}_F)}f(g)c(g)\,\mathrm{d}\mu(g). \tag{3.2.2.11}
$$

This gives $L(f,c)=Z(f,c)$ over $\Omega(C_F)_{>1}$, and hence, by the Identity Theorem, $L(f,c)=Z(f,c)$ holds everywhere over $\Omega(C_F)$, which establishes all the remaining assertions. $\square$

We explain Theorem 3.2.2.1(2) on an example that connects to the classical theory of Dirichlet series:

EXAMPLE 3.2.2.4. Let $F=\mathbf{Q}$ and $f:=f_{\infty}\otimes\bigotimes_p f_p$, with $f_2:=\widehat{1_{\mathbf{Z}_2^{\times}}}$ and $f_p=1_{\mathbf{Z}_p}$ for every prime $p\ne 2$, where $f_{\infty}$ is the Gaussian function on $\mathbf{R}$, i.e. $f_{\infty}(x):=e^{-\pi x^2}$.

We let $c\in\Omega(C_{\mathbf{Q}})(1)$, i.e. the connected component of the trivial quasi-character, be parametrized as $\lvert\cdot\rvert_{\mathbf{Q}}^s$, for $s\in\mathbf{C}$.

For $\mathrm{Re}(s)>1$, we compute:

$$
Z(f,c)=Z(f,\lvert\cdot\rvert_{\mathbf{Q}}^s)=\int_{\mathbf{R}^{\times}}f_{\infty}(x)\lvert x\rvert^s\,\frac{\mathrm{d}x}{\lvert x\rvert}\int_{\mathbf{Q}_2^{\times}}\widehat{1_{\mathbf{Z}_2^{\times}}}\lvert x\rvert_2^s\,\mathrm{d}\mu_2(x)\prod_{p>2}\int_{\mathbf{Q}_p^{\times}}1_{\mathbf{Z}_p}(x)\lvert x\rvert_p^s\,\mathrm{d}\mu_p(x)
$$

to be, up to a positive multiplicative constant, $\pi^{-s/2}\Gamma(s/2)(1-2^{1-s})\prod_p\frac{1}{1-p^{-s}}=(1-2^{1-s})\pi^{-s/2}\Gamma(s/2)\zeta(s)$, since, recall, $\mu_p=\frac{p}{p-1}\frac{\mathrm{d}x}{\lvert x\rvert_p}$, the multiplicative local Tamagawa measure from Definition A.3.2.2.

## PDF page 128

**128** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

The reader will recognize a phenomenon of resolution of the singularity at $s=0$ for $\pi^{-s/2}\Gamma(s/2)\zeta(s)$ similar to that for the Dirichlet $\eta$-function, which, recall, is the “alternating zeta function” defined as

$$
\eta(s):=\sum_{m\ge 1}\frac{(-1)^{m-1}}{m^s}
$$

which, over the half-plane of absolute convergence $\mathrm{Re}(s)>1$, agrees with $(1-2^{s-1})\zeta(s)$. The Dirichlet series defining $\eta(s)$ converges conditionally over the half-plane $\mathbf{C}_{>0}$, and absolutely over the half-plane $\mathbf{C}_{>1}$.

See, for example, [T1, Ch.IX,§9.13]; see also [H], where a proof of the functional equation for $\xi(s)$ is provided using the Dirichlet $\eta$-function.

The local Mellin transform of the Fourier transform of $1_{\mathbf{Z}_2^{\times}}$ resolves the singularity at $s=1$ of $\pi^{-s/2}\Gamma(s/2)\zeta(s)$, in light of the calculation from Example A.3.1.6, in a similar manner as the factor $(1-2^{s-1})$ does for $\eta(s)$.

We observe that indeed $\widehat{f}(0)=0$, which leads to $Z(f,\lvert\cdot\rvert_{\mathbf{Q}}^s)$ having no pole at $\lvert\cdot\rvert_{\mathbf{Q}}$.

We may think of the idelic Zeta functions $Z(f,c)$ for $f\in\mathcal{S}(\mathbf{A}_F)$ satisfying $f(0)=\widehat{f}(0)=0$, as idelic analogs of the Dirichlet $\eta$-function, and we may think of Theorem 3.2.2.1(2) as the corresponding analog of the conditional convergence over $\mathbf{C}_{>0}$ of the Dirichlet series defining $\eta(s)$.

We introduce the following terminology:

DEFINITION 3.2.2.5 (Global Idelic $Z$-functions). Let $F$ be a number field, $f\in\mathcal{S}(\mathbf{A}_F)$ a Schwartz-Bruhat function.

We refer to the meromorphic function $Z(f,c)$ of $c\in\Omega(C_F)$ defined in (3.2.2.2) of Theorem 3.2.2.1, as the Global Idelic $Z$-function of $f$.

We will often write $Z(f,c)$ even though the arguments under discussion will concern the global adelic $\theta$-function $\Phi_F(f)$ only, i.e. will depend on $f$ only through its $\theta$-function.

We will start referring to $Z$ as the Mellin transform of $f$, and of $\Phi_F(f)$, alike.

**3.3. $S$-Local Idelic Zeta Functions**

Throughout this subsection, we fix a number field $F$ and a finite set $S$ of places of $F$ containing all of the Archimedean places.

**3.3.1. $S$-local Idelic $Z$-functions.** Recall that the local Fourier transforms on each $\mathcal{S}(F_v)$, normalized using the standard continuous additive character for each $v$, which we constructed in Example A.3.1.8 and Example A.3.1.9, induce the $S$-adelic Fourier transform on $\mathcal{S}(\mathbf{A}_{F,S})$ with respect to a standard additive character of the $S$-adeles $\mathbf{A}_{F,S}$ and the additive Tamagawa measure $\nu_S$ (the Haar measure $\bigotimes_{v\in S}\nu_v$ on $\mathbf{A}_{F,S}$ from Definition A.3.4.1, with $\nu_v$ the local additive Tamagawa measure on the additive topological group of the local field $F_v$ from Definition A.3.1.2). This is a continuous automorphism with respect to the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{A}_{F,S})$. We further refer the reader to Remark A.3.4.2 and to Remark A.3.2.5.

If $S$ is large enough so as to contain all the places of $F$ ramified over $\mathbf{Q}$ then $\nu_S$ is also characterized as the unique Haar measure such that the counting measure on $\mathcal{O}_{F,S}$ and the additive Tamagawa measure $\nu_S$ on $\mathbf{A}_{F,S}$ induce the unique Haar measure on the compact Hausdorff quotient $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$ (as per Theorem D.1.2.1) giving it volume 1.

The additive Tamagawa measure $\nu_S$ on $\mathbf{A}_{F,S}$ is self-dual with respect to the standard $S$-local additive character (see Example A.3.1.11). Fourier Inversion therefore holds with no normalizing constants and can be deduced from the local case by [RV, Prop.5.6(iii),p.186], where the index set in [RV, Prop.5.6,(5.2),p.186] is finite.

## PDF page 129

**3.3. S-LOCAL IDELIC ZETA FUNCTIONS** · **129**

THEOREM 3.3.1.1 ($S$-local Idelic Mellin transform of $S$-local adelic $\theta$-functions). *We let $f\in\mathcal{S}(\mathbf{A}_{F,S})$ be a Schwartz-Bruhat function and $c\in\Omega(J_{F,S})$. Then*

(1) *the integral*

$$
Z_S(f,c):=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}f(g)c(g)\,\mathrm{d}\mu_S(g) \tag{3.3.1.1}
$$

*converges absolutely over $\Omega(J_{F,S})_{>0}$, uniformly on compact subsets as a function of $c\in\Omega(J_{F,S})_{>0}$ and so is holomorphic in $c$.*

(a) *It satisfies the functional equation*

$$
Z_S(f,c)=\rho_S(c)Z_S(\widehat{f},\widehat{c}) \tag{3.3.1.2}
$$

*over $\Omega(J_{F,S})_{(0,1)}$, where $\rho_S$ is the meromorphic function on $\Omega(J_{F,S})$ defined by*

$$
\rho_S(c):=\prod_{v\in S}\rho_v(c_v) \tag{3.3.1.3}
$$

*with $c_v$ the restriction of $c$ along the closed continuous homomorphism $F_v^{\times}\to\mathrm{GL}_1(\mathbf{A}_{F,S})$, and $\rho_v$ the explicit meromorphic function on $\Omega(F_v^{\times})$ defined in [CF, Ch.XV,§2.5] for each $v\in S$.*

(b) *It extends to a meromorphic function on $\Omega(J_{F,S})$ whose poles, if any, are poles of $\rho_S$ and have pole order at most that of $\rho_S$.*

(2) *The integral*

$$
L_S(f,c):=\int_{J_{F,S}}\Phi_{F,S}(f)(g)c(g)\,\mathrm{d}\bar{\mu}_S(g) \tag{3.3.1.4}
$$

*is absolutely convergent over $\Omega(J_{F,S})_{>0}$ uniformly on compact subsets as a function of $c\in\Omega(J_{F,S})_{>0}$. In particular, $\Lambda_S(f,c)$ is a holomorphic function of $c\in\Omega(J_{F,S})_{>0}$.*

(3) *Let $\tau:\mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_{F,S})$ be a continuous homomorphic section to the $S$-idelic norm. Upon defining $\omega:=c|_{J^1_{F,S}}\in\widehat{J^1_{F,S}}$, the integral*

$$
\int_{\mathbf{R}_{>0}}\Phi_{F,S,\omega}(f)(\tau(t))c(\tau(t))\,\frac{\mathrm{d}t}{t} \tag{3.3.1.5}
$$

*is absolutely convergent over $\Omega(J_{F,S})_{>0}$ uniformly on compact subsets as a function of $c\in\Omega(J_{F,S})_{>0}$. In particular, it is holomorphic as a function of $c\in\Omega(J_{F,S})_{>0}$. Moreover, the following identity holds*

$$
L_S(f,c)=\int_{\mathbf{R}_{>0}}\Phi_{F,S,\omega}(f)(\tau(t))c(\tau(t))\,\frac{\mathrm{d}t}{t} \tag{3.3.1.6}
$$

*as holomorphic functions of $c\in\Omega(J_{F,S})_{>0}$, and both sides are, in turn, equal to $Z_S(f,c)$ from (3.3.1.1) over $\Omega(J_{F,S})_{>0}$.*

REMARK 3.3.1.2. As for the global version of Theorem 3.3.1.1 (see Theorem 3.2.2.1), by “uniform convergence on compact subsets” for the various integrals we mean that the sequence of truncated integrals over $\mathrm{GL}_1(\mathbf{A}_{F,S})^{[1/n,n]}$ converges as $n\to+\infty$, uniformly as $c$ varies over each compact subset of $\Omega(J_{F,S})_{>0}$. Here $\mathrm{GL}_1(\mathbf{A}_{F,S})^{[1/n,n]}$ is the closed subset given by those $S$-ideles whose $S$-idelic norm is in $[1/n,n]$.

PROOF OF THEOREM 3.3.1.1. By Proposition 2.1.4.1(1), for each $f\in\mathcal{S}(\mathbf{A}_{F,S})$ there exist $f_1,\ldots,f_m\in\mathcal{S}(\mathbf{A}_{F,S})$ of the form $f_k=f_{k,\infty}\otimes\bigotimes_{v\in S_f}f_{k,v}$, with $S_f:=S\cap\Sigma_{F,f}$, and $f_{k,\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ and $f_{k,v}\in\mathcal{S}(F_v)$ for each $v\in S_f$, with complex numbers $c_1,\ldots,c_m$, such that $f=\sum_{1\le k\le m}c_kf_k$.

Since formation of $Z_S(f,c)$, $L_S(f,c)$ and $\Phi_{F,S,\omega}$ is $\mathbf{C}$-linear with respect to $f$, we may and do rename any of the $f_k$ as $f$ and reduce to the case $f=f_{\infty}\otimes\bigotimes_{v\in S_f}f_v$, with $S_f:=S\cap\Sigma_{F,f}$, and $f_{\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ and $f_v\in\mathcal{S}(F_v)$ for each $v\in S_f$.

## PDF page 130

**130** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

(1) : By [RV, Prop.5.6(ii)], since the index set $I=S$ is finite and we may therefore choose $S_0=S$ in loc.cit., we have:

$$
\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}f(g)c(g)\,\mathrm{d}\mu_S(g)=\prod_{v\in S}\int_{F_v^{\times}}f_v(g_v)c_v(g_v)\,\mathrm{d}\mu_v(g_v)=\prod_{v\in S}Z_v(f_v,c_v)
$$

where $Z_v(f_v,c_v)$ is the local zeta integral of [CF, Ch.XV,Def.2.4.1], and $c_v=\psi_v(c)$, where $\psi_v:\Omega(J_{F,S})\to\Omega(F_v^{\times})$ is the holomorphic submersion defined as the restriction of the arbitrary continuous $S$-idelic quasi-character to the closed subgroup $F_v^{\times}\subset J_{F,S}$ (see (3.1.2.4), Lemma 3.1.2.1, and Lemma 3.1.2.2).

Since $S$ is finite, (1) reduces to the case $S=\Sigma_{\infty}$, since $Z_v(f_v,c_v)$ is holomorphic for $\sigma(c)>0$ and its defining integral

$$
Z_v(f_v,c_v):=\int_{F_v^{\times}}f_v(g)c_v(g)\,\mathrm{d}\mu_v(g) \tag{3.3.1.7}
$$

for $\mu_v$ the multiplicative local Tamagawa measure on $F_v^{\times}$ (see Definition A.3.2.2) converges absolutely and uniformly over $\Omega(F_v^{\times})_{>0}$, for each $v$ non-Archimedean.

We are under the assumption that $f_{\infty}$ itself is of the form $\bigotimes_{v\in S_{\infty}}f_v$ for $f_v\in\mathcal{S}(F_v)$ for each Archimedean place $v$ of $F$.

Then, by the same token as for the case when $v$ is a non-Archimedean place, the condition $\sigma(c)>0$, renders the singularity of $c_v\lvert\cdot\rvert_v^{-1}$, for each Archimedean place $v$ of $F$, $\nu_v$-integrable, where $\nu_v$ is the additive local Tamagawa measure on $F_v$. Boundedness of every Schwartz function $f_v\in\mathcal{S}(F_v)$ around the origin, combined with the rapid decay of $f_v$ for all $g\in F_v^{\times}$ as $\lvert g\rvert_v\to+\infty$, ensures that the integral from (3.3.1.7) defining $Z_v(f_v,c_v)$ for $v$ Archimedean, is absolutely and uniformly convergent over $\Omega(F_v^{\times})_{>0}$.

The same argument applies directly to the integral defining $Z_{S_{\infty}}(f_{\infty},c)$ for general $f_{\infty}\in\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ and for any $c\in\Omega(J_{F,S_{\infty}})_{>0}$: the condition $\sigma(c)>0$ ensures that the singularity of $\lvert\cdot\rvert_{F,S_{\infty}}^{-1}c$ is absolutely $\nu_{S_{\infty}}$-integrable, noting that $\lvert\cdot\rvert_{F,S_{\infty}}^{-1}\nu_{S_{\infty}}$ equals, as a Radon measure on $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$, $\mu_{S_{\infty}}$ up to a positive multiplicative constant. Boundedness of $f_{\infty}$ around the origin in the Euclidean space $\mathbf{A}_{F,S_{\infty}}$ combined with the rapid decay at infinity of $f_{\infty}$ on $\mathbf{A}_{F,S_{\infty}}$, ensures the absolute and uniform convergence of the integral in (3.3.1.1) in the special case $S=S_{\infty}$.

Now we digress to show a continuity property of the $S$-local zeta functions as we vary $f$ for fixed $c$. In practice and throughout the proof of Theorem 3.3.1.1 we will only need this for $S=S_{\infty}$. We deal with the general case now for later use:

LEMMA 3.3.1.3 ($Z_S$ is valued in tempered distributions). *For each fixed $c\in\Omega(J_{F,S})_{>0}$, the value $Z_S(f,c)$ is continuous in $f\in\mathcal{S}(\mathbf{A}_{F,S})$ with respect to the Hausdorff locally convex topology on $\mathcal{S}(\mathbf{A}_{F,S})$ for fixed each $c\in\Omega(J_{F,S})_{>0}$.*

PROOF. As in the proof of Lemma 3.2.2.3, since $\mathcal{S}(\mathbf{A}_{F,S})$ is an LF-space (see Proposition 2.1.4.1(2)) it suffices to show the integral in (3.3.1.1) defining $Z_S(f,c)$ is sequentially continuous in $f$ for each $c\in\Omega(J_{F,S_{\infty}})_{>0}$ (even though $\mathcal{S}(\mathbf{A}_{F,S})$ is *not* second-countable).

To see the sequential continuity, let $\{f_k\}_{k\ge 0}\subset\mathcal{S}(\mathbf{A}_{F,S})$ be a Cauchy sequence with limit $f\in\mathcal{S}(\mathbf{A}_{F,S})$. In particular, $\mathcal{B}:=\{f_k\}_{k\ge 0}\cup\{f\}$ is a bounded subset of $\mathcal{S}(\mathbf{A}_{F,S})$. By Theorem 3.3.1.1 (resting on Weil’s Quotient Integral Formula: Theorem D.1.2.1) we have the identity, as holomorphic functions over $\Omega(J_{F,S})_{>0}$:

$$
Z_S(f,c)=\int_{J_{F,S}}\Phi_{F,S}(f)(g)c(g)\,\mathrm{d}\bar{\mu}_S(g).
$$

By Theorem 2.4.2.1 and Proposition 2.3.1.2(4), upon choosing an integer $N>1$, we obtain the following bound pointwise over $J_{F,S}$ for all $u\in\mathcal{B}$:

$$
\lvert\Phi_{F,S}(u)(g)\rvert\le(C_{\mathcal{B},1}\lvert\log\lvert g\rvert_{F,S}\rvert^{\lvert S\rvert-1}+C_{\mathcal{B},2})\cdot 1_{J_{F,S}^{(0,1]}}(g)+C_{\mathcal{B},N}\lvert g\rvert_{F,S}^{-N}\cdot 1_{J_{F,S}^{\ge 1}}(g)
$$

## PDF page 131

**3.3. S-LOCAL IDELIC ZETA FUNCTIONS** · **131**

with suitable constants. By Dominated Convergence, it follows that $Z_S(f_k,c)\to Z_S(f,c)$ for each fixed $c\in\Omega(J_{F,S})_{>0}$

(In fact, the mode of convergence is much stronger: it is uniform as $c$ varies over an arbitrary vertical strip of bounded width within each connected component of $\Omega(J_{F,S})_{>0}$. The strongest form of sequential continuity will be identified later.) $\square$

Returning to the proof of part (1) of Theorem 3.3.1.1, the subspace $\bigotimes_{v\in S}\mathcal{S}(F_v)\subset\mathcal{S}(\mathbf{A}_{F,S})$ is dense and so to prove (3.3.1.2) with $\rho_S$ defined in (3.3.1.3) it suffices to check that for each $v\in S$ we have $Z_v(f_v,c_v)=\rho_v(c_v)Z_v(\widehat{f}_v,\widehat{c}_v)$, which holds by [CF, Ch.XV,Thm.2.4.1]. This proves (a) in part (1).

Since $Z_S(f,c)$ is holomorphic in $c\in\Omega(J_{F,S})_{>0}$, and $Z_S(\widehat{f},\widehat{c})$ is holomorphic in $c\in\Omega(J_{F,S})_{<1}$, the poles of the analytic continuation of $Z_S(f,\cdot)$, which we shall denote by $Z_S(f,\cdot)$ again, can only occur among the poles of $\rho_S$. This settles (b) in part (1).

(2) : Absolute and locally uniform convergence over $\Omega(J_{F,S})_{>0}$ of the integral in (3.3.1.5) is a consequence of the estimates in Proposition 2.3.1.2 (as $\lvert g\rvert_{F,S}\to+\infty$) and Proposition 2.4.3.1 (as $\lvert g\rvert_{F,S}\to 0^+$, see also Theorem 2.4.2.1).

(3) : This follows from compactness of $J^1_{F,S}$: the locally uniform convergence over $\Omega(J_{F,S})_{>0}(\omega)$ of the integral in (3.3.1.5) is a consequence of the estimates in Proposition 2.3.1.4 (as $\lvert g\rvert_{F,S}\to+\infty$ and for the $\omega$-homogeneous $\theta$-function) and Proposition 2.4.3.1 (as $\lvert g\rvert_{F,S}\to 0^+$ and for the $\omega$-homogeneous $\theta$-function, see also Theorem 2.4.2.1).

The identity in (3.3.1.6) holds by compactness of $J^1_{F,S}$ and the absolute convergence, for each $c\in\Omega(J_{F,S})_{>0}$, of the integral in (3.3.1.4) (which renders Theorem D.1.2.1 applicable). $\square$

$^{1}$

REMARK 3.3.1.4 (Tensor decomposition of $Z_S(\cdot,c)$ for $c\in\Omega(J_{F,S})$). Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places, $c\in\Omega(J_{F,S})_{>0}$ a fixed quasi-character. We call $c_{\infty}$ the restriction of $c$ to the closed subgroup $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$, and for each place $v$ of $F$ we call $c_v$ the restriction of $c$ to the closed subgroup $F_v^{\times}$.

We have built the linear functional $Z_S(\cdot,c)$ on $\mathcal{S}(\mathbf{A}_{F,S})$, and want to express the sense in which this is a (completed) tensor product of the functionals $Z_v(\cdot,c_v):\mathcal{S}(F_v)\to\mathbf{C}$ for $v\in S$. Note that these latter functionals are continuous by inspection of their definition as an integral when $c_v\in\Omega(F_v^{\times})_{>0}$ (using for Archimedean $v$ that the topology on $\mathcal{S}(F_v)$ can be described using $L^1$ seminorms) and via the local functional equation when $c_v\in\Omega(F_v^{\times})_{<1}$ (using also continuity of the local Fourier transform on $\mathcal{S}(F_v)$). Here we recall that the spaces $\mathcal{S}(F_v)$ for $v\in S_f$ are equipped with their finest locally convex topology (see Proposition 2.1.2.4 and Proposition C.2.5.1).

On the Archimedean factor $\mathbf{A}_{F,S_{\infty}}$ Schwartz-Bruhat functions $f_{\infty}$ are *not* generally built as a product of functions arising from the spaces $\mathcal{S}(F_v)$ for Archimedean $v$, so the purely algebraic tensorial aspects for handling the finite places don’t apply at the Archimedean places. Instead, we recall that naturally $\overline{\bigotimes}_{v\in S}\mathcal{S}(F_v)\simeq\mathcal{S}(\mathbf{A}_{F,S})$ (using the completion of the inductive tensor product, where completion is relevant only for the Archimdean places), so it makes sense to form the continuous linear functional

$$
\overline{\bigotimes}_{v\in S}Z_v(\cdot,c_v)
$$

on $\overline{\bigotimes}_{v\in S}\mathcal{S}(F_v)\simeq\mathcal{S}(\mathbf{A}_{F,S})$. Our claim is that this agrees with $Z_S(\cdot,c)$.

We first introduce the intermediate linear functional

$$
T:=Z_{S_{\infty}}(\cdot,c_{\infty})\otimes\bigotimes_{v\in S_f}Z_v(\cdot,c_v),
$$

---

$^{1}$Commented out a Remark on sequential continuity and local boundedness that is never cited.

## PDF page 132

**132** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

(with the inductive tensor product topology) which is continuous on $\mathcal{S}(\mathbf{A}_{F,S})$ since $Z_{S_{\infty}}(\cdot,c_{\infty})$ is continuous on $\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ by Lemma 3.3.1.3. The functional $T$ agrees with $Z_S(\cdot,c)$ on elementary tensors in $\mathcal{S}(\mathbf{A}_{F,S})\simeq\mathcal{S}(\mathbf{A}_{F,S_{\infty}})\otimes_{\iota}\mathcal{S}(\prod_{v\in S_f}F_v)$ (an inductive tensor product), which in turn linearly generate the tensor product linear space. Thus, $Z_S(\cdot,c)=Z_{S_{\infty}}(\cdot,c)\otimes\bigotimes_{v\in S_f}Z_v(\cdot,c_v)$ as linear functionals on $\mathcal{S}(\mathbf{A}_{F,S})$.

By denseness of $\bigotimes_{v\in S_{\infty}}C^\infty_c(F_v)$ in $C^\infty_c(\mathbf{A}_{F,S_{\infty}})$ [Tre, Thm. 39.2] and the denseness of $C^\infty_c(\mathbf{R}^n)$ in $\mathcal{S}(\mathbf{R}^n)$, the algebraic tensor product $\bigotimes_{v\in S_{\infty}}\mathcal{S}(F_v)\subset\mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ is dense (see also the proof of Lemma D.3.6.1). Thus, $Z_{S_{\infty}}(\cdot,c_{\infty})$ is the completed tensor product functional $\overline{\bigotimes}_{v\in S_{\infty}}Z_v(\cdot,c_v)$ because both are continuous and agree on the dense subspace generated by elementary tensors (treating separately the cases $c\in\Omega(J_{F,S})_{>0}$ and $c\in\Omega(J_{F,S})_{<1}$).

3.3.1.1. *Estimates on the correcting factor $\rho_S$ from the $S$-local functional equation.* The following result studies the growth conditions of the correcting factor $\rho_S(c)$ defined in (3.3.1.3), in the $S$-local functional equation (3.3.1.2) from Theorem 3.3.1.1.

PROPOSITION 3.3.1.5 (Asymptotic behavior of the $\rho_S$-factor). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

*Let $\rho_S\in\mathscr{M}(\Omega(J_{F,S}))$ be the meromorphic function on $\Omega(J_{F,S})$ defined in (3.3.1.3).*

(1) *As meromorphic functions on $\Omega(J_{F,S})$, the following identities:*

$$
\rho_S(c)\,\rho_S(\widehat{c})=c(-1),\quad \rho_S(\bar{c})=c(-1)\overline{\rho_S(c)}. \tag{3.3.1.8}
$$

(2) *On the relative vertical line $\{\sigma(c)=1/2\}\subset\Omega(J_{F,S})$, $\rho_S$ is regular and valued in $\mathrm{U}(1)$, i.e. we have:*

$$
\lvert\rho_S(\chi\lvert\cdot\rvert_{F,S}^{1/2+i\mathbf{R}})\rvert=1 \tag{3.3.1.9}
$$

*for any continuous character $\chi\in\widehat{J_{F,S}}$.*

(3) *For any continuous character $\chi\in\widehat{J_{F,S}}$ and any integer $k\ge 0$, the holomorphic derivative:*

$$
\frac{\partial^k}{\partial s^k}\rho_S(\chi\lvert\cdot\rvert_{F,S}^s) \tag{3.3.1.10}
$$

*is holomorphic over $\mathbf{C}_{>0}$, and we have:*

$$
\frac{\partial^k}{\partial s^k}\rho_S(\chi\lvert\cdot\rvert_{F,S}^s)=O_{\sigma}(\lvert\tau\rvert^{\sigma-1/2}\lvert\log(\lvert\tau\rvert)\rvert^k) \tag{3.3.1.11}
$$

*for $s=\sigma+i\tau$, and for each fixed $\sigma>0$, as $\lvert\tau\rvert\to+\infty$.*

PROOF. (1) : By design of $\rho_S$ from (3.3.1.3), we have $\rho_S=\prod_{v\in S}\rho_v$, for $\rho_v$ is the explicit meromorphic function on $\Omega(F_v^{\times})$ defined in [CF, Ch.XV,§2.5], for each $v\in S$.

By [CF, Ch.XV,§2.4,Lemma 2.4.3], we have, for each $v\in S$:

$$
\rho_v(\psi_v(c))\rho_v(\widehat{\psi_v(c)})=\psi_v(c)(-1),\ \rho_v(\overline{\psi_v(c)})=\psi_v(c)(-1)\overline{\rho_v(\psi_v(c))} \tag{3.3.1.12}
$$

where $\psi_v:\Omega(J_{F,S})\to\Omega(F_v^{\times})$ is the holomorphic submersion given by restricting a continuous $S$-idelic quasi-character $c\in\Omega(J_{F,S})$ to the closed subgroup $F_v^{\times}\subset J_{F,S}$. Explicitly, for any continuous character $\chi\in\widehat{J_{F,S}}$, we have $\psi_v(\chi\lvert\cdot\rvert_{F,S}^s)=\chi_v\lvert\cdot\rvert_v^s$, and hence we have:

$$
\rho_v(\chi_v\lvert\cdot\rvert_v^s)\rho_v(\chi_v^{-1}\lvert\cdot\rvert_v^{1-s})=\chi_v(-1),\ \rho_v(\chi_v^{-1}\lvert\cdot\rvert_v^{\bar{s}})=\chi_v(-1)\overline{\rho_v(\chi_v\lvert\cdot\rvert_v^s)} \tag{3.3.1.13}
$$

and this implies that (3.3.1.8) holds, away from the poles of $\rho_S(c)$ and $\rho_S(\widehat{c})$.

(2) : If $c=\chi\lvert\cdot\rvert_{F,S}^{1/2+it}$ for $\chi\in\widehat{J_{F,S}}$ and $t\in\mathbf{R}$, then $\rho_S(\widehat{c})=\rho_S(\chi^{-1}\lvert\cdot\rvert_{F,S}^{1/2-it})=\rho_S(\bar{c})$ from (3.3.1.8), and we have $\rho_S(\bar{c})=c(-1)\overline{\rho_S(c)}$, from which we deduce:

$$
\rho_S(\chi\lvert\cdot\rvert_{F,S}^{1/2+it})\overline{\rho_S(\chi\lvert\cdot\rvert_{F,S}^{1/2+it})}\chi(-1)=\chi(-1) \tag{3.3.1.14}
$$

## PDF page 133

**3.3. S-LOCAL IDELIC ZETA FUNCTIONS** · **133**

and since $\chi(-1)\ne 0$, we deduce from (3.3.1.14) that (3.3.1.9) holds. It follows that $\rho_S$ is meromorphic and with neither zeros nor poles on the vertical line $\{\sigma(c)=1/2\}$, hence it is regular there.

(3) : We fix a real number $\sigma>0$. Upon choosing an enumeration for the finitely many places of $F$ contained in $S$, i.e. $S=\{v_1,\dots,v_N\}$, we have, as meromorphic functions of $s\in\mathbf{C}$:

$$
\frac{\partial^k}{\partial s^k}\rho_S(\chi\lvert\cdot\rvert_{F,S}^s)=\sum_{(i_1,\dots,i_N)\in\mathbf{N}^N,k=i_1+\dots+i_N}\binom{k}{i_1,\dots,i_N}\prod_{1\le j\le N}\frac{\partial^{i_j}}{\partial s^{i_j}}\rho_{v_j}(\chi_{v_j}\lvert\cdot\rvert_{v_j}^s) \tag{3.3.1.15}
$$

the sum in (3.3.1.15) being finite.

We analyze for every integer $k\ge 0$ and each $v\in S$, the derivative:

$$
\frac{\partial^k}{\partial s^k}\rho_v(\chi_v\lvert\cdot\rvert_v^s). \tag{3.3.1.16}
$$

If $v$ is non-Archimedean of prime residue characteristic $p$, associated to the prime ideal $\mathfrak{p}_v\subset\mathcal{O}_F$, locally generated by $\pi_v\in\mathcal{O}_{F_v}$, then if $\chi_v$ is unramified, we have, by [CF, Ch.XV,§2.5,p.322]:

$$
\rho_v(\lvert\cdot\rvert_v^s)=N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{s-1/2}\frac{1-N(\mathfrak{p}_v)^{s-1}}{1-N(\mathfrak{p}_v)^{-s}}
$$

and if $\chi_v$ is ramified, then up to a vertical translation (noting that all assertions in (3) are stable under replacement of $s$ by a vertical translate) we may assume $\chi_v(\pi_v)=1$, and we have

$$
\rho_v(\chi_v\lvert\cdot\rvert_v^s)=N(\mathfrak{d}_{F_v/\mathbf{Q}_p}\mathfrak{f}_{\chi_v})^{s-1/2}\rho_0(\chi_v\lvert\cdot\rvert_v^s)
$$

where $\rho_0(\chi_v\lvert\cdot\rvert_v^s)=\rho_0(\chi_v)$ is the root number, independent of $s$ and valued in $\mathrm{U}(1)$, and $\mathfrak{f}_{\chi_v}$ is the conductor of $\chi_v$.

In the unramified case, it is enough to show that, for every integer $k\ge 0$:

$$
\partial_s^k N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{s-1/2},\; \partial_s^k((1-N(\mathfrak{p}_v)^{s-1})(1-N(\mathfrak{p}_v)^{-s})^{-1})
$$

are regular and bounded over $\{\mathrm{Re}(s)=\sigma\}$.

For the former, we have $\partial_s^k N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{s-1/2}=(\log N(\mathfrak{p}_v))^k N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{s-1/2}$, which is indeed regular and bounded over $\{\mathrm{Re}(s)=\sigma\}$.

For the latter, it is enough to show that both $\partial_s^k(1-N(\mathfrak{p}_v)^{s-1})$ and $\partial_s^k((1-N(\mathfrak{p}_v)^{-s})^{-1})$ are regular and bounded over $\{\mathrm{Re}(s)=\sigma\}$ for every integer $k\ge 0$.

We have:

$$
\partial_s^k(1-N(\mathfrak{p}_v)^{s-1})=-(\log N(\mathfrak{p}_v))^k N(\mathfrak{p}_v)^{s-1}
$$

which is indeed regular and bounded over $\{\mathrm{Re}(s)=\sigma\}$ for every integer $k\ge 0$.

We have:

$$
\partial_s^k(1-N(\mathfrak{p}_v)^{-s})=-(-1)^k(\log N(\mathfrak{p}_v))^k N(\mathfrak{p}_v)^{-s}
$$

which is, for each integer $k\ge 0$, regular, nowhere vanishing and, on $\{\mathrm{Re}(s)=\sigma\}$, of constant absolute value $(\log N(\mathfrak{p}_v))^k N(\mathfrak{p}_v)^{-\sigma}$.

We now have:

$$
0=\sum_{(i,j)\in\mathbf{N}^2,i+j=k}\binom{k}{i,j}(\partial_s^i(1-N(\mathfrak{p}_v)^{-s}))\cdot(\partial_s^j((1-N(\mathfrak{p}_v)^{-s})^{-1})) \tag{3.3.1.17}
$$

$$
=\sum_{(i,j)\in\mathbf{N}^2,i+j=k}\binom{k}{i,j}(-1)^{i+1}(\log N(\mathfrak{p}_v))^i N(\mathfrak{p}_v)^{-s}\cdot(\partial_s^j((1-N(\mathfrak{p}_v)^{-s})^{-1})) \tag{3.3.1.18}
$$

which, by induction on $k\ge 0$, the base case $k=0$ asserting that $(1-N(\mathfrak{p}_v)^{-s})^{-1}$ is regular and bounded on $\{\mathrm{Re}(s)=\sigma\}$, which is indeed the case, implies that so is $\partial_s^k((1-N(\mathfrak{p}_v)^{-s})^{-1}$ over $\{\mathrm{Re}(s)=\sigma\}$.

## PDF page 134

**134** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

In the ramified case:

$$
\partial_s^k\rho_v(\chi_v\lvert\cdot\rvert_v^s)=(\log N(\mathfrak{d}_{F_v/\mathbf{Q}_p}\mathfrak{f}_{\chi_v})^k\rho_0(\chi_v)N(\mathfrak{d}_{F_v/\mathbf{Q}_p}\mathfrak{f}_{\chi_v})^{s-1/2}
$$

which is regular and bounded over $\{\mathrm{Re}(s)=\sigma\}$ for any integer $k\ge 0$.

We are reduced to analyzing $\rho_v(\chi_v\lvert\cdot\rvert_v^s)$ for $\{\mathrm{Re}(s)=\sigma\}$, for $v$ Archimedean.

In light of [CF, Ch.XV,§2.5,pp.317,319], it is enough to prove that the following meromorphic functions on the complex $s$-plane obtained from the $\Gamma$-function:

$$
\frac{\Gamma(s/2)}{\Gamma((1-s)/2)},\; \frac{\Gamma((s+1)/2)}{\Gamma(((1-s)+1)/2)},\; \frac{\Gamma(s+n/2)}{\Gamma(1-s+n/2)} \tag{3.3.1.19}
$$

for every integer $n\ge 0$, are, over the vertical line $\{\mathrm{Re}(s)=\sigma\}$, $O_{\sigma}(|\tau|^{\sigma-1/2}|\log(|\tau|)|^k)$ for any integer $k\ge 0$.

They are all holomorphic over $\mathbf{C}_{>0}$ (see [CF, Ch.XV,§2.4,Cor.2.4.1,p.316] and [CF, Ch.XV,§2.5,pp.317,319], noting that $\rho_v(c)$ equals the three functions in (3.3.1.19) up to a factor that is entire, nowhere vanishing, and, on the vertical line $\{\mathrm{Re}(s)=\sigma\}$ is bounded, with bounded derivatives of any order. Such factor is, respectively, $\pi^{1/2-s}$, $i\pi^{1/2-s}$, $(-i)^n(2\pi)^{1-2s}$).

Since $\Gamma(z+1)=z\Gamma(z)$ as meromorphic functions on the complex $z$-plane, it is enough to prove that the holomorphic derivative of order $k\ge 0$ of the following three meromorphic functions on the complex $s$-plane:

$$
\frac{\Gamma(s/2)}{\Gamma((1-s)/2)},\; \frac{\Gamma((s+1)/2)}{\Gamma(((1-s)+1)/2)},\; \frac{\Gamma(s+1/2)}{\Gamma(1-s+1/2)} \tag{3.3.1.20}
$$

is, on the vertical line $\{\mathrm{Re}(s)=\sigma\}$, $O_{\sigma}(|\tau|^{\sigma-1/2}|\log(|\tau|)|^k)$.

We have, for $k=1$:

$$
\frac{\partial}{\partial s}\frac{\Gamma(s/2)}{\Gamma((1-s)/2)}=\frac{(1/2)\Gamma'(s/2)}{\Gamma((1-s)/2)}-\frac{-(1/2)\Gamma(s/2)\Gamma'((1-s)/2)}{\Gamma((1-s)/2)^2} \tag{3.3.1.21}
$$

$$
=\frac{1}{2}\frac{\Gamma(s/2)}{\Gamma((1-s)/2)}\left\{\frac{\Gamma'(s/2)}{\Gamma(s/2)}+\frac{\Gamma'((1-s)/2)}{\Gamma((1-s)/2)}\right\} \tag{3.3.1.22}
$$

$$
=\frac{1}{2}\frac{\Gamma(s/2)}{\Gamma((1-s)/2)}\{\psi(s/2)+\psi((1-s)/2)\} \tag{3.3.1.23}
$$

$$
\tag{3.3.1.24}
$$

which, over $\{\mathrm{Re}(s)=\sigma\}$, is indeed $O_{\sigma}(|\tau|^{\sigma-1/2}|\log(|\tau|)|)$.

A similar argument applies to the holomorphic derivative of order $k=1$ of the remaining two functions in (3.3.1.20) over the vertical lines in $\mathbf{C}_{>0}$.

Induction on $k\ge 0$ using Stirling’s Approximation for each of the functions $f(s)$ in (3.3.1.20), combined with an argument similar to the calculation in (3.3.1.21) applied to the logarithmic derivative of $\partial_s^{k-1}f(s)$, leads to the bound $\partial_s^k f(\sigma+i\tau)=O_{\sigma}(|\tau|^{\sigma-1/2}|\log(|\tau|)|^k)$, as $|\tau|\to+\infty$. $\square$

We note that Theorem 3.3.1.5 implies that $\rho_S(c)$ grows at most polynomially over all the vertical lines in $\Omega(J_{F,S})_{>0}$, and on each such line its derivative of order $k\ge 0$ is asymptotically bounded above by $|\tau|^{\sigma-1/2}|\log(|\tau|)|^k$, $\tau$ being the ordinate, and as $|\tau|\to+\infty$.

In particular, along the relative vertical line $\sigma(c)=1/2$, $\rho_S(c)$ is bounded (in fact, valued in $\mathrm{U}(1)$), and its derivative of order $k\ge 0$ grows slowly, at most as $|\log(|\tau|)|^k$.

We now let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We define:

$$
L_S(c):=\prod_{v\in S}L_v(c_v) \tag{3.3.1.25}
$$

## PDF page 135

**3.3. S-LOCAL IDELIC ZETA FUNCTIONS** · **135**

where $L_v(c_v)$ is the local Euler factor at $v$ of the Hecke $L$-function $L(c)$ of $F$, and $c_v$ is the image of $c\in\Omega(J_{F,S})$ under the local analytic isomorphism to $\Omega(F_v^{\times})$ obtained by restricting $c$ along the continuous injective closed group homomorphism $F_v^{\times}\subset J_{F,S}$. We refer to $L_S(c)$ as the $S$-local Hecke $L$-function of $F$.

REMARK 3.3.1.6 (On partial Euler products). For any choice of connected component of $\Omega(J_{F,S})$, the restriction of $L_S(c)$ to that connected component is a partial Euler product for the Hecke $L$-function $L(c)$ restricted to the same connected component. Indeed, upon choosing a holomorphic parametrization $\{\chi\lvert\cdot\rvert_{F,S}^s, s\in\mathbf{C}\}$ of $\Omega(J_{F,S})$, equivalently, choosing a set of continuous characters $\widetilde{J_{F,S}^1}:=\{\chi\in\widehat{J_{F,S}}\}$ representing the elements of $\widehat{J_{F,S}^1}$, then, for each $\chi\in\widetilde{J_{F,S}^1}$ there exists a continuous character $\chi'\in\widehat{C_F}$ such that its restriction to $C_{F,S}\subset C_F$ agrees with the continuous character of $C_{F,S}$ obtained by composition of the continuous quotient homomorphism $C_{F,S}\to J_{F,S}$ followed by $\chi$.

Indeed, upon calling $\chi_S$ such composition, this is a continuous character of the open, hence closed (by [DE, Lemma 1.1.7(c)]) subgroup $C_{F,S}\subset C_F$, and by [DE, Cor.3.6.2], there exists a continuous character $\chi'\in\widehat{C_F}$ extending $\chi_S$ from $C_{F,S}$ to $C_F$. There therefore exists a finite set of places $S'$ of $F$ containing $S$ such that $\chi'$ is unramified outside $S'$, and large enough so as to have that $\mathrm{Pic}(\mathcal{O}_{F,S'})=1$ holds.

3.3.1.2. *$\epsilon_S$-factors and the $S$-local functional equation.* In the Lemma below, we revisit the $S$-local functional equation from Theorem 3.3.1.1, and rewrite it in terms of $\epsilon_S$-factors.

LEMMA 3.3.1.7 ($\epsilon_S$-factors and the $S$-local functional equation). *Let $F$ be a number field, $S$ a finite set of places containing all Archimedean places. Let $\omega$ be a continuous unitary character of $J_{F,S}^1$.*

(1) *For every $f\in\mathcal{S}(\mathbf{A}_{F,S})$, $Z_S(f,c)$ is Schwartz on every vertical line of $\Omega(J_{F,S})_{>0}$, and for each $\varepsilon>0$ it is uniformly Schwartz on vertical strips within $\Omega(J_{F,S})_{>\varepsilon}$ of bounded width (in the sense that the vertical decay constants can be chosen uniformly over such strips).*

(2) The meromorphic function

$$
\frac{Z_S(f,c)}{L_S(c)} \tag{3.3.1.26}
$$

*on $\Omega(J_{F,S})$ is entire and satisfies the following growth condition for every continuous unitary character $\chi$ of $J_{F,S}$:*

$$
\frac{Z_S(f,\chi\lvert\cdot\rvert_{F,S}^{\sigma+it})}{L_S(\chi\lvert\cdot\rvert_{F,S}^{\sigma+it})}\ll_{N,a,b}|t|^{-\{N+(\sigma-\frac12)(\frac{r_1}{2}+r_2)\}}\cdot e^{\frac{\pi t}{2}(\frac{r_1}{2}+r_2)} \tag{3.3.1.27}
$$

*for each integer $N\ge 1$ as $|t|\to+\infty$, and uniformly as $\sigma$ varies over the arbitrary bounded interval $[a,b]$ of $\mathbf{R}_{>0}$.*

(3) *There exists an entire function $\epsilon_S$ on $\Omega(J_{F,S})$, such that:*

(a) As meromorphic functions of $c\in\Omega(J_{F,S})$,

$$
\epsilon_S(c)=\prod_{v\in S}\epsilon_v(c_v) \tag{3.3.1.28}
$$

*where $\epsilon_v$ is the entire function on $\Omega(F_v^{\times})$ defined by:*

(i) ($v$ real) $\epsilon_v(c_v)=1$ if $c_v\in\Omega(F_v^{\times})(1)$, $\epsilon_v(c_v)=-i$ if $c_v\in\Omega(F_v^{\times})(\mathrm{sgn})$,

(ii) *($v$ complex) $\epsilon_v(c_v)=(-i)^{|n|}$ if $c_v\in\Omega(F_v^{\times})(\chi_n)$ with $\chi_n:z\mapsto e^{in\theta}$ for $z=re^{i\theta}$ with $r>0$ and $n\in\mathbf{Z}$,*

(iii) *($v$ is non-Archimedean of residue characteristic $p$) on unramified $c_v$ we have*

$$
\epsilon_v(\lvert\cdot\rvert_v^s):=N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{s-1/2} \tag{3.3.1.29}
$$

## PDF page 136

**136** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

*and if $c_v=\chi_v\lvert\cdot\rvert_v^s$ is ramified at $v$, with $\chi_v$ normalized to satisfy $\chi_v(\pi_v)=1$ for a choice of local uniformizer $\pi_v$ at $v$ then*

$$
\epsilon_v(\chi_v\lvert\cdot\rvert_v^s):=N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{s-1/2}\rho_0(\chi_v\lvert\cdot\rvert_v^s) \tag{3.3.1.30}
$$

*where $\rho_0(\chi_v\lvert\cdot\rvert_v^s)$ is the Gauss sum $N(\mathfrak{f})^{-1/2}\sum_u\chi_v(u)e^{2\pi i\Lambda_v(u/\pi_v^{m_v})}$, with $\mathfrak{f}$ the conductor of $\chi_v$, $m_v:=v(\mathfrak{d}_{F_v/\mathbf{Q}_p}\mathfrak{f})$, and the sum over any set of representatives for the finite coset space $\mathcal{O}_{F_v}^{\times}/(1+\mathfrak{f})$.*

(b) *$\epsilon_S$ is entire over $\Omega(J_{F,S})$ and nowhere-vanishing, and we have $|\epsilon_S(c)|=1$ for $\sigma(c)=1/2$.*

(c) *The following identity of entire functions over $\Omega(J_{F,S})$:*

$$
\frac{Z_S(f,c)}{L_S(c)}=\epsilon_S(c)\frac{L_S(\widehat{f},\widehat{c})}{L_S(\widehat{c})} \tag{3.3.1.31}
$$

*holds for all Schwartz-Bruhat functions $f\in\mathcal{S}(\mathbf{A}_{F,S})$.*

(d) The meromorphic function $\rho_S$ from (3.3.1.3) satisfies

$$
\rho_S(c)=\epsilon_S(c)\frac{L_S(c)}{L_S(\widehat{c})} \tag{3.3.1.32}
$$

as meromorphic functions over $\Omega(J_{F,S})$.

REMARK 3.3.1.8. For each place $v\in S$, the standard character $\psi_{v,\mathrm{std}}:x\mapsto e^{2\pi i\Lambda_v(x)}$ of $F_v$ in Lemma 3.3.1.7 is defined for $v$ non-Archimedean of residue characteristic $p$ in Example A.3.1.6 as $\psi_{p,\mathrm{std}}(\mathrm{Tr}_{F_v/\mathbf{Q}_p}(\cdot))$ with $\psi_{p,\mathrm{std}}$ the standard character on $\mathbf{Q}_p$ from Example A.3.1.6 and $\Lambda_v=\mathrm{Tr}_{F_v/\mathbf{Q}_p}$. For Archimedean $v$, it is defined in Example A.3.1.5 with $\Lambda_v$ the respective local trace form (see Remark A.3.2.5). This standard character for each $v$ makes the additive local Tamagawa measure $\nu_v$ from Definition A.3.1.2 on $F_v$ be self-dual upon defining the Fourier transform on $\mathcal{S}(F_v)$ using the additive character $\psi_{v,\mathrm{std}}$ on $F_v$. In effect, $\epsilon_S$ depends on a choice of continuous additive character of $F_v$ for each $v\in S$, which we have taken to be the standard additive characters. We further refer the reader to [CF, Ch.XV,§2.5].

PROOF OF LEMMA 3.3.1.7. Let $f\in\mathcal{S}(\mathbf{A}_{F,S})$ be an arbitrary Schwartz-Bruhat function.

(1) : It is enough to check the assertion on each connected component of $\Omega(J_{F,S})_{>0}$. Upon choosing $\chi\in\widehat{J_{F,S}}$, then $Z_S(f,\chi\lvert\cdot\rvert_{F,S}^s)$ is the Mellin transform of the function $\phi(t):=\chi(\tau(t))\Phi_{F,S,\chi|_{J_{F,S}^1}}(f)(\tau(t))$ for $\tau$ a choice of continuous homomorphic section to the $S$-idelic norm.

By Corollary 2.4.3.2 combined with Proposition 2.3.1.4(2), for every $\varepsilon>0$ the function $t^{\varepsilon}\phi(t)$ is, as a function of $t>0$, Schwartz-Bruhat over $\mathbf{R}_{>0}$ with (forward) semi-exponential decay (see Definition B.2.1.1(1)). Concretely, this means that for every integer $N\ge 1$ there exist real numbers $T_N>0$ and $C_N>0$ such that:

$$
|t^{\varepsilon}\phi(t)|<C_N t^{-N}
$$

for all $t>T_N$.

It follows that $Z_S(f,\chi\lvert\cdot\rvert_{F,S}^s)=M(\phi)(s)$ is holomorphic over the half-plane $\mathbf{C}_{>0}$ and Schwartz on vertical strips of bounded width (meaning Schwartz on each vertical line, and with uniform decay constants on all such lines in the strip) upon applying Lemma B.2.1.5 to $t^{\varepsilon}\phi(t)$ for every $\varepsilon>0$.

(2) and (3) : The holomorphy of $Z_S(f,c)/L_S(c)$ over $\Omega(J_{F,S})_{>0}$ follows from (1), and over $\Omega(J_{F,S})_{<0}$ from the functional equation of (3.3.1.2) from Theorem 3.3.1.1. Since $Z_S(f,c)$ and $Z_S(\widehat{f},\widehat{c})$ are both holomorphic over $\Omega(J_{F,S})_{(0,1)}$ by Theorem 3.3.1.1(1), then from (3.3.1.2) the function $Z_S(f,\cdot)$ can only have poles located at the poles of the meromorphic function $\rho_S$ defined in (3.3.1.3).

By [CF, Ch.XV,Lemma 2.4.2] (and the incipit of the proof of [CF, Ch.XV,Thm.2.4.1]), for every $v\in S$ we have $\rho_v(c_v)=\epsilon_v(c_v)L_v(c_v)/L_v(\widehat{c}_v)$, so $\rho_S(c)=\epsilon_S(c)L_S(c)/L_S(\widehat{c})$ with $1/L_S(\widehat{c})$ entire, so $Z_S(f,\cdot)$ can only

## PDF page 137

**3.3. S-LOCAL IDELIC ZETA FUNCTIONS** · **137**

have poles at the poles of $L_S$. We can therefore rewrite the functional equation from (3.3.1.2) as:

$$
\frac{Z_S(f,c)}{L_S(c)}=\epsilon_S(c)\frac{Z_S(\widehat{f},\widehat{c})}{L_S(\widehat{c})} \tag{3.3.1.33}
$$

as meromorphic functions over $\Omega(J_{F,S})$. Since the left side is holomorphic over $\Omega(J_{F,S})_{>0}$ and the right side is holomorphic over $\Omega(J_{F,S})_{<1}$, we deduce that each side extends to a holomorphic function over $\Omega(J_{F,S})$.

By (3.3.1.33), it is enough to check the Schwartz condition uniformly over the vertical strips of bounded width of $\Omega(J_{F,S})_{>0}$.

For $v$ non-Archimedean, we analyze $Z_v(f_v,c_v)/L_v(c_v)$. For $c_v$ ramified, we have $L_v(c_v)=1$, and for $c_v$ unramified, $1/L_v(c_v)$ is bounded uniformly over the vertical strips of bounded width of $\Omega(F_v^{\times})_{>0}$ (away from the edge). Since $Z_v(f_v,c_v)$ is also bounded uniformly on such vertical strips, so is $Z_v(f_v,c_v)/L_v(c_v)$.

Let $[a,b]\subset\mathbf{R}_{>0}$ be an arbitrary non-empty bounded interval. It follows that $Z_S(f,\chi\lvert\cdot\rvert_{F,S}^{\sigma+it})/L_S(\chi\lvert\cdot\rvert_{F,S}^{\sigma+it})$ can be written as:

$$
\frac{Z_S(f,\chi\lvert\cdot\rvert_{F,S}^{\sigma+it})}{L_S(\chi\lvert\cdot\rvert_{F,S}^{\sigma+it})}=\epsilon_S(\chi\lvert\cdot\rvert_{F,S}^{\sigma+it})\frac{1}{L_{S_{\infty}}(\chi\lvert\cdot\rvert_{F,S_{\infty}}^{\sigma+it})}\cdot\frac{Z_S(f,\chi\lvert\cdot\rvert_{F,S}^{\sigma+it})}{\prod_{v\in S_f}L_v(\chi_v\lvert\cdot\rvert_v^{\sigma+it})} \tag{3.3.1.34}
$$

with $S_f:=S\cap\Sigma_{F,f}$. The third factor is Schwartz as a function of $t$, uniformly with respect to $\sigma\in[a,b]$.$^{2}$ Since $1/L_{S_{\infty}}(\chi\lvert\cdot\rvert_{F,S_{\infty}}^{\sigma+it})$ is a product of vertical translations of $\Gamma$-functions, the estimate from (3.3.1.27) holds by Stirling Approximation (see specifically [IK, Ch.5,§A.4,(5.114),(5.115),p.151]).

The formula for $\epsilon_v$ for each $v\in S$ follows by comparing (3.3.1.2) with (3.3.1.33), as in the proof of [RV, Ch.7,§7.1,Thm.7.2,p.246]. $\square$

**3.3.2. Poles and Residues of local $L$-functions.** We review here basic facts on the poles and residues of the local $Z$-functions $Z_v(f,c)$, defined, for $c\in\Omega(F_v^{\times})_{>0}$, by the absolutely and uniformly convergent integral:

$$
Z_v(f,c):=\int_{F_v^{\times}}f(g)c(g)\,\mathrm{d}\mu_v(g) \tag{3.3.2.1}
$$

for $f\in\mathcal{S}(F_v)$, $c\in\Omega(F_v^{\times})$, for $v$ a place of the number field $F$, and $\mu_v$ the local multiplicative Tamagawa measure on $F_v^{\times}$ (see Definition A.3.2.2).

We refer the reader to [CF, Ch.XV,§2.4,Def.2.4.1], and to [CF, Ch.XV,§2.4,Thm.2.4.1], for basic properties of the local $Z$-functions $Z_v(f,c)$, some of which we have recalled in Theorem 3.3.1.1.

We denote by $Z_v(f,c)$ the unique analytic continuation of the holomorphic function defined on $\Omega(F_v^{\times})_{>0}$ by the integral in (3.3.2.1), to a meromorphic function over the local Riemann surface $\Omega(F_v^{\times})$.

As $f\in\mathcal{S}(F_v)$ varies, the assignment $Z_v(f,c)$ for $c\in\Omega(F_v^{\times})$ defines a meromorphic $\mathcal{S}(F_v)'_{\beta}$-valued function on the Riemann surface $\Omega(F_v^{\times})$. We denote the functional on $\mathcal{S}(F_v)$ obtained by varying $f$ in $Z_v(f,c)$ for each fixed $c\in\Omega(F_v^{\times})$ by $Z_v(\cdot,c)$ (for each fixed $c$ it is a tempered distribution on $F_v$, i.e. it is continuous as $f$ varies over $\mathcal{S}(F_v)$) and if we further vary $c$ then we denote the resulting function $\Omega(F_v^{\times})$ valued in $\mathcal{S}(F_v)'_{\beta}$ by $Z_v$, a meromorphic distribution-valued function on $\Omega(F_v^{\times})$. We will be returning on this perspective later in this Chapter and the next Chapters on this work.

The theory of vector-valued holomorphic and meromorphic functions (which is discussed in Appendix C and specifically in §C.5.2 and §C.5.3) will be used occasionally throughout this work when we want to think about certain residue operators and coefficients of principal parts, as themselves operators on a space of vector valued meromorphic functions. This perspective has indeed appeared in relevant literature before: we have in mind Sarnak's paper on the equidistribution of long horocycles (see [Sarnak]) where certain residue operators arise of meromorphic vector-valued Eisenstein series. We will return to Sarnak's paper in Chapters 7 and 8 of this work when we explain the connection of our work with a number of elements of Deninger's program.

---

$^{2}$Need to give a reference for a proof of this “uniform Schwartz” assertion.

## PDF page 138

**138** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

3.3.2.1. *Poles and residues of the local $Z$-functions at the Archimedean places.* Recall from §3.1.1 on generalities concerning quasi-characters of modulated groups, that for $G$ a modulated group (i.e. a Hausdorff locally compact abelian group equipped with a continuous proper homomorphism $\lvert\cdot\rvert_G:G\to\mathbf{R}_{>0}$, which we assume to be non-trivial and call *module*) the set of continuous quasi-characters (i.e. continuous homomorphisms $G\to\mathbf{C}^{\times}$), denoted $\Omega(G)$, is a Riemann surface whose connected components are cylinders, if the image of $\lvert\cdot\rvert_G$ is a discrete subgroup of $\mathbf{R}_{>0}$, complex planes, if $\lvert\cdot\rvert_G$ is surjective.

We have denoted in §3.1.1 by $\Omega(G)(c)$ the connected component of $\Omega(G)$ that contains the quasi-character $c$. If $\omega\in\widehat{G^1}$, with $G^1$ the compact kernel of $\lvert\cdot\rvert_G$, then we denote by $\Omega(G)(\omega)$ the connected component parametrized by $\omega$ (when we view $\Omega(G)$ as fibred over $\widehat{G^1}$ by restricting quasi-characters of $G$ to characters of $G^1$). In the former case we call $G$ *discretely modulated* and in the latter we term it $\mathbf{R}_{>0}$-*modulated*. The local fields $F_v$ for $v$ a non-Archimedean place of the number field $F$ are all discretely modulated by the $v$-adic absolute value $\lvert\cdot\rvert_v$. The Archimedean local fields $F_v$ are $\mathbf{R}_{>0}$-modulated.

We recall here the following result on local $Z$-functions:

LEMMA 3.3.2.1 (Poles and Residues of the local $Z$-functions - Archimedean places). *Let $F$ be a number field, $v$ an Archimedean place.*

(1) *The poles of the meromorphic function $Z_v$ on $\Omega(F_v^{\times})$ valued in tempered distributions are simple and located at the following quasi-characters:*

(1) *For $v$ real and $c\in\Omega(F_v^{\times})(1)$:*

$$
c_{0,m}(x)=\lvert x\rvert_v^{-m},\; m\in 2\mathbf{N} \tag{3.3.2.2}
$$

*and for $v$ real and $c\in\Omega(F_v^{\times})(\mathrm{sgn})$:*

$$
c_{1,m}(x)=x^{-1}\lvert x\rvert_v^{-m},\; m\in 2\mathbf{N} \tag{3.3.2.3}
$$

(2) *If $v$ is complex and, fixing $r\in\mathbf{Z}$, $r\ge 0$, upon calling $\chi_r(z)=\chi_r(Re^{i\theta})=e^{ir\theta}$, then for $c\in\Omega(F_v^{\times})(\chi_r)$:*

$$
c_{r,m}(z)=\bar{z}^{-r}\lvert z\rvert_v^{-m},\; m\in\mathbf{N} \tag{3.3.2.4}
$$

*and for $c\in\Omega(F_v^{\times})(\chi_{-r})$:*

$$
c_{-r,m}(z)=z^{-r}\lvert z\rvert_v^{-m},\; m\in\mathbf{N}. \tag{3.3.2.5}
$$

(2) *The residues of $Z_v(\cdot,c)$ are:*

(1) *If $v$ is real:*

$$
\operatorname{Res}_{c=c_{a,m}}Z_v(\cdot,c)=A_{v,a,m}D^{a+m}\delta_0,\; a\in\{0,1\},\; m\in 2\mathbf{N} \tag{3.3.2.6}
$$

*where $D:\mathcal{S}(F_v)\to\mathcal{S}(F_v)$ is the differential operator $\frac{1}{2\pi i}\partial_x$ on $\mathcal{S}(\mathbf{R})$, where $A_{v,a,m}\in\mathbf{C}^{\times}$ is a constant depending only on the quasi-character, given by the following formula:*

$$
A_{v,0,m}=\frac{2^{m+1}\pi^{m}(-1)^{m/2}}{m!},\; A_{v,1,m}=-i\frac{2^{m+2}\pi^{m+1}(-1)^{m/2}}{(m+1)!}. \tag{3.3.2.7}
$$

(2) *If $v$ is complex, for $r\ge 0$, and:*

$$
\operatorname{Res}_{c=c_{r,m}}Z_v(\cdot,c)=A_{v,r,m}\overline{D}^{\,r+m}D^{m}\delta_0 \tag{3.3.2.8}
$$

*and:*

$$
\operatorname{Res}_{c=c_{-r,m}}Z_v(\cdot,c)=A_{v,r,m}D^{r+m}\overline{D}^{\,m}\delta_0 \tag{3.3.2.9}
$$

## PDF page 139

**3.3. S-LOCAL IDELIC ZETA FUNCTIONS** · **139**

*for the differential operators $D:=\frac{1}{2\pi i}\partial_z$ and $\overline{D}:=\frac{1}{2\pi i}\partial_{\bar{z}}$ on $\mathcal{S}(\mathbf{C})$ for $v$ complex, where $A\in\mathbf{C}^{\times}$ is a constant depending only on the quasi-character, given by the following formula:*

$$
A_{v,r,m}=(-i)^{\lvert r\rvert}(2\pi)^{1+\lvert r\rvert+2m}\frac{(-1)^m}{\Gamma(1+\lvert r\rvert+m)m!}. \tag{3.3.2.10}
$$

PROOF. For any place $v$ of $F$ and $c\in\Omega(F_v^{\times})$, we have, for every $f\in\mathcal{S}(F_v)$:

$$
Z_v(f,c)=\rho_v(c)Z_v(\widehat{f},\widehat{c}) \tag{3.3.2.11}
$$

by [CF, Ch.XV,Thm.2.4.1]. The function $Z_v(\widehat{f},\widehat{c})$ is holomorphic over $\Omega(F_v^{\times})_{<1}$ and $Z_v(f,c)$ is holomorphic over $\Omega(F_v^{\times})_{>0}$. The functional equation in (3.3.2.11) implies that $Z_v(f,c)$ extends to a meromorphic function over the entire $\Omega(F_v^{\times})$, with poles located at the poles of $\rho_v(c)$, of order bounded above by the orders of pole of $\rho_v(c)$, respectively.

Since (3.3.2.11) holds for all $f\in\mathcal{S}(F_v)$ and both sides of the identity are meromorphic functions valued in tempered distributions on $F_v$, the poles of $Z_v$ as a meromorphic vector-valued function are exactly the poles of $\rho_v$ as a meromorphic complex-valued function. This means that even though there exist Schwartz-Bruhat functions on $F_v$ such that $Z_v(f,c_v)$ has fewer poles that $\rho_v$, the poles of $Z_v$ as an operator-valued meromorphic function (i.e. valued in continuous functionals on $\mathcal{S}(F_v)$) are exactly those of $\rho_v$ because of Lemma C.5.3.3, which computes its residues as functionals on $\mathcal{S}(F_v)$ (concretely, for $Z_v$ to have a pole at $c$ it is enough that for some $f\in\mathcal{S}(F_v)$, the classical meromorphic function $Z_v(f,\cdot)$ has a pole at $c$. This existence assertion is proved in Tate's thesis: the “Gaussian” functions constructed in [CF, Ch.XV,§2.5,p.316] are examples).

(1) : If $v$ is Archimedean, we distinguish the two cases when $v$ is real, and $v$ is complex.

For $v$ real, $\Omega(F_v^{\times})$ has two connected components, $\Omega(F_v^{\times})(1)$ and $\Omega(F_v^{\times})(\mathrm{sgn})$.

In the former case, $\rho_v(c)$ is computed in [CF, Ch.XV,§2.5], and it is, upon writing $c=\lvert\cdot\rvert_v^s$ for a unique complex number $s\in\mathbf{C}$:

$$
\rho_v(c)=\frac{\pi^{-\frac{s}{2}}\Gamma\left(\frac{s}{2}\right)}{\pi^{-\frac{1-s}{2}}\Gamma\left(\frac{1-s}{2}\right)}=2^{1-s}\pi^{-s}\cos\left(\frac{\pi s}{2}\right)\Gamma(s). \tag{3.3.2.12}
$$

The $\Gamma$-function has simple poles at $s=-\mathbf{N}$, and the cosine function $\cos\left(\frac{\pi s}{2}\right)$ has simple zeros at the odd integers. The odd negative integers are therefore removable singularities of $\rho_v(\lvert\cdot\rvert_v^s)$, whose only poles are simple and located at $c=\lvert\cdot\rvert_v^{-m}$ for $m\in 2\mathbf{N}$.

For $c\in\Omega(F_v^{\times})(\mathrm{sgn})$, we have $c=\mathrm{sgn}\cdot\lvert\cdot\rvert_v^s$ for a unique complex number $s\in\mathbf{C}$:

$$
\rho_v(c)=i\frac{\pi^{-\frac{s+1}{2}}\Gamma\left(\frac{s+1}{2}\right)}{\pi^{-\frac{(1-s)+1}{2}}\Gamma\left(\frac{(1-s)+1}{2}\right)}=-i\,2^{1-s}\pi^{-s}\sin\left(\frac{\pi s}{2}\right)\Gamma(s). \tag{3.3.2.13}
$$

The $\Gamma$-function has simple poles at $-\mathbf{N}$, and the sine function $\sin\left(\frac{\pi s}{2}\right)$ has simple zeros at the even integers, and so the function $\rho_v(c)$ restricted to $\Omega(F_v^{\times})(\mathrm{sgn})$ has simple poles located exactly at the quasi-characters $c=\mathrm{sgn}\lvert\cdot\rvert_v^{-m-1}$, which, evaluated on $x\in\mathbf{R}\simeq F_v$, reads $c(x)=x^{-1}\lvert x\rvert_v^{-m}$, for $m\in 2\mathbf{N}$.

If $v$ is complex, then $\Omega(F_v^{\times})$ is fibred over the discrete dual group of $\mathrm{U}(1)$, which is isomorphic to $\mathbf{Z}$ upon choosing the standard unitary character $\chi_1:F_v^{\times}\to\mathrm{U}(1)$ defined as $\chi_1(z)=\chi_1(Re^{i\theta}):=e^{i\theta}$.

We fix $r\in\mathbf{Z}$. Note that we have $\chi_r=(\chi_1)^r$. For $c\in\Omega(F_v^{\times})(\chi_r)$, we have:

$$
\rho_v(c)=(-i)^{\lvert r\rvert}\frac{(2\pi)^{1-s}\Gamma\left(s+\frac{\lvert r\rvert}{2}\right)}{(2\pi)^s\Gamma\left((1-s)+\frac{\lvert r\rvert}{2}\right)}. \tag{3.3.2.14}
$$

For $r\ge 0$, the function $\Gamma(s+r/2)$ has simple poles located at the points $-r/2-\mathbf{N}$, and the function $1/\Gamma((1-s)+r/2)$ is entire, with simple zeros located at the points $1+r/2+\mathbf{N}$. The intersection of these two sets comprises of points $s\in\mathbf{C}$ of the form $-r/2-m=1+r/2-m'$ for some integer $m'\in\mathbf{N}$, and it is empty.

## PDF page 140

**140** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

The poles of $\rho_v(c)$ are therefore simple and located at the quasi-characters $c=\chi_r\lvert\cdot\rvert_v^{-r/2-m}$ for $m\in\mathbf{N}$, which evaluated on $z\in\mathbf{C}\simeq F_v$ read $c(z)=\bar{z}^{-r}\lvert z\rvert_v^{-m}$.

For $r\le 0$, the function $\Gamma(s-r/2)$ has simple poles located at the points $r/2-\mathbf{N}$, and the function $1/\Gamma((1-s)-r/2)$ is entire, with simple zeros located at the points $1-r/2+\mathbf{N}$. The intersection of these two sets is empty, and so the poles of $\rho_v(c)$ are located at the quasi-characters $c=\chi_r\lvert\cdot\rvert_v^{r/2-m}$ for $m\in\mathbf{N}$, which, evaluated at $z\in\mathbf{C}\simeq F_v$, read $c(z)=z^{r}\lvert z\rvert_v^{-m}$.

(2) : For $v$ real, the residue of $\rho_v(c)$ at $c_{0,m}$ for $m\in 2\mathbf{N}$ is:

$$
\frac{2^{m+1}\pi^{m}(-1)^{m/2}}{m!} \tag{3.3.2.15}
$$

and at $c_{1,m}$ for $m\in 2\mathbf{N}$, it is:

$$
-i\frac{2^{m+2}\pi^{m+1}(-1)^{m/2}}{(m+1)!}. \tag{3.3.2.16}
$$

For $v$ complex, the residue of $\rho_v(c)$ at $c_{r,m}$ for $r\in\mathbf{Z}$, $m\in\mathbf{N}$, is:

$$
(-i)^{\lvert r\rvert}(2\pi)^{1+\lvert r\rvert+2m}\frac{(-1)^m}{\Gamma(1+\lvert r\rvert+m)m!}. \tag{3.3.2.17}
$$

For any $v$ Archimedean the residue satisfies:

$$
\operatorname{Res}_{c}Z_v(f,c')=\operatorname{Res}_{c}\rho_v(c')Z_v(\widehat{f},\widehat{c}) \tag{3.3.2.18}
$$

as continuous linear operators on $\mathcal{S}(F_v)$.

We compute $Z_v(\widehat{f},\widehat{c})$ in terms of the differential operators $D^k$ for $v$ real and $k\in\mathbf{N}$, and $D^a\overline{D}^{\,b}$ for $v$ complex and $a,b\in\mathbf{N}$, when $c$ is a pole of $Z_v$.

If $v$ is real and $c=c_{0,m}$ for $m\in 2\mathbf{N}$, we have

$$
Z_v(\widehat{f},\widehat{c_{0,m}})=\int_{F_v^{\times}}\widehat{f}(g)\lvert g\rvert_v^{1+m}\,\mathrm{d}\mu_v(g)
$$

and upon choosing an isomorphism of topological fields $F_v\simeq\mathbf{R}$, we have:

$$
\int_{F_v^{\times}}\widehat{f}(g)\lvert g\rvert_v^{1+m}\,\mathrm{d}\mu_v(g)=\int_{\mathbf{R}}\widehat{f}(x)\lvert x\rvert^{m}\,\mathrm{d}x=\frac{1}{(2\pi i)^m}\int_{\mathbf{R}}(2\pi ix)^m\widehat{f}(x)\,\mathrm{d}x=\frac{1}{(2\pi i)^m}(\partial_x^mf)(0)=(D^m\delta_0)(f) \tag{3.3.2.19}
$$

where we used [Fol, Thm.8.22,(e)] and [Fol, Thm.8.26].

If $c=c_{1,m}$ for $m\in 2\mathbf{N}$, we have

$$
Z_v(\widehat{f},\widehat{c_{1,m}})=\int_{F_v^{\times}}\widehat{f}(g)c_{1,m}(g)\,\mathrm{d}\mu_v(g)
$$

and upon choosing an isomorphism of topological fields $F_v\simeq\mathbf{R}$, we have:

$$
\int_{F_v^{\times}}\widehat{f}(g)\widehat{c_{1,m}}(g)\,\mathrm{d}\mu_v(g)=\int_{\mathbf{R}}\widehat{f}(x)x\lvert x\rvert^{m}\,\mathrm{d}x=\frac{1}{(2\pi i)^{m+1}}\int_{\mathbf{R}}(2\pi ix)^{m+1}\widehat{f}(x)\,\mathrm{d}x=\frac{1}{(2\pi i)^{m+1}}(\partial_x^{m+1}f)(0)=(D^{m+1}\delta_0)(f). \tag{3.3.2.20}
$$

We deduce that (3.3.2.6) holds.

If $v$ is complex, then we have, for $r,m\in\mathbf{Z}$, $r\ge 0$ and $m\le 0$, and for $c=c_{r,m}$:

$$
Z_v(\widehat{f},\widehat{c})=\int_{F_v^{\times}}\widehat{f}(g)\widehat{c_{r,m}}(g)\,\mathrm{d}\mu_v(g)
$$

## PDF page 141

**3.4. EIGENDISTRIBUTIONS AND WEIL'S IDENTITY** · **141**

and upon choosing an isomorphism of topological fields $F_v\simeq\mathbf{C}$, we have:
(3.3.2.21)

$$
\int_{F_v^{\times}}\widehat{f}(g)\widehat{c_{r,m}}(g)\,\mathrm{d}\mu_v(g)=\int_{\mathbf{C}}\widehat{f}(z)\bar{z}^r\lvert z\rvert_v^{1+m}\frac{\lvert\mathrm{d}z\wedge\mathrm{d}\bar{z}\rvert}{\lvert z\rvert_v}=\int_{\mathbf{C}}\widehat{f}(z)\bar{z}^{r+m}z^m\lvert\mathrm{d}z\wedge\mathrm{d}\bar{z}\rvert=\frac{1}{(2\pi i)^{2m+r}}(\partial_{\bar{z}}^{r+m}\partial_z^m\delta_0)(f)
$$

which reads $(\overline{D}^{r+m}D^m\delta_0)(f)$.

For $c=c_{-r,m}$ we have:
(3.3.2.22)

$$
\int_{F_v^{\times}}\widehat{f}(g)\widehat{c_{-r,m}}(g)\,\mathrm{d}\mu_v(g)=\int_{\mathbf{C}}\widehat{f}(z)z^r\lvert z\rvert_v^{1+m}\frac{\lvert\mathrm{d}z\wedge\mathrm{d}\bar{z}\rvert}{\lvert z\rvert_v}=\int_{\mathbf{C}}\widehat{f}(z)z^{r+m}\bar{z}^m\lvert\mathrm{d}z\wedge\mathrm{d}\bar{z}\rvert=\frac{1}{(2\pi i)^{2m+r}}(\partial_z^{r+m}\partial_{\bar{z}}^m\delta_0)(f)
$$

which reads $(D^{r+m}\overline{D}^m\delta_0)(f)$. $\square$

3.3.2.2. *Poles and residues of the local Z-functions at the non-Archimedean places.* The non-Archimedean analog of Lemma 3.3.2.1 is the following:

LEMMA 3.3.2.2 (Poles and Residues of the local Z-functions - non-Archimedean places). *Let $F$ be a number field, $v$ a non-Archimedean place. The meromorphic function $Z_v$ on $\Omega(F_v^{\times})$ valued in tempered distributions on $F_v$ has one simple pole at the trivial quasi-character $c=1$. Its residue is:*

$$
\mathrm{Res}_{c=1}\,Z_v(f,c)=N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{-\frac12}\frac{1-q_v^{-1}}{\log(q_v)}\widehat{f}(0). \tag{3.3.2.23}
$$

PROOF. Indeed, for any $f\in\mathcal{S}(F_v)$, we have:

$$
Z_v(f,c)=\rho_v(c)Z_v(\widehat{f},\widehat{c})
$$

by [CF, Ch.XV,§2.4,Thm.2.4.1,p.315] and the only poles of $Z_v(f,c)$ are located among the poles of $\rho_v(c)$, which is explicitly given by the following formula (see [CF, Ch.XV,§2.5,p.322]) upon writing $q_v=N(\mathfrak{p}_v)$ for $\mathfrak{p}_v$ the unique prime ideal of $\mathcal{O}_F$ corresponding to the finite place $v$ of $F$, and for $\mathfrak{d}_{F_v/\mathbf{Q}_p}$ the local discriminant, with $p$ the residue characteristic of $F_v$:

$$
\rho_v(\lvert\cdot\rvert_v^s)=N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{s-it_v-\frac12}\frac{1-q_v^{s-it_v-1}}{1-q_v^{-s-it_v}},\quad \rho_v(\chi\lvert\cdot\rvert_v^s)=N(\mathfrak{d}_{F_v/\mathbf{Q}_p}\mathfrak{f}_{\chi})^{s-\frac12}\rho_0(\chi) \tag{3.3.2.24}
$$

where $\mathfrak{f}_{\chi}$ is the conductor of a ramified unitary character $\chi$ of $F_v^{\times}$ and $\rho_0(\chi)$ is the root number, a complex number of absolute value 1, independent of $s\in\mathbf{C}$ modulo $2\pi i\mathbf{Z}/\log(q_v)$. The only poles of $\rho_v(c)$ therefore occur over the connected component of $\Omega(F_v^{\times})$ fibred over the trivial character of $\mathcal{O}_{F_v}^{\times}$, and within such connected component, parametrized by $\lvert\cdot\rvert_v^s$ with $s$ unique modulo $2\pi i\mathbf{Z}/\log(q_v)$, the pole occurs at the image of the origin in the complex $s$-plane into the cylinder $\mathbf{C}/(2\pi i\mathbf{Z}/\log(q_v))$. The pole is simple, because the zeros of $1-q_v^{-s-it_v}$ in the complex $s$-plane are simple, and its residue is:

$$
\mathrm{Res}_{c=1}\,Z_v(f,c)=N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{-\frac12}\frac{1-q_v^{-1}}{\log(q_v)}Z_v(\widehat{f},\lvert\cdot\rvert_v)=N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{-\frac12}\frac{1-q_v^{-1}}{\log(q_v)}\int_{F_v^{\times}}\widehat{f}(g)\lvert g\rvert_v\,\mathrm{d}\mu_v(g) \tag{3.3.2.25}
$$

and, given that $\nu_v=\lvert\cdot\rvert_v\mu_v$ as Radon measures over $F_v^{\times}$, which has $\nu_v$-measure zero complement in $F_v$, the rightmost side of (3.3.2.25) indeed is the rightmost side of (3.3.2.23). $\square$

**3.4. Eigendistributions and Weil's Identity**

In this section we discuss what we refer to, throughout this work, as *Weil's Identity*. It is a formula to compute the meromorphic function $Z(f,\chi\lvert\cdot\rvert_F^s)$ from Theorem 3.2.2.1 in terms of the finite Hecke $L$-function $L_f(s,\chi)$, for any Schwartz-Bruhat function $f$ on $\mathbf{A}_F$.

## PDF page 142

**142** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

This was observed by Weil in his paper on eigendistributions (see [Weil-a, §3]). The study of the global Idelic $Z$-functions defined in Definition 3.2.2.5 through the lens of functional analysis, was initiated by Weil in his paper [Weil-a] on adelic eigendistributions.

Therein, Weil gave a direct construction and a characterization (proving their uniqueness up to normalization, in a similar vein as for uniqueness of the Haar measure on a Hausdorff locally compact abelian group) of those adelic tempered distributions, i.e. elements of the strong dual $\mathcal{S}(\mathbf{A}_F)'_{\beta}$, satisfying a homogeneity condition with weight a continuous idelic quasi-character, under the adjoint of the continuous left-translation action of $\mathrm{GL}_1(\mathbf{A}_F)$ on $\mathcal{S}(\mathbf{A}_F)$.

They turn out to be equal to the continuous functionals:

$$
\frac{Z(\cdot,c)}{L(c)}
$$

on $\mathcal{S}(\mathbf{A}_F)$ for each $c\in\Omega(C_F)$, and they vary holomorphically with respect to the continuous quasi-character $c\in\Omega(C_F)$. They define a holomorphic family of eigendistributions, equivalently an $\mathcal{S}(\mathbf{A}_F)'_{\beta}$-valued holomorphic function on $\Omega(C_F)$: its value at each $c\in\Omega(C_F)$ is homogeneous of weight $c$ under the adjoint of the continuous left-translation action of $\mathrm{GL}_1(\mathbf{A}_F)$ on $\mathcal{S}(\mathbf{A}_F)$.

The Theory of holomorphic and meromorphic functions valued in a quasi-complete Hausdorff topological $\mathbf{C}$-vector space, is developed in §C.5. The reader is referred to §C.5 (and specifically to Theorem C.5.2.6), and the references contained therein.

Eigendistributions will be reprised throughout the next Chapter, where we will be studying the Hausdorff locally convex topological $\mathbf{C}$-vector spaces of Adelic (both global and $S$-local) $\theta$-functions, as well as the resulting Hausdorff locally convex topological $\mathbf{C}$-vector spaces of meromorphic functions on $\Omega(C_F)$ under the Mellin transform $Z$. We refer the reader to §5.5 of Chapter 4.

In this section, we record Weil's main results from [Weil-a, §1,3], and provide a few complements, for later reference.

**3.4.1. Weil's Identity: the unramified case.** We begin by recalling the following:

NOTATION 3.4.1.1. We recall that for $c\in\Omega(C_F)$, i.e. for $c$ a continuous quasi-character of $C_F$, we denote by $c_v$ the restriction of $c$ to $F_v^{\times}\subset C_F$, where $F_v^{\times}$ is embedded as a closed subgroup under the insertion into the $v$-adic "coordinate" $F_v^{\times}\to\mathrm{GL}_1(\mathbf{A}_F)$ followed by the quotient homomorphism $\mathrm{GL}_1(\mathbf{A}_F)\to C_F$. By [CF, Ch.XV,§3.2,Lemma 3.2.1,p.324] we have $\bigotimes_{v\in\Sigma_F}c_v=c$.

Recall that we say $c$ is *unitary* if it is valued in $\mathrm{U}(1)\subset\mathbf{C}^{\times}$. Any other unitary quasi-character $c'$ of $C_F$ with the same restriction to $C_F^1$, i.e. within the same connected component of $\Omega(C_F)$, is related to $c$ by the formula

$$
c'=c\lvert\cdot\rvert_F^{ix_0}
$$

for a unique real number $x_0\in\mathbf{R}$, and if $c'$ is possibly non-unitary then there exists a unique complex number $s$ such that $c'=c\lvert\cdot\rvert_F^s$.

We refer the reader to §3.1.1 for generalities on quasi-characters.

We will reserve the letter $\chi$ to denote an arbitrary continuous character of $C_F$. We denote by $S_{\chi}$ the finite set of non-Archimedean places of $F$ at which $\chi$ is ramified.

The following Theorem relates the global Idelic Zeta functions from (3.2.2.1) of Theorem 3.2.2.1 to the finite Hecke $L$-function $L_f(s,\chi)$ from Definition 3.2.1.4 up to finitely many Euler factors.

We will be generalizing it by the end of this Chapter using Weil's Eigendistributions (see Theorem 3.4.3.3). The special case discussed in Theorem 3.4.1.1 below is already of interest and does not require the reader to have familiarity with distributions. We record it here separately for later use.

## PDF page 143

**3.4. EIGENDISTRIBUTIONS AND WEIL'S IDENTITY** · **143**

THEOREM 3.4.1.1 (Weil's Identity - I). *Let $F$ be a number field. Let $f\in\mathcal{S}(\mathbf{A}_F)$ be a Schwartz-Bruhat function. Assume $f$ is of the form $f=f_{\infty}\otimes\bigotimes_{v\in\Sigma_{F,f}}f_v$, where $f_v\in\mathcal{S}(F_v)$ is of the form $f_v=1_{K_v}$ for $K_v\subset F_v$ a compact open subset, with $K_v=\mathcal{O}_{F_v}$ for all but finitely many finite places $v$.*

*Then the following product is convergent absolutely and uniformly on compact subsets of $\Omega(C_F)_{>0}$ to a holomorphic function of $c\in\Omega(C_F)_{>0}$:*

$$
\widetilde{Z}(f,c):=\widetilde{Z}_{S_{\infty}}(f_{\infty},c_{\infty})\prod_{v\in\Sigma_{F,f}}\widetilde{Z}_v(f_v,c_v) \tag{3.4.1.1}
$$

*where*

$$
\widetilde{Z}_{S_{\infty}}(f_{\infty},c_{\infty}):=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})}f_{\infty}(g_{\infty})\,c_{\infty}(g_{\infty})\,\mathrm{d}\mu_{S_{\infty}}(g_{\infty}) \tag{3.4.1.2}
$$

*where $c_{\infty}:=\bigotimes_{v\in S_{\infty}}c_v$, and for each finite place $v$ of $F$*

$$
\widetilde{Z}_v(f_v,c_v):=\int_{F_v^{\times}}(f_v(g_v)-f_v(\pi_v^{-1}g_v))\,c_v(g_v)\,\mathrm{d}\mu_v(g_v) \tag{3.4.1.3}
$$

*if $c$ is unramified at $v$, where $\pi_v$ denotes a choice of uniformizer for $F_v$ and*

$$
\widetilde{Z}_v(f_v,c_v):=\int_{F_v^{\times}}f_v(g_v)c_v(g_v)\,\mathrm{d}\mu_v(g_v)=Z_v(f_v,c_v) \tag{3.4.1.4}
$$

*if $c$ is ramified at $v$.*

*Moreover, for a fixed choice of arbitrary continuous character $\chi\in\widehat{C_F}$ and $S$ any finite set of places of $F$ containing $S_{\infty}\cup S_{\chi}$ such that $f_v=1_{\mathcal{O}_{F_v}}$ for all finite $v\notin S$, then as holomorphic functions over $\mathbf{C}_{>0}$ we have*

$$
\widetilde{Z}(f,\chi\lvert\cdot\rvert_F^s)=Z_{S_0}(f_{S_0},\chi_{S_0}\lvert\cdot\rvert_{F,S_0}^s)\prod_{v\in S-S_0}\widetilde{Z}_v(f_v,\chi_v\lvert\cdot\rvert_v^s) \tag{3.4.1.5}
$$

*where $S_0=S_{\infty}\cup S_{\chi}\subset S$, $f_{S_0}:=f_{\infty}\otimes\bigotimes_{v\in S_{\chi}}f_v$, and $\chi_{S_0}$ is the unique continuous character of $J_{F,S_0}$ obtained from $\chi$ by descent by $\widehat{\mathcal{O}}_{\Sigma_F-S_0}^{\times}$-invariance of the restriction of $\chi$ to $C_{F,S_0}$. Moreover, as holomorphic functions over $\mathbf{C}_{>0}$, we have*

$$
Z(f,\chi\lvert\cdot\rvert_F^s)=Z_{S_0}(f_{S_0},\chi_{S_0}\lvert\cdot\rvert_{F,S_0}^s)\prod_{v\in S-S_0}\widetilde{Z}_v(f_v,\chi_v\lvert\cdot\rvert_v^s)L_{\Sigma_F-S_0}(s,\chi) \tag{3.4.1.6}
$$

*where $L_{\Sigma_F-S_0}(s,\chi):=\prod_{v\in S_{\chi}}(1-\chi(\mathfrak{p}_v)N(\mathfrak{p}_v)^{-s})L_f(s,\chi)$.*

Recall that $Z_S(f,c)$ is the $S$-idelic Zeta function of the Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_{F,S})$, which we defined in Definition 5.1.1.1 and studied throughout §5.1.1.

PROOF. To see this, we observe that the first factor integral defining $\widetilde{Z}_{S_{\infty}}(f_{\infty},c_{\infty})$ from (3.4.1.2) is absolutely convergent, because, upon calling $B$ a compact neighborhood of $0\in\mathbf{A}_{F,S_{\infty}}\simeq\prod_{v\in S_{\infty}}F_v$ of the form $\prod_{v\in S_{\infty}}Z_v$, for $B_v\subset F_v$ a compact neighborhood of zero in $F_v$, then the integral over $B\cap\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ of $f_{\infty}c_{\infty}\prod_{v\in S_{\infty}}\lvert\cdot\rvert_v^{-1}$ with respect to the Lebesgue measure on the Euclidean space $\mathbf{A}_{F,S_{\infty}}$ is absolutely convergent so long as $\sigma(c_v)>0$ for every Archimedean place $v$ of $F$, since such convergence is ensured by the convergence of $\int_{B_v}\lvert\cdot\rvert_v^{\sigma(c_v)-1}\,\mathrm{d}x_v$ for $\sigma(c_v)>0$ and by boundedness over $B$ of $f_{\infty}$. Since $\sigma(c)>0$, then $\sigma(c_v)>0$ for every Archimedean place $v$ of $F$, and so the desired convergence holds, locally uniformly with respect to $c_v$ for each such $v$.

The Schwartz condition on $f_{\infty}$ then implies the absolute convergence of the integral over the complement of $B$ in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$. Both convergent integrals converge locally uniformly over $\Omega(C_F)_{>0}$ as functions of $c$ through $c_{\infty}=\bigotimes_{v\in S_{\infty}}c_v$.

## PDF page 144

**144** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

We note that in the special case $c$ is unramified outside $S_{\infty}$, then $c_{\infty}$ is trivial on the global units, and we have $\widetilde{Z}_{S_{\infty}}(f_{\infty},c_{\infty})=Z_{S_{\infty}}(f_{\infty},c_{\infty})$, the $S_{\infty}$-idelic $Z$-function of $f_{\infty}$ over the connected component of $c_{\infty}$ in $\Omega(J_{F,S_{\infty}})$.

We call $S_f'$ the finite set of finite places of $F$ such that $f_v\ne 1_{\mathcal{O}_v}$. We fix $c\in\Omega(C_F)$, and we compute, for every finite place $v\notin(S_f\cup S_c)$, where $S_c$ is the finite set of non-Archimedean places at which $c$ is ramified:

$$
\int_{F_v^{\times}}(f_v(g_v)-f_v(\pi_v^{-1}g_v))c_v(g_v)\,\mathrm{d}\mu_v(g_v)=\int_{F_v^{\times}}(1_{\mathcal{O}_v}-1_{\pi_v\mathcal{O}_v})(g_v)c_v(g_v)\,\mathrm{d}\mu_v(g_v)
$$

$$
=\int_{F_v^{\times}}1_{\mathcal{O}_v^{\times}}(g_v)c_v(g_v)\,\mathrm{d}\mu_v(g_v)
$$

$$
=\int_{\mathcal{O}_v^{\times}}\mathrm{d}\mu_v(g_v)=N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{-1/2}.
$$

We refer the reader to Definition A.3.2.2 for the normalization defining the local multiplicative Tamagawa measures on the local fields $F_v^{\times}$. Note that in particular $\mu_v(\mathcal{O}_{F_v}^{\times})=1$ for all but finitely many finite places $v$ of $F$.

For every $v\in S_f'$ at which $c$ is unramified, we have

$$
\int_{F_v^{\times}}(f_v(g_v)-f_v(\pi_v^{-1}g_v))\,c_v(g_v)\,\mathrm{d}\mu_v(g_v)=\int_{F_v^{\times}}f_v(g_v)\,c_v(g_v)\,\mathrm{d}\mu_v(g_v)-\int_{F_v^{\times}}f_v(\pi_v^{-1}g_v)\,c_v(g_v)\,\mathrm{d}\mu_v(g_v)
$$

$$
=\int_{F_v^{\times}}f_v(g_v)\,c_v(g_v)\,\mathrm{d}\mu_v(g_v)-\int_{F_v^{\times}}f_v(g_v)\,c_v(\pi_v)\,c_v(g_v)\,\mathrm{d}\mu_v(g_v)
$$

$$
=(1-c_v(\pi_v))\int_{F_v^{\times}}f_v(g_v)\,c_v(g_v)\,\mathrm{d}\mu_v(g_v)
$$

$$
=(1-c_v(\pi_v))\,Z(f_v,c_v)
$$

where the integral $\int_{F_v^{\times}}f_v(g_v)\,c_v(g_v)\,\mathrm{d}\mu_v(g_v)$ converges, for each $v\in S_f'$ at which $c$ is unramified, absolutely and uniformly over $\Omega(F_v^{\times})_{>0}$, where $\Omega(F_v^{\times})$ is the Riemann surface of the continuous quasi-characters of the non-Archimedean local field $F_v$, and $\Omega(F_v^{\times})_{>0}\subset\Omega(F_v^{\times})$ is the open subset of those quasi-characters of exponent $\sigma(c_v)>0$.

It follows that the product defining $\widetilde{Z}(f,c)$ in (3.4.1.1) is finite and its factors are holomorphic over $\Omega(C_F)_{>0}$, since each is either $\widetilde{Z}_{S_{\infty}}(f_{\infty},c_{\infty})$ (which is holomorphic as a function of $c\in\Omega(C_F)_{>0}$ since it factors through the monomial function $\otimes_{v\in S_{\infty}}c_v$ of $c\in\Omega(C_F)_{>0}$) or of the form $Z(f_v,c_v)$ or $(1-c_v(\pi_v))Z(f_v,c_v)$ for finite $v$ (both holomorphic over $\Omega(F_v^{\times})_{>0}$ by [CF, Ch.XV,Lemma 2.4.1]). As a function of $c$, $\widetilde{Z}(f,c)$ is therefore holomorphic over $\Omega(C_F)_{>0}$ because it is a finite product of functions that are each holomorphic over $\Omega(C_F)_{>0}$ by Lemma 3.1.2.1.

We now observe that, for $c=\chi\lvert\cdot\rvert_F^s$ with $\chi$ a continuous character of $C_F$, upon parametrizing $\Omega(C_F)(\chi|_{C_F^1})_{>1}$ by means of the global holomorphic chart

$$
c=\chi\lvert\cdot\rvert_F^s \tag{3.4.1.7}
$$

with $\mathrm{Re}(s)>1$, then we have that the identities of holomorphic functions in (3.4.1.5) and (3.4.1.6) hold over $\Omega(C_F)(\chi|_{C_F^1})_{>1}$.$^{3}$

Since $\widetilde{Z}(f,\chi\lvert\cdot\rvert_F^s)$ is holomorphic over $\Omega(C_F)(\chi|_{C_F^1})_{>0}$, and since both $L_f(s,\chi)$, and hence also $L_{\Sigma_F-S_0}(s,\chi)$, and $Z(f,\chi\lvert\cdot\rvert_F^s)$ extend to meromorphic functions over $\Omega(C_F)(\chi|_{C_F^1})_{>0}$, where $L_f(s,\chi)$ is regarded as a meromorphic function on $\Omega(C_F)(\chi|_{C_F^1})_{>0}$ by means of the parametrization of $\Omega(C_F)(\chi|_{C_F^1})_{>0}$ from (3.4.1.7) with $\mathrm{Re}(s)>0$, the identities in (3.4.1.5) and (3.4.1.6) hold over $\Omega(C_F)(\chi|_{C_F^1})_{>0}$ by the Identity Theorem. $\square$

**3.4.2. Applications of the unramified case of Weil's Identity.**

---

$^{3}$Why do such identities hold? Must say more about how this follows.

## PDF page 145

**3.4. EIGENDISTRIBUTIONS AND WEIL’S IDENTITY** · **145**

3.4.2.1. *Convergence on the relative 1-line.* We record here below an application of Weil’s Identity from Theorem 3.4.1.1: an observation that, while not used throughout this work, we find opportune to mention here. It concerns the validity of the identity in (3.2.2.1) from Theorem 3.2.2.1, which is taken as the definition of $Z(f, c)$ over $\Omega(C_F)_{>1}$, over the relative 1-line, i.e. the discretely-parametrized family of vertical lines:

$$
\{\sigma(c) = 1, c \in \Omega(C_F)\} \subset \Omega(C_F)
$$

over the discrete parameter space $\widehat{C^1_F}$.

Proposition 3.4.2.1 (Convergence on the relative 1-line). *Let $F$ be a number field. For any real number $A > 0$, we define the subset:*

$$
L_A := \{\sigma(c) = 1, c \in \Omega(C_F), c|_{C^1_F} \ne 1\} \cup \{|\cdot|^{1+ix}_F, x \in \mathbf{R} - (-A, A)\} \subset \Omega(C_F).
$$

*For any Schwartz-Bruhat function $f \in \mathcal{S}(\mathbf{A}_F)$, as a function of $c \in L_A$ the Lebesgue integral*

$$
\int_{\mathrm{GL}_1(\mathbf{A}_F)} f(g)c(g)\,\mathrm{d}\mu(g) \tag{3.4.2.1}
$$

*is finite and varies continuously in such $c$. As a function of $c$, it equals the restriction of $Z(f, c)$ to $L_A$.*

Proof. The complex measure $c\mu$ on $\mathrm{GL}_1(\mathbf{A}_F)$ is Radon, and formation of the integral in (3.4.2.1) is $\mathbf{C}$-linear with respect to $f \in \mathcal{S}(\mathbf{A}_F)$. By Proposition 2.1.3.2(3), it is therefore sufficient to prove the assertions of the Proposition in the special case $f$ is of the form $f = f_\infty \otimes \bigotimes_{v \in \Sigma_{F,f}} f_v$, with $f_\infty \in \mathcal{S}(\mathbf{A}_{F,S_\infty})$ and $f_v \in \mathcal{S}(F_v)$ for every finite place $v$ of $F$, and with $f_v = 1_{\mathcal{O}_{F_v}}$ for all but finitely many finite places of $F$.

By [RV, Ch.5, §5.1, Prop.5.6(i), p.186], the integral from (3.4.2.1) equals the possibly divergent product:

$$
\int_{\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})} f_\infty(g_\infty)c_\infty(g_\infty)\,\mathrm{d}\mu_\infty(g_\infty) \prod_{v \in \Sigma_{F,f}} \int_{F_v^\times} f_v(g_v)c_v(g_v)\,\mathrm{d}\mu_v(g_v). \tag{3.4.2.2}
$$

We prove that product in (3.4.2.2) converges, for any $A > 0$, pointwise over $L_A$ and uniformly over its compact subsets. If so, then its limit function is therefore continuous over $L_A$, and hence the same holds for the integral from (3.4.2.1).

The convergence assertions on the product in (3.4.2.2) can be checked on each connected component of $\Omega(C_F)$, respectively. We let $\omega \in \widehat{C^1_F}$ be arbitrary, and choose a base point $\chi \in \widehat{C_F}$ for the connected component parametrized by $\omega = \chi|_{C^1_F} \in \widehat{C^1_F}$. We parametrize $\Omega(C_F)(\omega)$ holomorphically as $\{\chi|\cdot|^s_F, s \in \mathbf{C}\}$.

Let $S_\chi$ be the finite set of finite places of $F$ at which $\chi$ is ramified, and let $S_0$ be the finite set of finite places of $F$ such that $f_v \ne 1_{\mathcal{O}_{F_v}}$.

We call $S := S_\infty \cup S_0 \cup S_\chi$. By Weil’s Identity (see (3.4.1.6) from Theorem 3.4.1.1), it is enough to show that the countable net of meromorphic functions over the complex $s$-plane, defined by the partial Euler products:

$$
S' \mapsto \prod_{v \in S'} L_v(\chi_v|\cdot|^s_v)
$$

for the Hecke $L$-function $L(s, \chi)$, as $S'$ varies over all finite sets of finite places of $F$ such that $S' \cap S = \varnothing$, converges pointwise to $L_f(s, \chi) \prod_{v \in S_0} L_v(\chi_v|\cdot|^s_v)^{-1}$ over $1+i\mathbf{R}$ if $\chi|_{C^1_F} \ne 1$ (uniformly on its compact subsets), and $1 + i(\mathbf{R} - (-A - x_0, A - x_0))$ if $\chi = |\cdot|^{ix_0}_F$ (uniformly on its compact subsets).

This is indeed the case by Corollary B.7.2.5 (a consequence of Perron’s Formula; see also [T2, Ch.III, §3.15, p.66] for the special case $F = \mathbf{Q}$ and $\chi = 1$). $\square$

3.4.2.2. *Estimates on adelic $\theta$-functions, uniformly on Schwartz-Bruhat-bounded subsets.* We record here the following result as another application of Theorem 3.4.1.1, presenting a different method to establish some

## PDF page 146

**146** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

of the estimates from Theorem 2.2.5.4 on the decay properties of the functions $\Phi_F(f)(g)$ over $C_F$ as $|g|_F \to 0^+$ and as $|g|_F \to +\infty$, for $f$ a Schwartz-Bruhat function on $\mathbf{A}_F$.

The Theorem below was already established in Theorem 2.2.5.4. The proof we provide has one important advantage though. It gives a concrete interpretation to the constants $C_N$ that appear in the estimates stated in Theorem 2.2.5.4, revealing why they can be maximized over bounded subsets in $\mathcal{S}(\mathbf{A}_F)$. The existence of maxima comes down to $\mathcal{S}(\mathbf{A}_F)$ satisfying the Heine-Borel property. Already through the proof of the existence of uniform versions of the constants $C_N$ from Theorem 2.2.5.4 (uniform as $f$ varies over a fixed bounded subset $\mathcal{B} \subset \mathcal{S}(\mathbf{A}_F)$) the Heine-Borel property was used to the same effect: maximizing certain auxiliary continuous functions (seminorms) arising in the process of building the uniform constants $C_{\mathcal{B},N}$ from parts (5) and (6) of Theorem 2.2.5.4.

The idelic Mellin transform in the proof below reveals the nature of those constants, and why they can be rendered uniform on bounded subsets of $\mathcal{S}(\mathbf{A}_F)$.

Theorem 3.4.2.2 (Estimates over the Idele classes - III). *Let $F$ be a number field, $f \in \mathcal{S}(\mathbf{A}_F)$ a Schwartz-Bruhat function. Let $\omega \in \widehat{C^1_F}$ be a fixed continuous character. The continuous function $\Phi_{F,\omega}(f)$ on $C_F$ satisfies the following conditions:*

(1) *For every integer $N \ge 0$, there exists a real number $C_N > 0$ depending on $N$ and $f$, such that for every $g \in C_F$, we have*

$$
|\Phi_{F,\omega}(f)(g)| \le C_N|g|^{-N}_F \tag{3.4.2.3}
$$

as $g \in C_F$ is such that $|g|_F \to +\infty$.

(2) *For every integer $N \ge 0$, there exists a real number $C_N > 0$ depending on $N$ and $f$, such that for every $g \in C_F$, we have*

$$
|\Phi_{F,\omega}(f)(g) - (|g|^{-1}_F \widehat{f}(0) - f(0)) \delta_\omega(g)| \le C_N |g|^N_F \tag{3.4.2.4}
$$

as $g \in C_F$ is such that $|g|_F \to 0^+$, where

$$
\delta_\omega : C_F \to \mathbf{C} \tag{3.4.2.5}
$$

*is the bounded function on $C_F$ defined as:*

$$
\delta_\omega(g) := 1_{\{x \in C_F : |x|_F \le 1\}}(g), \quad g \in C_F \tag{3.4.2.6}
$$

if $\omega = 1$, and identically zero otherwise.

*Moreover, the constants $C_N$ from (3.4.2.3) and (3.4.2.4) can be made to be uniform with respect to $f$ varying over a fixed arbitrary bounded subset $\mathcal{B} \subset \mathcal{S}(\mathbf{A}_F)$.*

Remark 3.4.2.3 (On the nature of the uniform constants $C_{\mathcal{B},N}$ from Theorem 2.2.5.4). The main points of the argument that follows, are two. Let $f \in \mathcal{S}(\mathbf{A}_F)$ be of the form $\pi_S(f_S)$ for some $f_S \in \mathcal{S}(\mathbf{A}_{F,S})$. Recall that $\pi_S : \mathcal{S}(\mathbf{A}_{F,S}) \to \mathcal{S}(\mathbf{A}_F)$ is the transition operator from (2.1.4.5) defined by sending $f_S$ to $f_S \otimes 1_K$ with $K = \prod_{v \notin S} \mathcal{O}_{F_v}$.

• Use Weil’s Identity in the unramified case (i.e. (3.4.1.6) from Theorem 3.4.1.1) to deduce properties of $Z(f, \chi|\cdot|^s_F)$ from properties of $Z_S(f_S, \chi_S|\cdot|^s_{F,S})$ combined with well known properties of the finite Hecke $L$-function itself $L_f(s, \chi)$ (these are shown in Appendix B). We know much about the growth properties of $L_f(s, \chi)$ uniformly on vertical strips of bounded width of the complex $s$-plane, and $\pi_S$ is turned into multiplication by $L_f(s, \chi)$ with finitely many Euler factors “removed” (all the Archimedean Euler factors, and all the $S$-indexed non-Archimedean Euler factors too). We refer the reader to §B.1 and specifically to Proposition B.1.1.3.

• Exhibit the constants appearing in the estimates from Theorem 2.2.3.4 (see (2.2.3.4) and (2.2.3.5)) as $L^1$-norms of $Z(f, c)$ on certain vertical lines over $\Omega(C_F)$ of prescribed abscissa (dependent on $N$).

## PDF page 147

**3.4. EIGENDISTRIBUTIONS AND WEIL’S IDENTITY** · **147**

The second point illustrates to the reader why one can indeed successfully make those constants uniform on bounded subsets of $\mathcal{S}(\mathbf{A}_F)$. This, we already did in Theorem 2.2.5.4 obtaining the constant $C_{\mathcal{B},N}$, through direct arguments via geometry of numbers.

Therein, we used the following important fact about $\mathcal{S}(\mathbf{A}_F)$: it satisfies the Heine-Borel property, i.e. closed bounded subsets are compact. It is a Montel space by Lemma 2.1.3.2, and hence it satisfies this property, just as the Schwartz space of any Euclidean space (in the special case of Euclidean spaces, this is a consequence of Ascoli-Arzelà). We used the Heine-Borel property to maximize certain continuous functions on bounded subsets in $\mathcal{S}(\mathbf{A}_F)$ on our way to build the uniform constants $C_{\mathcal{B},N}$. Upon exhibiting such constants $C_N$ in the statement of Theorem 2.2.5.4 as $L^1$-norms of $Z(f, c)$ on vertical lines of $\Omega(C_F)_{>1}$, then the fact that one can render them uniform on bounded subsets is not only reproved, but explained: such $L^1$-norms induce continuous seminorms on $\mathcal{S}(\mathbf{A}_F)$ and by the Heine-Borel property they attain maxima on bounded subsets.

We write, for $c \in \Omega(C_F)$ unramified outside a finite set $S$ of places of $F$ containing all the Archimedean places, $c_S$ the unique quasi-character of $J_{F,S}$ obtained from $c$ by restricting it to $C_{F,S}$ and descending it by $\widehat{\mathcal{O}}^\times_{\Sigma_F-S}$-invariance (where $\widehat{\mathcal{O}}^\times_{\Sigma_F-S} = \prod_{v \notin S} \mathcal{O}^\times_{F_v}$).

Proof of Theorem 3.4.2.2. By Theorem 3.2.2.1, $Z(f, c)$ has at most two poles, at the quasi-characters $c = 1$ and $c = |\cdot|_F$. Both of them are located in the connected component of $\Omega(C_F)$ parametrized by $\omega = 1 \in \widehat{C^1_F}$, i.e. in the fibre of $\pi$ from (3.1.1.1) over $\{1\}$ in $\widehat{C^1_F}$.

We now restrict $Z(f, c)$ to $\Omega(C_F)(1)$, the connected component of the trivial character, and obtain by Theorem 3.2.2.1(3), upon parametrizing $\Omega(C_F)(1)$ by $s \mapsto |\cdot|^s_F$ and choosing a continuous homomorphic section $\tau$ to the idelic norm $|\cdot|_F$:

$$
Z(f, |\cdot|^s_F) = \int_{\mathbf{R}_{>0}} \Phi_{F,\omega=1}(f)(\tau(t)) t^s \,\frac{\mathrm{d}t}{t} = M(\Phi_{F,\omega=1}(f)\circ\tau)(s)
$$

adhering to the notation $M(\phi)(s) := \int_{\mathbf{R}_{>0}} \phi(t) t^s \,\frac{\mathrm{d}t}{t}$ for the Mellin transform (see (B.2.1.2)).

By Theorem 3.2.2.1(3), we know that, for $\phi := \Phi_{F,\omega=1}(f)\circ\tau$, $M(\phi)(s)$ converges absolutely and uniformly on the compact subsets of $\mathbf{C}_{>1}$.

By Theorem 3.2.2.1(1), the Mellin transform $M(\phi)(s)$ extends to a meromorphic function over the entire complex $s$-plane, with simple poles at most at $s = 0, 1$, whose residues are $-\overline{\mu}_1(C_F)f(0)$ and $\overline{\mu}_1(C_F)\widehat{f}(0)$, respectively.

We now use Weil’s Identity. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. We fix $f \in \mathcal{S}(\mathbf{A}_F)$ of the form $f = f_\infty \otimes \bigotimes_{v \in \Sigma_{F,f}} f_v$ with $f_v = 1_{K_v}$ for $K_v \subset F_v$ a compact open subset for every finite place $v$, and $K_v = \mathcal{O}_{F_v}$ for every $v \notin S$. This we can arrange once such $f$ is chosen, up to enlarging $S$.

We denote by $f_S$ the Schwartz-Bruhat function in $\mathcal{S}(\mathbf{A}_{F,S})$ defined as $f_S := f_\infty \otimes \bigotimes_{v \in S_f} 1_{K_v}$. For simplicity, we choose $S$ containing $S_\infty$ and minimal with respect to the above property (i.e. that $K_v \ne \mathcal{O}_{F_v}$ should occur for $v \in S$).

As a consequence of (3.4.1.6) from Theorem 3.4.1.1 (applied to a large enough finite set of places $S$ of $F$ containing all the Archimedean places), we have, as meromorphic functions on the complex $s$-plane, away from the zeros of $\prod_{v \in S_f} (1 - q_v^{-s})$ and the poles of $\zeta_F(s)$ and $\widetilde{Z}_v(1_{K_v}, |\cdot|^s_v)$ (if any):

$$
Z(f, |\cdot|^s_F) = Z_S(f_S, |\cdot|^s_{F,S}) \prod_{v \in S_f} (1 - q_v^{-s}) \zeta_F(s) \prod_{v \in S_f} \widetilde{Z}_v(1_{K_v}, |\cdot|^s_v) \tag{3.4.2.7}
$$

where $\zeta_F(s)$ is the Dedekind zeta function of $F$, $q_v := N(\mathfrak{p}_v)$ and $\mathfrak{p}_v$ the prime ideal of $\mathcal{O}_F$ corresponding to the finite place $v$, and $\widetilde{Z}_v$ was defined in (3.4.1.3). It is the meromorphic function $\frac{Z_v(1_{K_v}, |\cdot|^s_v)}{1-q_v^{-s}}$ (which turns out to be entire).

## PDF page 148

**148** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

The idea now is to show that, in light of the identity from (3.4.2.7), $Z(f, |\cdot|^s_F)$ satisfies the assumptions of the Asymptotic Residue Theorem (see Theorem B.3.2.1). This will lead, through Mellin Inversion, to all the estimates stated in the Theorem, and to new information on the constants $C_N$.

We now apply the Asymptotic Residue Theorem (see Theorem B.3.2.1) to the meromorphic function

$$
Z(f, |\cdot|^s_F)t^{-s} = M(\Phi_{F,\omega=1}(f)\circ\tau)(s)t^{-s}
$$

of $s \in \mathbf{C} - \{0, 1\}$.

In order to apply the Asymptotic Residue Theorem over a vertical strip of bounded width $\mathbf{C}_I$, for $I \subset \mathbf{R}$ a connected open non-empty interval, it is sufficient to show the following (compare with the statement of Theorem B.3.2.1). We must show that $Z(f, |\cdot|^s_F)$ can be written as a product

$$
\Phi(s)u(s)
$$

over a slightly larger open vertical strip $\mathbf{C}_J$ of bounded width containing $\mathbf{C}_I$, with $\Phi$ holomorphic over $\mathbf{C}_J$ and $u$ meromorphic on $\mathbf{C}_J$ with slow growth near its poles (for this concept, the reader is referred to Definition B.3.1.1). The function $\Phi$ must further satisfy the assumption that $\Phi$ is Schwartz uniformly on any open vertical strip of bounded width contained within $\mathbf{C}_J$.

Indeed, $\prod_{v \in S_f} (1 - q_v^{-s})$ is bounded uniformly on vertical strips of bounded width, together with all of its derivatives, and its zeros resolve the singularities of $Z_S(f_S, |\cdot|^s_{F,S})$ located on the imaginary line of the complex $s$-plane, with the sole possible exception of a single point, i.e. $s = 0$. The meromorphic function $\zeta_F(s)$ grows polynomially uniformly over the vertical strips of bounded width of the complex $s$-plane (see Proposition B.1.1.3), and it has simple poles at $s = 0$ and $s = 1$. The functions $\widetilde{Z}_v(1_{K_v}, |\cdot|^s_v)$ are, for each $v \in S_f$, entire (by (3.4.1.3) combined with the local functional equation, see [CF, Ch.XV, Thm.2.4.1] and [CF, Ch.XV, §2.5]) and bounded uniformly on vertical strips (by vertical periodicity) together with all of their derivatives.

Finally, $Z_S(f_S, |\cdot|^s_{F,S})$ is Schwartz uniformly over the vertical strips of bounded width of the complex half-plane $\mathbf{C}_{>0}$ by the Uniform Riemann-Lebesgue Lemma of Proposition B.2.2.3, which applies as a consequence of Theorem 2.3.1.4 and Proposition 2.3.2.2. The $S$-local functional equation (see (3.3.1.3) from Theorem 3.3.1.1) together with the estimates on $\rho_S$ and its derivatives from Proposition 3.3.1.5) then exhibit $Z_S(f_S, |\cdot|^s_{F,S})$ as being indeed of the form $\Phi(s)u(s)$ with $\Phi$ Schwartz uniformly on the vertical strips of bounded width of the complex half-plane $\mathbf{C}_{>-N}$ for each fixed $N > 0$, and $u$ meromorphic with slow growth near its poles therein.

We give the idea of how to see this. Once $N > 0$ is fixed, we want to apply the Asymptotic Residue Theorem to $Z(f, |\cdot|^s_F)$ over a rectangle contained in $\mathbf{C}_{>-N-\varepsilon}$ for $\varepsilon > 0$ small enough and fixed (whose rightmost edge has abscissa $\sigma > 1$ and horizontal edges are let to tend to $\pm\infty$ vertically). Over the half-plane $\mathbf{C}_{>-N-\varepsilon}$, $Z_S(f_S, |\cdot|^s_{F,S})$ has its poles within the discrete subset of the zeros of $\prod_{v \in S_f} (1-q_v^{-s})$ (with multiplicity bounded above by their respective order of vanishing) and within the finite subset of the poles of the Archimedean local factors of the Hecke $L$-function $L(s, \chi)$. In particular, we define the function

$$
\Phi(s) := Z_S(f_S, |\cdot|^s_{F,S}) \prod_{v \in S_f} (1 - q_v^{-s}) p_N(s) \zeta_F(s) s(s-1)
$$

with $p_N$ any entire polynomial function on $\mathbf{C}$ whose zeros are located at the poles of $Z_S(f_S, |\cdot|^s_{F,S})$ counted with multiplicity. The meromorphic function $\Phi$ is entire, and Schwartz uniformly on the open non-empty vertical strips of bounded width contained within $\mathbf{C}_{>-N-\varepsilon}$ (to see this, we use Lemma D.3.1.1 and the Uniform Riemann-Lebesgue Lemma of Proposition B.2.2.3, which informs us of the rapid decay of $Z_S(f_S, |\cdot|^s_{F,S})$ over $\mathbf{C}_{>0}$) and since $u_N(s) := 1/(p_N(s)s(s-1))$ is meromorphic and has slow growth near its poles, then indeed $Z(f, |\cdot|_{F,S}) = \Phi(s)u_N(s)$ by (3.4.2.7), as claimed, and the Asymptotic Residue Theorem applies to $Z(f, |\cdot|^s_{F,S})$ over $\mathbf{C}_{>-N-\varepsilon}$.

## PDF page 149

**3.4. EIGENDISTRIBUTIONS AND WEIL'S IDENTITY** · **149**

The identity from (3.4.2.7) then implies that the Asymptotic Residue Theorem applies to $Z(f,\lvert\cdot\rvert_F^s)$. We obtain, for every fixed real number $\sigma>1$, and every integer $N>0$:

(3.4.2.8)

$$
\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}M(\Phi_{F,\omega=1}(f)\circ\tau)(s)t^{-s}\,\mathrm{d}s=t^{-1}\bar{\mu}_1(C_F)\widehat{f}(0)-\bar{\mu}_1(C_F)f(0)+\frac{1}{2\pi i}\int_{-N-i\infty}^{-N+i\infty}M(\Phi_{F,\omega=1}(f)\circ\tau)(s)t^{-s}\,\mathrm{d}s.
$$

The leftmost side of (3.4.2.8) reads $\Phi_{F,\omega=1}(f)(\tau(t))$ by Fourier-Mellin inversion. We therefore deduce from (3.4.2.8) that the following identity holds:

(3.4.2.9)

$$
\Phi_{F,\omega=1}(f)(\tau(t))-t^{-1}\bar{\mu}_1(C_F)\widehat{f}(0)+\bar{\mu}_1(C_F)f(0)=\frac{1}{2\pi i}\int_{-N-i\infty}^{-N+i\infty}M(\Phi_{F,\omega=1}(f)\circ\tau)(s)t^{-s}\,\mathrm{d}s.
$$

The following estimate therefore holds:

(3.4.2.10)

$$
\lvert\Phi_{F,\omega=1}(f)(\tau(t))-t^{-1}\bar{\mu}_1(C_F)\widehat{f}(0)+\bar{\mu}_1(C_F)f(0)\rvert\le\frac{t^N}{2\pi}\lVert M(\Phi_{F,\omega=1}(f)\circ\tau)(-N+ix)\rVert_{L^1(\mathbf{R},\mathrm{d}x)}
$$

as $t\to 0^+$ (the only regime in which the bound is useful). Note that the estimate in (3.4.2.10) does not depend on $\sigma$.

We now apply the Asymptotic Residue Theorem (see Theorem B.3.2.1) one more time, to obtain, for every integer $N>1$ and for every real number $\sigma\in(1,N)$:

(3.4.2.11)

$$
\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}M(\Phi_{F,\omega=1}(f)\circ\tau)(s)t^{-s}\,\mathrm{d}s=\frac{1}{2\pi i}\int_{N-i\infty}^{N+i\infty}M(\Phi_{F,\omega=1}(f)\circ\tau)(s)t^{-s}\,\mathrm{d}s
$$

since $Z(f,\lvert\cdot\rvert_F^s)$ has no poles in the vertical strip $\mathbf{C}_{(\sigma-\varepsilon,N+\varepsilon)}$ for all small enough $\varepsilon>0$ and hence the same can be said about $Z(f,\lvert\cdot\rvert_F^s)t^{-s}$.

The leftmost side of (3.4.2.11) is $\Phi_{F,\omega=1}(f)(\tau(t))$ by Mellin inversion (see Theorem B.2.1.7 and Proposition B.2.1.8), and the rightmost side is bounded above by $\frac{t^{-N}}{2\pi}\lVert M(\Phi_{F,\omega=1}(f)\circ\tau)(N+ix)\rVert_{L^1(\mathbf{R},\mathrm{d}x)}$, leading to the estimate:

(3.4.2.12)

$$
\lvert\Phi_{F,\omega=1}(f)(\tau(t))\rvert\le\frac{t^{-N}}{2\pi}\lVert M(\Phi_{F,\omega=1}(f)\circ\tau)(N+ix)\rVert_{L^1(\mathbf{R},\mathrm{d}x)}
$$

as $t\to+\infty$. Once again we observe that the estimate in (3.4.2.12) does not depend on $\sigma$.

For $\omega\ne 1$, the meromorphic function $Z(f,c)$ restricted to $\Omega(C_F)(\omega)$ has no poles, and the same argument as in the foregoing shows that the Asymptotic Residue Theorem applies to it, leading to the estimates, for each integer $N>1$:

(3.4.2.13)

$$
\lvert\Phi_{F,\omega}(f)(\tau(t))\rvert\le\frac{t^{-N}}{2\pi}\lVert M(\Phi_{F,\omega}(f)\circ\tau)(N+ix)\rVert_{L^1(\mathbf{R},\mathrm{d}x)}
$$

as $t\to+\infty$, and, for every integer $N>0$:

(3.4.2.14)

$$
\lvert\Phi_{F,\omega}(f)(\tau(t))\rvert\le\frac{t^N}{2\pi}\lVert M(\Phi_{F,\omega}(f)\circ\tau)(-N+ix)\rVert_{L^1(\mathbf{R},\mathrm{d}x)}
$$

as $t\to 0^+$. We established the Theorem for $N>1$, so we are done. $\square$

REMARK 3.4.2.4. Using compatibility of the global $\theta$-function operator $\Phi_F$ with directional derivatives (see Lemma 2.2.4.3) in combination with the Uniform Riemann-Lebesgue Lemma of Theorem D.3.4.2, it is indeed possible to prove the “non $\omega$-homogeneous” version of the estimates in Theorem 3.4.2.2 proved in Theorem 2.2.3.4.

This reads, for any fixed integer $N\ge 0$, for any $f\in\mathcal{S}(\mathbf{A}_F)$:

(3.4.2.15)

$$
\lvert\Phi_{F,\omega}(f)(g)\rvert\le C_N\lvert g\rvert_F^{-N}
$$

## PDF page 150

**150** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

as $\lvert g\rvert_F\to+\infty$ for some real number $C_N>0$, and

(3.4.2.16)

$$
\lvert\Phi_F(f)(g)-(\lvert g\rvert_F^{-1}\widehat{f}(0)-f(0))\delta(g)\rvert\le C_N\lvert g\rvert_F^N
$$

for some real number $C_N>0$ and as $\lvert g\rvert_F\to 0^+$, where

$$
\delta:C_F\to\mathbf{C}
$$

is the bounded function on $C_F$ defined in (3.4.2.6). We note that the Fourier transform of the bounded function $\delta$ in (3.4.2.6) is supported on the connected component of the trivial character in $\widehat{C_F}$ (namely the space of characters $c$ trivial on $C_F^1$).

In other words, through Weil's Identity which we discussed in Theorem 3.4.1.1, we can read off the estimates from Theorem 2.2.3.4 from the forward side of the Mellin transform, through properties of Hecke $L$-functions (analytic continuation, functional equation, polynomial growth of $L_f(s,\chi)$ uniformly on vertical strips of bounded width, all of which are discussed in Appendix B).

We sketch the method here, to shed light on the nature of the uniform constants $C_{\mathcal{B},N}$ from Theorem 2.2.5.4. We use the functional equation from (3.2.2.2), giving the identity

$$
M(\Phi_{F,\omega}(f)\circ\tau)(-N+ix)=M(\Phi_{F,\bar{\omega}}(\widehat{f})\circ\tau)(1+N-ix)
$$

as functions of $x\in\mathbf{R}$. We now assume $N>1$, so that the estimates in (3.4.2.10) and (3.4.2.12), respectively (3.4.2.13) and (3.4.2.14), all hold at the same time with this fixed choice of $N$.

The functions of $\omega$ given by

$$
\lVert M(\Phi_{F,\omega}(f)\circ\tau)(N+ix)\rVert_{L^1(\mathbf{R},\mathrm{d}x)},\; \lVert M(\Phi_{F,\bar{\omega}}(f)\circ\tau)(1+N-ix)\rVert_{L^1(\mathbf{R},\mathrm{d}x)}
$$

are integrable with respect to the Plancherel measure to the Haar measure $\bar{\mu}_1$ on $C_F^1$. Note that since $C_F^1$ is compact Hausdorff, the Plancherel measure on $\widehat{C_F^1}$ of the measure $\bar{\mu}_1$ on $C_F^1$ (see [DE, Thm.3.4.8] for the definition of the Plancherel measure on the dual of a Hausdorff locally compact abelian group equipped with a choice of Haar measure) is a nonzero multiple of the counting measure.

We observe that it implies (3.4.2.15) and (3.4.2.16). Indeed, from (3.4.2.10), (3.4.2.12), (3.4.2.13) and (3.4.2.14), and using the Hausdorff-Young inequality applied to the Fourier transform on $C_F^1$, we obtain the estimates

(3.4.2.17)

$$
\lvert\Phi_F(f)(g)\rvert\le\frac{\lvert g\rvert_F^N}{2\pi}\lVert M(\Phi_{F,\bar{\omega}}(\widehat{f})\circ\tau)(1+N-ix)\rVert_{L^1(\mathbf{R}\times\widehat{C_F^1},\mathrm{d}x\otimes\mathrm{d}\widehat{\overline{\mu}}_1)}
$$

as $\lvert g\rvert_F<1$, and

(3.4.2.18)

$$
\lvert\Phi_F(f)(g)-(\lvert g\rvert_F^{-1}\widehat{f}(0)-f(0))\delta(g)\rvert\le\frac{\lvert g\rvert_F^{-N}}{2\pi}\lVert M(\Phi_{F,\omega}(f)\circ\tau)(N+ix)\rVert_{L^1(\mathbf{R}\times\widehat{C_F^1},\mathrm{d}x\otimes\mathrm{d}\widehat{\overline{\mu}}_1)}.
$$

as $\lvert g\rvert_F>1$.

We now, at last, recognize the constants

$$
C_N(f):=\frac{1}{2\pi}\lVert M(\Phi_{F,\bar{\omega}}(\widehat{f})\circ\tau)(1+N-ix)\rVert_{L^1(\mathbf{R}\times\widehat{C_F^1},\mathrm{d}x\otimes\mathrm{d}\widehat{\overline{\mu}}_1)},\; C_N'(f):=\frac{1}{2\pi}\lVert M(\Phi_{F,\omega}(f)\circ\tau)(N+ix)\rVert_{L^1(\mathbf{R}\times\widehat{C_F^1},\mathrm{d}x\otimes\mathrm{d}\widehat{\overline{\mu}}_1)}
$$

as serving the same role of the constants $C_N$ from Theorem 2.2.5.4. They depend on $f$ (and on $N$, as they should), but they do so continuously in $f$. This will be shown much later throughout this treatise, and the proof of this fact will *not* use Theorem 2.2.5.4 and the uniform constants $C_{\mathcal{B},N}$ as an input!

Proving continuity of $C_N(f)$ and $C_N'(f)$ on the forward side of the Mellin transform only, is, in other words, indeed possible. All the work we did in Theorem 2.2.3.4 and Theorem 2.2.5.4 however has to be shifted elsewhere, then. It is indeed shifted into Theorem 2.4.2.1 and Proposition 2.3.1.2 (the $S$-local counterparts to Theorem 2.2.3.4 and Theorem 2.2.5.4), which will lead to a proof of continuity of the $S$-idelic Zeta

## PDF page 151

**3.4. EIGENDISTRIBUTIONS AND WEIL'S IDENTITY** · **151**

function operators $Z_S$ taking values in $\mathcal{S}_{(0,+\infty)}(J_{F,S})$ (the nuclear strict LF-space of $I$-exponentially decaying Schwartz-Bruhat functions on $J_{F,S}$, with $I=(0,+\infty)$, see Definition D.3.3.3 in Appendix D).

The remaining ingredient is then the Convexity Bound on the finite Hecke $L$-function (see Proposition B.1.1.3), combined with Weil's Identity in the unramified case (Theorem 3.4.1.1) and in the general case, to be proved in Theorem 3.4.3.3 by the end of this Chapter (using eigendistributions).

This Remark wants to point out to the reader how the uniform constants $C_{\mathcal{B},N}$ from the estimates from Theorem 2.2.3.4 come to life, i.e. where they come from and how they can be thought of. They arise as maxima over bounded subsets in $\mathcal{S}(\mathbf{A}_F)$, of continuous seminorms on $\mathcal{S}(\mathbf{A}_F)$. This is the punchline of this Remark. The fact that such maxima exist is due to an important structural property of $\mathcal{S}(\mathbf{A}_F)$: it is a Montel space. This means, concretely, that a version of Ascoli-Arzelà holds within it. Specifically, bounded subsets are relatively compact (equivalently precompact, since $\mathcal{S}(\mathbf{A}_F)$ is complete). This is why continuous functions (hence in particular the continuous functions $C_N(f)$ and $C_N'(f)$), can be maximized over the bounded subsets of $\mathcal{S}(\mathbf{A}_F)$. Ultimately, however, some work with concrete estimates and lattice point-counting techniques has to be done: indeed, Theorem 2.4.2.1 and Proposition 2.3.1.2 are, for all practical purposes, unavoidable.

Proving the continuity aspects of the formation of $Z_S(f,c)$, even for $c\in\Omega(J_{F,S})_{>0}$, requires the bounds proved therein as inputs. Throughout the arguments in the proofs of Theorem 2.4.2.1 and Proposition 2.3.1.2 and those bounds, we find that once again the Montel property of the $S$-local Schwartz-Bruhat spaces $\mathcal{S}(\mathbf{A}_{F,S})$ is used therein, to maximize certain continuous seminorms on bounded subsets in the process of maximizing constants dependent on the Schwartz-Bruhat function, and obtain the $C_{\mathcal{B},1}$ and $C_{\mathcal{B},2}$ in Theorem 2.4.2.1, and the $C_{\mathcal{B},N}$ in Proposition 2.3.1.2.

This gives a big-picture idea to the reader of how the elements of this work fit together: a detailed study of the $S$-local $\theta$-functions and Zeta functions is required, because proving assertions on their global analogs is then done by reduction to the $S$-local case, where more flexibility is available and arguments are concrete and manageable. This is what the first nine Chapters of this work are for.

“Global-to-$S$-local” is the motto to keep in mind, entering the next Chapter and up to the very main trace calculation. The “global-to-$S$-local” general rule of thumb will underlie the trace calculation itself.

**3.4.3. Eigendistributions and Weil's Identity: the general case.** We will need an extension of the identity in (3.4.1.6) to the case $\chi$ is not unramified outside $S$. To this end we will be using the completed Hecke $L$-function $L(s,\chi)$ as opposed to the finite Hecke $L$-function $L_f(s,\chi)$ with finitely many Euler factors removed, i.e. $L_{\Sigma_F-S}(\chi,s)$, and we will be using results of Weil on local and global eigendistributions from [Weil-a, §1,3], whose main elements we briefly recall below, to be reprised in the next Chapter.

DEFINITION 3.4.3.1. Let $F$ be a number field, $v$ a place of $F$, $F_v$ the completion of $F$ at $v$.

(1) Let $c\in\Omega(F_v^{\times})$ be a quasi-character. We say $T\in\mathcal{S}(F_v)'_{\beta}$ is an *eigendistribution of weight $c$* if and only if:

(3.4.3.1)

$$
\rho_v'(g,T)=c(g)T
$$

for all $g\in F_v^{\times}$, where $\rho_v'$ is the dual of the continuous right-translation action $\rho_v:F_v^{\times}\times\mathcal{S}(F_v)\to\mathcal{S}(F_v)$; i.e., $(\rho_v'(g,T))(f)=T(f\circ m_g)$ where $m_g$ is $g$-multiplication on $F_v$. We denote by $\mathcal{S}(F_v)'_{\beta}(c)$ the closed subspace of $\mathcal{S}(F_v)'_{\beta}$ of eigendistributions on $F_v$ of weight $c$.

(2) For $c\in\Omega(C_F)$ an idelic quasi-character, say $T\in\mathcal{S}(\mathbf{A}_F)'_{\beta}$ is a *global eigendistribution of weight $c$* if

(3.4.3.2)

$$
\rho_F'(g,T)=c(g)T
$$

for all $g\in\mathrm{GL}_1(\mathbf{A}_F)$, where $\rho_F'$ is the dual of the continuous right-translation action $\rho_F:\mathrm{GL}_1(\mathbf{A}_F)\times\mathcal{S}(\mathbf{A}_F)\to\mathcal{S}(\mathbf{A}_F)$.

We denote by $\mathcal{S}(\mathbf{A}_F)'_{\beta}(c)$ the closed subspace of $\mathcal{S}(\mathbf{A}_F)'_{\beta}$ of eigendistributions on $\mathbf{A}_F$ of weight $c$. We refer to the elements of $\mathcal{S}(\mathbf{A}_F)'_{\beta}(c)$ as *global eigendistributions of weight $c$*.

Definition 3.4.3.1(2) will be recalled again in Definition 5.5.1.1.

## PDF page 152

**152** · **CHAPTER 3. IDELIC ZETA FUNCTIONS**

3.4.3.1. *Standard Gaussians local and global Schwartz-Bruhat functions.* We begin with the following definition:

DEFINITION 3.4.3.2 (Standard Gaussians). Let $F$ be a number field, $\omega\in\widehat{C_F^1}$ a continuous character (labeling a connected component of $\Omega(C_F)$).

We define Schwartz-Bruhat functions $E_{\omega_v,v}$ on $F_v$, for each place $v$ of $F$.

(1) for $v$ real Archimedean:

(a) if $\omega_v=1$

(3.4.3.3)

$$
E_{1,v}(x):=e^{-\pi x^2}.
$$

(b) if $\omega_v=\mathrm{sgn}$, the sign character

(3.4.3.4)

$$
E_{\mathrm{sgn},v}(x):=xe^{-\pi x^2}.
$$

(2) For $v$ complex Archimedean, if $\omega_v=\omega_{t,m}:re^{i\theta}\mapsto r^te^{im\theta}$

(a) for $m\ge 0$

(3.4.3.5)

$$
E_{m,v}(z):=\frac{1}{2\pi}z^me^{-2\pi z\bar{z}}.
$$

(b) For $m<0$

(3.4.3.6)

$$
E_{m,v}(z):=\frac{1}{2\pi}\bar{z}^{-m}e^{-2\pi z\bar{z}}
$$

(3) For $v$ non-Archimedean:

(3.4.3.7)

$$
E_v(x):=1_{\mathcal{O}_{F_v}}.
$$

For $S_{\omega}$ the finite set of finite places of $F$ at which $\omega$ is ramified, we further define for $v\in S_{\omega}$:

(3.4.3.8)

$$
E_{\omega_v,v}(x):=\omega_v^{-1}1_{\mathcal{O}_{F_v}^{\times}}.
$$

For $c\in\Omega(C_F)$ a fixed quasi-character we denote by $E_{c,v}$, abbreviating to $E_v$ if no confusion can arise, the local Schwartz-Bruhat function defined above associated to the character $c|_{C_F^1}$ of $C_F^1$. We define the global Schwartz-Bruhat function:

(3.4.3.9)

$$
E_c:=\bigotimes_{v\in\Sigma_F}E_{c_v,v}.
$$

We abbreviate the notation for $E_c$ to $E$ when no confusion can arise.

We refer to the local Schwartz-Bruhat functions $E_{c_v,v}$, for $v$ Archimedean, respectively non-Archimedean, and to the global Schwartz-Bruhat function $E_c$, as *standard Gaussian* Schwartz-Bruhat functions.

The completed Hecke $L$-function $c\mapsto L(c)$ is defined, upon choosing a parametrization $\chi\lvert\cdot\rvert_F^s$ of $\Omega(C_F)$ for $\chi\in\widehat{C_F}$ a continuous character, to be $Z(E_{\chi},s)$. This function near $c$ depends only on the connected component of $c$ in $\Omega(C_F)$, which is to say on restriction of $c$ to $C_F^1$.

3.4.3.2. *Weil's Identity: the general case.* Weil classified the local and global eigendistributions. We provide the statements below for later reference:

THEOREM 3.4.3.3 (Weil's Identity - II). *Let $F$ be a number field, $v$ a place of $F$. We equip $\mathrm{GL}_1(\mathbf{A}_F)$ and each $F_v^{\times}$ with the global, respectively local, multiplicative Tamagawa measures $\mu$, $\mu_v$.*

*(1) For every $c\in\Omega(F_v^{\times})$, we have $\dim_{\mathbf{C}}\mathcal{S}(F_v)'(c)=1$. There exists a unique generator $\Delta_v'(c)$ of $\mathcal{S}(F_v)'(c)$ determined by the condition:*

## PDF page 153

**3.4. EIGENDISTRIBUTIONS AND WEIL'S IDENTITY** · **153**

(1) *If $v$ is non-Archimedean and $c$ is unramified at $v$:*

(3.4.3.10)

$$
\langle\Delta_v'(c),E_v\rangle_{\mathcal{S}(F_v)'_{\beta},\mathcal{S}(F_v)}=1.
$$

(2) *If $v$ is non-Archimedean and $c$ is ramified at $v$:*

(3.4.3.11)

$$
\langle\Delta_v'(c),c^{-1}1_{\mathcal{O}_{F_v}^{\times}}\rangle_{\mathcal{S}(F_v)'_{\beta},\mathcal{S}(F_v)}=1.
$$

(3) *If $v$ is Archimedean:*

(3.4.3.12)

$$
\langle\Delta_v'(c),E_{c_v,v}\rangle_{\mathcal{S}(F_v)'_{\beta},\mathcal{S}(F_v)}=1.
$$

*For any place $v$ of $F$, the function $c\mapsto\Delta_v'(c)$ is a holomorphic function $\Omega(F_v^{\times})\to\mathcal{S}(F_v)'_{\beta}$. The following identity holds, as meromorphic $\mathcal{S}(F_v)'_{\beta}$-valued functions on $\Omega(F_v^{\times})$:*

(3.4.3.13)

$$
Z_v(\cdot,c)=L_v(c)\Delta_v'(c)
$$

*where $L_v$ is the local factor at $v$ of the completed Hecke $L$-function.*

*(2) For every $c\in\Omega(C_F)$, we have $\dim_{\mathbf{C}}\mathcal{S}(\mathbf{A}_F)'(c)=1$. The following tempered distribution in $\mathcal{S}(\mathbf{A}_F)'$*

(3.4.3.14)

$$
\Delta'(c):=\bigotimes_{v\in\Sigma_F}\Delta_v'(c)
$$

*is a global eigendistribution of weight $c$ (see Remark 3.4.3.4 for the meaning of the right side as a continuous linear functional on $\mathcal{S}(\mathbf{A}_F)$). The function $c\mapsto\Delta'(c)$ is a holomorphic function $\Omega(C_F)\to\mathcal{S}(\mathbf{A}_F)'_{\beta}$. The following identity holds, as meromorphic $\mathcal{S}(\mathbf{A}_F)'_{\beta}$-valued functions on $\Omega(C_F)$:*

(3.4.3.15)

$$
Z(\cdot,c)=L(c)\Delta'(c)
$$

*where $c\mapsto L(c)$ is the completed Hecke $L$-function.*

REMARK 3.4.3.4. For the right side of (3.4.3.14) to act continuously on $\mathcal{S}(\mathbf{A}_F)$, we use that $\mathcal{S}(\mathbf{A}_F)=(\bar{\otimes}_{v\mid\infty}\mathcal{S}(F_v))\otimes(\otimes_{v\nmid\infty}\mathcal{S}(F_v))$ as a locally convex inductive limit in which all tensor products are given the inductive topology and $\bar{\otimes}$ denotes completion for $\otimes_{v\mid\infty}\mathcal{S}(F_v)$. The topology on the latter (even prior to completion) coincides with both the projective and injective topologies on that tensor product since $\mathcal{S}(F_v)$ for archimedean $v$ is Fréchet: Corollary C.2.3.12 gives equality with the projective topology, and nuclearity of the $\mathcal{S}(F_v)$'s for such $v$ gives equality of the projective and injective tensor product topologies.

PROOF. We refer the reader to [Weil-a, §1,3] for (1) and (2) with the exception of the holomorphy aspects, which, in turn, follow from Theorem C.5.2.6 and Theorem C.5.2.4, since, for every $f\in\mathcal{S}(F_v)$, the function $c\mapsto\langle\Delta_v'(c),f\rangle_{\mathcal{S}(F_v)'_{\beta},\mathcal{S}(F_v)}$ is a holomorphic function of $c\in\Omega(F_v^{\times})$, and, for every $f\in\mathcal{S}(\mathbf{A}_F)$, the function $c\mapsto\langle\Delta_v'(c),f\rangle_{\mathcal{S}(F_v)'_{\beta},\mathcal{S}(F_v)}$ is a holomorphic function of $c\in\Omega(C_F)$. We note that Theorem C.5.2.6 and Theorem C.5.2.4 apply since $\mathcal{S}(F_v)'_{\beta}$ is complete, hence quasi-complete.

We further refer the reader to [Kudla, pp.109-130] and specifically to [Kudla, Lemma 3.2,3.3] for the structural results of local eigendistributions. Especially to [Kudla, Thm.3.4] for their existence and uniqueness up to nonzero scalar multiplication, i.e. the one-dimensionality of $\mathcal{S}(F_v)'_{\beta}(c)$ for any continuous quasi-character $c$ of $F_v^{\times}$. This proves (1).

We refer the reader to [Kudla, Lemma 4.1], for the case of global eigendistributions, i.e. $c$-homogeneous continuous functionals in $\mathcal{S}(\mathbf{A}_F)'$, for $c\in\Omega(C_F)$, and particularly to [Kudla, Thm.4.2] for the existence and uniqueness of global eigendistributions up to nonzero scalar multiplication, i.e. the one-dimensionality of $\mathcal{S}(\mathbf{A}_F)'(c)$ for any continuous idelic quasi-character. Similarly, the function $c\mapsto\Delta'(c)$ is a holomorphic $\mathcal{S}(\mathbf{A}_F)'_{\beta}$-valued function, by Theorem C.5.2.6 and Theorem C.5.2.4, both of which apply since $\mathcal{S}(\mathbf{A}_F)'_{\beta}$ is complete, hence quasi-complete (see Proposition 2.1.3.2). $\square$

## PDF page 154
