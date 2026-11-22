## PDF page 221

CHAPTER 5

**Spaces of adelic $\theta$-functions and Idelic $Z$-functions**

5.1. The topological vector spaces of adelic $\theta$-functions and Idelic $Z$-functions · 221

5.1.1. Definition of the global and $S$-local spaces of adelic $\theta$-functions and Idelic $Z$-functions · 222

5.1.2. The kernels of the $S$-local and global adelic $\theta$-function operators · 224

5.1.3. Continuity of the Mellin transform operators · 226

5.2. Structure Theorem I: topology of the spaces of adelic $\theta$-functions · 230

5.2.1. Topology of $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ and $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$ · 230

5.2.2. Isotypes of $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ and $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$ · 232

5.2.3. First Structure Theorem on $\mathrm{H}_{0,\mathrm{cont}}(\omega, \mathcal{S}(\mathbf{A}_F))$, $\mathrm{H}_{0,\mathrm{cont}}(\omega_S, \mathcal{S}(\mathbf{A}_{F,S}))$ · 233

5.2.4. Interaction with the Fourier Transform · 238

5.3. Weil's Principal Value Operators · 240

5.3.1. Non-Archimedean Principal Value Operators · 240

5.3.2. Preparations on tempered distributions supported at the origin · 243

5.3.3. Smoothness and rapid decay of extensions by zero · 249

5.3.4. Weil's Principal Value Operators and holomorphic $S$-idelic Zeta functions · 259

5.4. Structure Theorem II: $S$-local Čech sequence · 265

5.4.1. Second Structure Theorem · 265

5.4.2. $S$-local Čech sequences · 274

5.5. Structure Theorem III: strong duals and Eigendistributions · 277

5.5.1. Eigendistributions and the strong duals of $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$ and $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ · 277

5.5.2. An example: global eigendistributions of weight $c=1, \lvert\cdot\rvert_F$ · 280

5.5.3. Third Structure Theorem · 281

**5.1. The topological vector spaces of adelic $\theta$-functions and Idelic $Z$-functions**

Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. In this subsection we define the Hausdorff locally convex topological $\mathbf{C}$-vector space

$$
\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))
$$

of continuous co-invariants of the left-translation action by $F^{\times}$ on the Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}(\mathbf{A}_F)$ of Schwartz-Bruhat functions on $\mathbf{A}_F$. After defining it, $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ will be identified with a Hausdorff quotient of the $\mathbf{C}$-linear space of algebraic co-invariants

$$
\mathrm{H}_0(F^{\times}, \mathcal{S}(\mathbf{A}_F)) = \mathrm{Tor}^{\mathbf{Z}[F^{\times}]}_0(\mathbf{Z}, \mathcal{S}(\mathbf{A}_F)) = \mathbf{Z}\otimes_{\mathbf{Z}[F^{\times}]}\mathcal{S}(\mathbf{A}_F)
$$

of $\mathcal{S}(\mathbf{A}_F)$ under the left-translation action by the discrete subgroup $F^{\times}\subset\mathrm{GL}_1(\mathbf{A}_F)$, which promotes $\mathcal{S}(\mathbf{A}_F)$ to a (continuous $\mathbf{Z}[F^{\times}]$-module. The ring map $\mathbf{Z}[F^{\times}]\to\mathbf{Z}$ is the augmentation map. These will be spaces of global, respectively $S$-local, adelic $\theta$-functions, topologized as quotients of $\mathcal{S}(\mathbf{A}_F)$, respectively $\mathcal{S}(\mathbf{A}_{F,S})$.

221

## PDF page 222

**222** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC $Z$-FUNCTIONS**

We will study the topology on $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ and prove several structural results in the spirit of Proposition 2.1.4.1 for $\mathcal{S}(\mathbf{A}_F)$, by relating $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ to its $S$-local analogs $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$, in turn a Hausdorff quotient of the $\mathbf{C}$-linear space of algebraic co-invariants $\mathrm{H}_0(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$ of the $\mathbf{Z}[\mathcal{O}_{F,S}^{\times}]$-module $\mathcal{S}(\mathbf{A}_{F,S})$.

The main ingredients in the arguments for the main results of this Chapter are the existence of the analytic continuation to the idelic zeta functions as per Theorem 3.2.2.1, the structural results on $\mathcal{S}(\mathbf{A}_F)$ and their $S$-local analogs, and the Asymptotic Residue Theorem (see Theorem B.3.2.1), applicable by known estimates on the order of growth of Hecke $L$-functions and related meromorphic functions uniformly on vertical strips of bounded width, recalled in Appendix B.

At least formally, there is some overlap between some of the results discussed throughout this Chapter, and some of the results from [Me1, §4], insofar as some of the statements from [Me1, §4.6,4.7] are formally analogous, and at times their proofs share some elements in common (with particular emphasis on the use of multiplier operators from [Me1, §4.7] in the proof of [Me1, §4.7,Lemma 4.20,p.20]. We will be using similar operators, constructed and discussed at length in §5.3.1 of this Chapter, to a similar effect throughout the proof of Theorem 5.4.1.1, even though the statement of Theorem 5.4.2.2 from §5.4.2, a consequence of Theorem 5.4.1.1, is different, though analogous, to [Me1, §4.7,Lemma 4.20,p.20]).

We will be referring the reader to the relevant contents from [Me1, §4] whenever appropriate, explaining the similarities and differences. An important difference that we record here from the outset, is that the results being discussed in this Chapter concern the Hausdorff locally convex topologies on $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$, $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$, as well as their corresponding spaces of meromorphic functions on the Riemann surfaces $\Omega(C_F)$, respectively $\Omega(J_{F,S})$, under the Mellin transform, while those results from [Me] that find analogs throughout this Chapter, are concerned with the von Neumann bornologies underlying the topological vector spaces which are the subject of our study.

These are referred to as bornological vector spaces in [Me1] (see also [Me2] and [Me3]), with the caveat that, therein and in the quoted references, a bornological vector space is meant to be a complex vector space equipped with a bornology of bounded subsets, rather than a Hausdorff locally convex topological vector space which is bornological (see [NB, Ch.13,§13.2]). The latter class provides examples of the bornological vector spaces from the former.

We further refer the reader to Remark 5.2.3.4.

**5.1.1. Definition of the global and $S$-local spaces of adelic $\theta$-functions and Idelic $Z$-functions.** For any Schwartz-Bruhat function $f\in\mathcal{S}(\mathbf{A}_F)$, respectively $f\in\mathcal{S}(\mathbf{A}_{F,S})$, the resulting idelic zeta integral $Z(f,c)$, respectively $Z_S(f,c)$, as defined in (3.2.2.1), respectively in (3.3.1.1), is, recall:

$$
Z(f,c) := \int_{\mathrm{GL}_1(\mathbf{A}_F)}f(g)c(g)\,\mathrm{d}\mu(g),\quad Z_S(f,c) := \int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}f(g)c(g)\,\mathrm{d}\mu_S(g)
$$

for $c\in\Omega(C_F)_{>1}$, respectively $c\in\Omega(J_{F,S})_{>0}$, and Theorem 3.2.2.1, respectively Theorem 3.3.1.1 shows that $Z(f,c)$ and $Z_S(f,c)$ extend to meromorphic functions over $\Omega(C_F)$, respectively $\Omega(J_{F,S})$, whose only poles are located within the subsets $\{c=1, c=\lvert\cdot\rvert_F\}$, respectively among the poles of the meromorphic function $\rho_S$ over $\Omega(J_{F,S})$ from (3.3.1.3): they are at most simple, in the former case, and they are counted with multiplicity bounded above by the polar multiplicity of each pole of $\rho_S(c)$, in the latter.

The Theorems further provide equivalent ways to write $Z(f,c)$ and $Z_S(f,c)$ in terms of the $\theta$-function operators $\Phi_F$, $\Phi_{F,\omega}$, $\Phi_{F,S}$ and $\Phi_{F,S,\omega}$, where $\omega$ is the restriction of $c$ to $C^1_F$, respectively $J^1_{F,S}$.

Namely, $Z(f,c)$ and $Z_S(f,c)$ are obtained as Mellin transforms over $C_F$, respectively $J_{F,S}$, of $\Phi_F(f)$, respectively $\Phi_{F,S}(f)$, up to a vertical translation on the complex $s$-plane uniquely determined by a choice of continuous character $\chi\in\widehat{C_F}$, respectively $\chi\in\widehat{J_{F,S}}$, extending to $C_F$, respectively $J_{F,S}$, the continuous

## PDF page 223

**5.1. THE TOPOLOGICAL VECTOR SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC $Z$-FUNCTIONS** · **223**

character $\omega\in\widehat{C^1_F}$, respectively $\omega\in\widehat{J^1_{F,S}}$, and on a choice of continuous homomorphic section to the idelic, respectively $S$-idelic, norm.

We now define linear spaces whose elements are adelic $\theta$-functions, both global and $S$-local, respectively, and their corresponding spaces of meromorphic functions, and topologize them using the Hausdorff locally convex topology of the Schwartz-Bruhat spaces $\mathcal{S}(\mathbf{A}_F)$, respectively $\mathcal{S}(\mathbf{A}_{F,S})$.

Definition 5.1.1.1 (Spaces of adelic $\theta$-functions and Idelic $Z$-functions). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

(1) Let $f\in\mathcal{S}(\mathbf{A}_F)$ be a Schwartz-Bruhat function. We denote by $Z(f,c)$ the analytic continuation to $\Omega(C_F)$ of the function of $c\in\Omega(C_F)_{>1}$ from (3.2.2.1), and refer to it as the global idelic $Z$-function of $f$. We denote by:

$$
Z : \mathcal{S}(\mathbf{A}_F)\to\mathscr{M}(\Omega(C_F)) \tag{5.1.1.1}
$$

the linear operator sending $f\in\mathcal{S}(\mathbf{A}_F)$ to the idelic $L$-function $Z(f,c)$ as an element of the complex vector space $\mathscr{M}(\Omega(C_F))$ of meromorphic functions on $\Omega(C_F)$ whose poles are contained within the subset $\{1, \lvert\cdot\rvert_F\}\subset\Omega(C_F)$. We refer to the linear operator $Z$ from (5.1.1.1) as the global Idelic Mellin transform.

(2) Let $f\in\mathcal{S}(\mathbf{A}_{F,S})$ be a Schwartz-Bruhat function. We denote by $Z_S(f,c)$ the analytic continuation to $\Omega(J_{F,S})$ of the function of $c\in\Omega(J_{F,S})_{>0}$ from (3.3.1.1), and refer to it as the local $S$-idelic $L$-function of $f$. We denote by:

$$
Z_S : \mathcal{S}(\mathbf{A}_{F,S})\to\mathscr{M}(\Omega(J_{F,S})) \tag{5.1.1.2}
$$

the linear operator sending $f\in\mathcal{S}(\mathbf{A}_{F,S})$ to the $S$-idelic $Z$-function $Z_S(f,c)$ as an element of the complex vector space $\mathscr{M}(\Omega(J_{F,S}))$ of meromorphic functions on $\Omega(J_{F,S})$ whose poles are contained within the subset $\mathcal{U}_S$ of $\Omega(J_{F,S})$ of the poles of $\rho_S(c)$ from (3.3.1.3). We refer to the linear operator $Z_S$ from (5.1.1.2) as the $S$-local Idelic Mellin transform.

(3) We define:

$$
\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F)) := \mathcal{S}(\mathbf{A}_F)/\ker(\Phi_F),\quad \mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S})) := \mathcal{S}(\mathbf{A}_{F,S})/\ker(\Phi_{F,S}) \tag{5.1.1.3}
$$

equipped with the quotient topologies. We denote by

$$
Z : \mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))\to\mathscr{M}(\Omega(C_F)),\quad Z_S : \mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))\to\mathscr{M}(\Omega(J_{F,S})) \tag{5.1.1.4}
$$

the operators induced by $Z$ from (5.1.1.1) by factorization through $\Phi_F$, respectively $Z_S$ from (5.1.1.2) by factorization through $\Phi_{F,S}$. We refer to the operators $Z$, respectively $Z_S$, from (5.1.1.4), as the global, respectively $S$-local, Idelic Mellin transforms.

(4) We define:

$$
\mathcal{Z}_F := Z(\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F)))\subset\mathscr{M}(\Omega(C_F))\quad \mathcal{Z}_{F,S} := Z_S(\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S})))\subset\mathscr{M}(\Omega(J_{F,S})) \tag{5.1.1.5}
$$

equipped with the linear topologies induced by the Mellin transforms $Z$, respectively $Z_S$.

Remark 5.1.1.2. We note that the quotient topologies on $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$, respectively $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$, are locally convex by [Scha, Ch.II,§6,pp.54-55]. They are Hausdorff so long as $\ker(\Phi_F)$, respectively $\ker(\Phi_{F,S})$, are closed subspaces, which we have yet to prove (see Theorem 5.1.1.3 below).

The main result of this section is the following:

Theorem 5.1.1.3. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. The Mellin transform operators $Z$ on $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ and $Z_S$ on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$ are injective. Moreover:*

## PDF page 224

**224** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC $Z$-FUNCTIONS**

(1) *The kernels of $\Phi_F$ and $\Phi_{F,S}$ are closed as $\mathbf{C}$-linear subspaces of the Hausdorff locally convex topological $\mathbf{C}$-vector spaces $\mathcal{S}(\mathbf{A}_F)$, respectively $\mathcal{S}(\mathbf{A}_{F,S})$.*

(2) *For every $\omega\in\widehat{C^1_F}$, the kernel of the operator $\Phi_{F,\omega}$ is a closed $\mathbf{C}$-linear subspace of the Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}(\mathbf{A}_F)$.*

(3) *For every $\omega\in\widehat{J^1_{F,S}}$, the kernel of the operator $\Phi_{F,S,\omega}$ is a closed $\mathbf{C}$-linear subspace of the Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathcal{S}(\mathbf{A}_{F,S})$.*

The Theorem will enable to study the quotient topologies on $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ and $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$ induced by the operators $\Phi_F$, respectively $\Phi_{F,S}$, and deduce that such topologies are Hausdorff, locally convex, and promote each of them to complete LF-spaces that are nuclear and Montel, whose strong duals are complete, nuclear and Montel.

We will be recalling these concepts from the theory of Hausdorff locally convex topological vector spaces further, as the need arises.

In order to prove Theorem 5.1.1.3, we need preparations on the isotypes of the continuous actions of $C^1_F$ on $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$, and $J^1_{F,S}$ on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$, inherited from the continuous left-translation actions of $\mathrm{GL}_1(\mathbf{A}_F)$, respectively $\mathrm{GL}_1(\mathbf{A}_{F,S})$, on $\mathcal{S}(\mathbf{A}_F)$, respectively $\mathcal{S}(\mathbf{A}_{F,S})$, by restriction to the respective norm-one closed subgroups.

**5.1.2. The kernels of the $S$-local and global adelic $\theta$-function operators.** In this subsection we establish preparations on the kernels of the global and local adelic $\theta$-function operators, to prove Theorem 5.1.1.3, which asserts that their kernel is a closed subspace of $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}, \mathcal{S}(\mathbf{A}_{F,S}))$, respectively of $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$.

This is the first instance of a structural result on the locally convex topological $\mathbf{C}$-vector spaces $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}, \mathcal{S}(\mathbf{A}_{F,S}))$ and $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$, whose arguments rest on the idelic (both $S$-local and global) Mellin transform.

Specifically, we will be deducing that the quotient topologies on the spaces of adelic $\theta$-functions $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}, \mathcal{S}(\mathbf{A}_{F,S}))$ and $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ inherited from the $S$-local and global Schwartz-Bruhat spaces $\mathcal{S}(\mathbf{A}_{F,S})$ and $\mathcal{S}(\mathbf{A}_F)$, both locally convex, are also Hausdorff.

The structural results on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}, \mathcal{S}(\mathbf{A}_{F,S}))$ and $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ all initiate from here.

Lemma 5.1.2.1 (Kernels of global $\theta$-function and $Z$-function operators). *Let $F$ be a number field, $\omega\in\widehat{C^1_F}$ a continuous character. Let $Z : \mathcal{S}(\mathbf{A}_F)\to\mathscr{M}(\Omega(C_F))$ be the Idelic Mellin transform operator from (5.1.1.1). Then:*

(1) *We have, as $\mathbf{C}$-linear subspaces of $\mathcal{S}(\mathbf{A}_F)$:*

$$
\ker(Z) = \ker(\Phi_F). \tag{5.1.2.1}
$$

(2) *We have, as $\mathbf{C}$-linear subspaces of $\mathcal{S}(\mathbf{A}_F)$:*

$$
\ker(\Phi_{F,\omega}) = \{f\in\mathcal{S}(\mathbf{A}_F) : Z(f,c)|_{\Omega(C_F)(\omega)} = 0\}. \tag{5.1.2.2}
$$

Proof. (1) : Let $f\in\mathcal{S}(\mathbf{A}_F)$ be a Schwartz-Bruhat function, and assume that its adelic $\theta$-function satisfies $\Phi_F(f) = 0$. Then the function of $c\in\Omega(C_F)_{>1}$ given by:

$$
Z(f,c) = \int_{C_F}\Phi_F(f)(g)c(g)\,\mathrm{d}\bar{\mu}(g)
$$

vanishes for every $c\in\Omega(C_F)_{>1}$. Since $Z(f,c)$ is meromorphic over $\Omega(C_F)$ by Theorem 3.2.2.1(1), it vanishes identically over $\Omega(C_F)$ away from its poles by the Identity Theorem, and hence it is entire and identically zero.

Conversely, if $Z(f,c) = 0$ for all $c\in\Omega(C_F)-\{1, \lvert\cdot\rvert_F\}$, then for any choice of continuous homomorphic section $\tau$ to the idelic norm, the integral

$$
Z(f,c) = \int_{\mathbf{R}_{>0}}c(\tau(t))\Phi_{F,\omega}(f)(\tau(t))\,\frac{\mathrm{d}t}{t}
$$

## PDF page 225

**5.1. THE TOPOLOGICAL VECTOR SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC $Z$-FUNCTIONS** · **225**

vanishes for any $c\in\Omega(C_F)(\omega)_{>1}$ for any $\omega\in\widehat{C^1_F}$.

Since, if $\sigma(c) > 1$, the function $c(\tau(t))\Phi_{F,\omega}(f)(\tau(t))$ is Schwartz on $\mathbf{R}_{>0}$ by Theorem 2.2.5.4, then by Fourier inversion, since we have $Z(f,c\lvert\cdot\rvert^{ix}_F) = 0$ for every $x\in\mathbf{R}$, we deduce that we have $c(\tau(t))\Phi_{F,\omega}(f)(\tau(t)) = 0$ as continuous functions of $t\in\mathbf{R}_{>0}$. This holds for any $\omega\in\widehat{C^1_F}$, and by Lemma 4.3.2.2 we have $c\cdot\Phi_F(f) = 0$ as $\bar{\mu}$-measurable and square $\bar{\mu}$-integrable functions on $C_F$, $\bar{\mu}$-almost everywhere.

Since $c$ is continuous and nowhere vanishing over $C_F$, we deduce that, as $\bar{\mu}$-measurable functions over $C_F$, we have $\Phi_F(f) = 0$, $\bar{\mu}$-almost everywhere. Since $\Phi_F(f)$ is continuous as a function on $C_F$ by Theorem 2.2.3.4, then $\Phi_F(f) = 0$ holds everywhere on $C_F$.

(2) : If $f\in\ker(\Phi_{F,\omega})$, then $Z(f,c) = 0$ for every $c\in\Omega(C_F)(\omega)_{>1}$, since over this domain of the Riemann surface $\Omega(C_F)$, we have

$$
Z(f,c) = \int_{\mathbf{R}_{>0}}c(\tau(t))\Phi_{F,\omega}(f)(\tau(t))\,\frac{\mathrm{d}t}{t}
$$

and hence $Z(f,c) = 0$ everywhere over $\Omega(C_F)(\omega)-\{1, \lvert\cdot\rvert_F\}$ by the Identity Theorem, and hence everywhere over $\Omega(C_F)(\omega)$.

Conversely, if $Z(f,c) = 0$ for every $c\in\Omega(C_F)(\omega)$, then, since $c\lvert\cdot\rvert^{ix}_F\in\Omega(C_F)(\omega)$ for every $x\in\mathbf{R}$, Fourier Inversion implies that $c(\tau(t))\Phi_{F,\omega}(f)(\tau(t)) = 0$ as Schwartz (by Theorem 2.2.5.4(4)) functions of $t\in\mathbf{R}_{>0}$, and hence $\Phi_{F,\omega}(f) = 0$, since $c$ is smooth and nowhere vanishing over $C_F$, and hence so is its composition with any continuous $1$-parameter subgroup. $\square$

The following is an $S$-local analog of Lemma 5.1.2.1, characterizing the kernels of $\Phi_{F,S}$ and $\Phi_{F,S,\omega}$ in terms of the kernel of $Z_S$ from (5.1.1.2).

Lemma 5.1.2.2 (Kernels of $S$-local $\theta$-function and $Z$-function operators). *Let $F$ be a number field, $S$ a finite set of places containing all Archimedean places, $\omega\in\widehat{J^1_{F,S}}$ a continuous character. Let $Z_S : \mathcal{S}(\mathbf{A}_{F,S})\to\mathscr{M}(\Omega(J_{F,S}))$ be the $S$-Idelic Mellin transform operator from (5.1.1.2). Then:*

(1) *We have, as $\mathbf{C}$-linear subspaces of $\mathcal{S}(\mathbf{A}_{F,S})$:*

$$
\ker(Z_S) = \ker(\Phi_{F,S}). \tag{5.1.2.3}
$$

(2) *We have, as $\mathbf{C}$-linear subspaces of $\mathcal{S}(\mathbf{A}_{F,S})$:*

$$
\ker(\Phi_{F,S,\omega}) = \{f\in\mathcal{S}(\mathbf{A}_{F,S}) : Z_S(f,c)|_{\Omega(J_{F,S})(\omega)} = 0\}. \tag{5.1.2.4}
$$

Proof. (1) : Let $f\in\mathcal{S}(\mathbf{A}_{F,S})$ be a Schwartz-Bruhat function. If $\Phi_{F,S}(f) = 0$, then $Z_S(f,c) = 0$ for all $c\in\Omega(J_{F,S})_{>0}$, and hence $Z_S(f,c) = 0$ for every $c\in\Omega(J_{F,S})$ by the Identity Theorem.

Assume now $Z_S(f,c) = 0$ for all $c\in\Omega(J_{F,S})$. Over the domain $\Omega(J_{F,S})_{>0}$, the integral:

$$
Z_S(f,c) = \int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}f(g)c(g)\,\mathrm{d}\mu_S(g)
$$

is absolutely convergent and we may write it, by Theorem D.1.2.1, as:

$$
Z_S(f,c) = \int_{\mathbf{R}_{>0}}c(\tau(t))\Phi_{F,S,\omega}(f)(\tau(t))\,\frac{\mathrm{d}t}{t}
$$

for any choice of continuous homomorphic section $\tau$ to the $S$-idelic norm, and for any $c\in\Omega(C_{F,S})(\omega)_{>0}$ for each $\omega\in\widehat{J^1_{F,S}}$.

Since, for any $x\in\mathbf{R}$, we have $c\lvert\cdot\rvert^{ix}_F\in\Omega(J_{F,S})(\omega)_{>0}$ for any $c\in\Omega(C_{F,S})(\omega)_{>0}$, and $c(\tau(t))\Phi_{F,S,\omega}(f)(\tau(t))$ is a Schwartz function on $\mathbf{R}_{>0}$ for any $\omega\in\widehat{J^1_{F,S}}$ and $c\in\Omega(J_{F,S})(\omega)_{>1}$ (because

$$
(\log(t))^m c(\tau(t))\Phi_{F,S,\omega}(f)(\tau(t))
$$

is bounded as a function of $t\in\mathbf{R}_{>0}$ for every integer $m\ge 0$ by Proposition 2.3.1.4(2) and Corollary 2.4.3.2, as are all of its $(t\partial_t)$-derivatives of any order, by Proposition 2.3.2.2 upon replacing $f$ with $\partial_{\gamma_{\tau}}f$ using Lemma

## PDF page 226

**226** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC $Z$-FUNCTIONS**

2.3.2.1, for $\gamma_{\tau}$ the continuous $1$-parameter subgroup of $\mathrm{GL}_1(\mathbf{A}_{F,S})$ associated to $\tau$), then by Fourier Inversion we have $c(\tau(t))\Phi_{F,S,\omega}(f)(\tau(t)) = 0$ as continuous functions of $t\in\mathbf{R}_{>0}$ for every $\omega\in\widehat{J^1_{F,S}}$. By Lemma 4.3.2.2, we deduce that we have $c\,\Phi_{F,S}(f) = 0$, $\bar{\mu}_S$-almost everywhere over $J_{F,S}$. Since $c$ and $\Phi_{F,S}(f)$ are continuous functions on $J_{F,S}$, and since $c$ is nowhere vanishing over $J_{F,S}$, we deduce that we have $\Phi_{F,S}(f) = 0$ everywhere over $J_{F,S}$.

(2) : Let $f\in\mathcal{S}(\mathbf{A}_{F,S})$ be a Schwartz-Bruhat function. If $\Phi_{F,S,\omega}(f) = 0$, then $Z_S(f,c) = 0$ for all $c\in\Omega(J_{F,S})(\omega)_{>0}$, and hence $Z_S(f,c) = 0$ for every $c\in\Omega(J_{F,S})(\omega)$ by the Identity Theorem.

Conversely, assume $Z_S(f,c) = 0$ for all $c\in\Omega(J_{F,S})(\omega)$. Over the domain $\Omega(J_{F,S})(\omega)_{>0}$, the integral:

$$
Z_S(f,c) = \int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}f(g)c(g)\,\mathrm{d}\mu_S(g)
$$

is absolutely convergent and we may write it, by Theorem D.1.2.1, as:

$$
Z_S(f,c) = \int_{\mathbf{R}_{>0}}c(\tau(t))\Phi_{F,S,\omega}(f)(\tau(t))\,\frac{\mathrm{d}t}{t}
$$

for any choice of continuous homomorphic section $\tau$ to the $S$-idelic norm, and for any $c\in\Omega(C_{F,S})(\omega)_{>0}$.

Since, for any $x\in\mathbf{R}$, we have $c\lvert\cdot\rvert^{ix}_F\in\Omega(J_{F,S})(\omega)_{>0}$ for any $c\in\Omega(C_{F,S})(\omega)_{>0}$, and $c(\tau(t))\Phi_{F,S,\omega}(f)(\tau(t))$ is a Schwartz function on $\mathbf{R}_{>0}$ for any $\omega\in\widehat{J^1_{F,S}}$ and $c\in\Omega(J_{F,S})(\omega)_{>0}$, then by Fourier Inversion we have $c(\tau(t))\Phi_{F,S,\omega}(f)(\tau(t)) = 0$ as continuous functions of $t\in\mathbf{R}_{>0}$, and hence, since $c(\tau(t))$ is continuous and nowhere vanishing over $\mathbf{R}_{>0}$, we have $\Phi_{F,S,\omega}(f) = 0$. $\square$

**5.1.3. Continuity of the Mellin transform operators.** We recall that as a consequence of Theorem 3.2.2.1, the global Idelic $Z$-function operator $Z : \mathcal{S}(\mathbf{A}_F)\to\mathscr{M}(\Omega(C_F))$ from (5.1.1.1), which we also termed global Idelic Mellin transform, is valued in the linear subspace of the $\mathbf{C}$-vector space of meromorphic functions $\mathscr{M}(\Omega(C_F))$ on the Riemann surface $\Omega(C_F)$, of those meromorphic functions on $\Omega(C_F)$ whose divisor is bounded below by the divisor $D := -(1)-(\lvert\cdot\rvert_F)$ on $\Omega(C_F)$.

We call such linear subspace $\mathscr{M}(\Omega(C_F),D)$ and topologize it with the topology inherited from $\mathscr{H}(\Omega(C_F))$, the space of entire functions on $\Omega(C_F)$ topologized with the topology of uniform convergence on the compact subsets of $\Omega(C_F)$, under the linear bijection:

$$
\mathscr{M}(\Omega(C_F),D)\to\mathscr{H}(\Omega(C_F))
$$

defined by sending each meromorphic function in $\mathscr{M}(\Omega(C_F),D)$ to the entire function obtained by multiplication by the entire function which is constant and equal to $1$, on each connected component of $\Omega(C_F)$ other than $\Omega(C_F)(1)$, and, upon parametrizing $\Omega(C_F)(1)$ as $\{\lvert\cdot\rvert^s_F, s\in\mathbf{C}\}$, by $s(s-1)$.

This linear topology promotes $\mathscr{M}(\Omega(C_F),D)$ to a separable Fréchet space, by [Jar, Part I,Ch.5,§5.5,p.96] (separability being a consequence of countability of the dual group of $C^1_F$).

Similarly, as a consequence of Theorem 3.3.1.1, the $S$-Idelic $Z$-function operator $Z_S : \mathcal{S}(\mathbf{A}_{F,S}))\to\mathscr{M}(\Omega(J_{F,S}))$ from (5.1.1.2), which we also termed $S$-Idelic Mellin transform, is valued in the linear subspace of the $\mathbf{C}$-vector space $\mathscr{M}(\Omega(J_{F,S}))$ of meromorphic functions on $\Omega(J_{F,S})$, of those meromorphic functions whose divisor is bounded below by the divisor $D_S$ of the meromorphic function $L_S(c) := \prod_{v\in S}L_v(c_v)$, for $L_v(c_v)$ the local Euler factor at $v\in S$ of the Hecke $L$-function $L(c)$ of $F$.

Recall from (3.3.1.32) that $L_S(c)$ is related to the correcting factor $\rho_S(c)$ in the $S$-local functional equation of (3.3.1.2) from Theorem 3.3.1.1, by the identity of meromorphic functions on $\Omega(J_{F,S})$:

$$
\rho_S(c) = \epsilon_S(c)\frac{L_S(c)}{L_S(\widehat{c})}
$$

## PDF page 227

**5.1. THE TOPOLOGICAL VECTOR SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC $Z$-FUNCTIONS** · **227**

where $\epsilon_S(c)$ is the entire nowhere vanishing function defined in (3.3.1.28) of Lemma 3.3.1.7, and $1/L_S(\widehat{c})$ is entire, with zeros at the image of the poles of $L_S(c)$ under the self-map $\Omega(J_{F,S})\to\Omega(J_{F,S})$ assigned by $c\mapsto\widehat{c} := c^{-1}\lvert\cdot\rvert_F$.

We topologize $\mathscr{M}(\Omega(J_{F,S}),D_S)$ with the topology induced from the separable Fréchet space $\mathscr{H}(\Omega(J_{F,S}))$ of entire functions on $\Omega(J_{F,S})$, under the linear bijection $\mathscr{M}(\Omega(J_{F,S}),D_S)\to\mathscr{H}(\Omega(J_{F,S}))$ sending an element $\phi$ of $\mathscr{M}(\Omega(J_{F,S}),D_S)$ to $L_S(c)^{-1}\phi(c)$, an entire function over $\Omega(J_{F,S})$.

The topology on $\mathscr{H}(\Omega(J_{F,S}))$ is the topology of uniform convergence on compact subsets, which promotes $\mathscr{H}(\Omega(J_{F,S}))$ to a separable Fréchet space by [Jar, Part I,Ch.5,§5.5,p.96] (separability being a consequence of countability of the dual group of $J^1_{F,S}$).

The topologies described above on the spaces of meromorphic functions $\mathscr{M}(\Omega(C_F),D)$ and $\mathscr{M}(\Omega(J_{F,S}),D_S)$, respectively, agree with the topology termed Holdgrün topology in [GE, §3.1,p.290].

Indeed, the Hausdorff locally convex topologies defined on $\mathscr{M}(\Omega(C_F),D)$ and $\mathscr{M}(\Omega(J_{F,S}),D_S)$, promote each to a separable Fréchet space as a consequence of the Maximum Modulus Principle (see [Cnw-b, Ch.VI,§1,Thm.1.2,p.128]) and [Cnw-b, Ch.VII,§2,Thm.2.1,p.151], and the Holdgrün topology also promotes each of the two linear spaces $\mathscr{M}(\Omega(C_F),D)$ and $\mathscr{M}(\Omega(J_{F,S}),D_S)$ to Fréchet spaces (see [GE, §2.2,p.290] applied to $\Omega=\Omega(G)(\omega)\cup\{\infty\}$ for $G=C_F$, $G=J_{F,S}$, respectively, and for each continuous character of $G^1$, upon choosing a holomorphic parametrization $\{\chi\lvert\cdot\rvert^s_G, s\in\mathbf{C}\}$ for each, with $\delta(\infty)=0$ and $\delta : \Omega-\{\infty\}\to\mathbf{N}$ supported on a countable discrete subset of the complex $s$-plane; see also [Kothe-I, Ch.6,§27,(3),p.373]).

By [NB, Thm.14.5.1] (noting that Fréchet spaces are Baire), the identity on $\mathscr{M}(\Omega(C_F),D)$ and $\mathscr{M}(\Omega(J_{F,S}),D_S)$, which is continuous with respect to the Höldgrun topology on the source, and the topology from the foregoing, on the target, is a linear topological isomorphism.

We further refer the reader to [GE] for more on Hausdorff locally convex topologies on the space of meromorphic functions on a complex domain, and how the respective induced topologies on the linear subspaces of meromorphic functions with prescribed location and order of poles, relate (and to [GE, Appendix,p.301] for an account on the problem of topologizing the linear space of meromorphic functions on a complex domain, with unconstrained divisor of poles).

Lemma 5.1.3.1 (Meromorphic compact convergence continuity of the Idelic Mellin transforms). *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places.*

(1) *The global Idelic Mellin transform operator $Z : \mathcal{S}(\mathbf{A}_F)\to\mathscr{M}(\Omega(C_F),D)$ from (5.1.1.1) is continuous with respect to the Hausdorff locally convex topology of $\mathcal{S}(\mathbf{A}_F)$ on the source, and the topology of uniform convergence on the compact subsets of $\Omega(C_F)-\{1, \lvert\cdot\rvert_F\}$ on the target. It satisfies, for every $g\in\mathrm{GL}_1(\mathbf{A}_F)$, the following identity:*

$$
Z(\rho_F(g,\cdot),c) = c(g)Z(\cdot,c) \tag{5.1.3.1}
$$

*as continuous linear operators on $\mathcal{S}(\mathbf{A}_F)$, where $\rho_F : \mathrm{GL}_1(\mathbf{A}_F)\times\mathcal{S}(\mathbf{A}_F)\to\mathcal{S}(\mathbf{A}_F)$ is the continuous left-translation action of $\mathrm{GL}_1(\mathbf{A}_F)$.*

(2) *The $S$-local Idelic Mellin transform operator $Z_S : \mathcal{S}(\mathbf{A}_{F,S})\to\mathscr{M}(\Omega(J_{F,S}),D_S)$ (5.1.1.2) is continuous with respect to the Hausdorff locally convex topology of $\mathcal{S}(\mathbf{A}_F)$ on the source, and the topology of uniform convergence on the compact subsets of $\Omega(J_{F,S})-D_S$ on the target, where $D_S$ is the divisor on $\Omega(J_{F,S})$ of the meromorphic function $\rho_S(c)$ on $\Omega(J_{F,S})$ defined in (3.3.1.3). It satisfies, for every $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$, the following identity:*

$$
Z_S(\rho_{F,S}(g,\cdot),c) = c(g)Z_S(\cdot,c) \tag{5.1.3.2}
$$

*as continuous linear operators on $\mathcal{S}(\mathbf{A}_{F,S})$, where $\rho_{F,S} : \mathrm{GL}_1(\mathbf{A}_{F,S})\times\mathcal{S}(\mathbf{A}_{F,S})\to\mathcal{S}(\mathbf{A}_{F,S})$ is the continuous left-translation action of $\mathrm{GL}_1(\mathbf{A}_{F,S})$.*

## PDF page 228

**228** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC $Z$-FUNCTIONS**

Proof. Throughout this argument, for $G$ a Hausdorff locally compact abelian group which is chosen to be either $\mathrm{GL}_1(\mathbf{A}_F)$, $C_F$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, respectively $J_{F,S}$, we denote, upon writing $\lvert\cdot\rvert_G$ for either the idelic, or $S$-idelic norm, $G^I$, for $I\subset\mathbf{R}_{>0}$ a connected interval with non-empty interior, for the subset $G^I := \{g\in G : \lvert g\rvert_G\in I\}$.

We write $G^{>a}$ if $I = (a,+\infty)$ for a real number $a\in\mathbf{R}_{>0}$.

(1) : We choose $\chi\in\widehat{C_F}$ and parametrize $\Omega(C_F)(\chi)$ as $c = \chi\lvert\cdot\rvert^s_F$, $s\in\mathbf{C}$.

If $\chi|_{C^1_F}$ is trivial, then $\chi = \lvert\cdot\rvert^{ix_0}_F$ for a unique real number $x_0$, and we have

$$
Z(f,c) = \int_{\mathrm{GL}_1(\mathbf{A}_F)^{>1}}f(g)\chi(g)\lvert g\rvert^s_F\,\mathrm{d}\mu(g)+\int_{\mathrm{GL}_1(\mathbf{A}_F)^{>1}}\widehat{f}(g)\overline{\chi}(g)\lvert g\rvert^{1-s}_F\,\mathrm{d}\mu(g)+\delta_{\chi|_{C^1_F}}\bar{\mu}_1(C^1_F)\left\{\frac{\widehat{f}(0)}{s-ix_0-1}-\frac{f(0)}{s-ix_0}\right\} \tag{5.1.3.3}
$$

by [CF, Ch.XV,Thm.4.2.1] and the proof of [CF, Ch.XV,Thm.4.4.1], where $\delta_{\chi|_{C^1_F}} = 0$ if $\chi|_{C^1_F}\ne 1$, and $\delta_{\chi|_{C^1_F}}\ne 0$ if $\chi|_{C^1_F} = 1$.

Formation of $f(0)$ and $\widehat{f}(0)$ is linear and continuous on $\mathcal{S}(\mathbf{A}_F)$, since the former is the tempered distribution $\delta_0$ and the latter is $\widehat{\delta}_0$, its adelic Fourier transform, and the adelic Fourier transform is a linear topological automorphism of $\mathcal{S}(\mathbf{A}_F)$.

By Dominated Convergence, formation of the two integrals in (5.1.3.3) is sequentially continuous on $\mathcal{S}(\mathbf{A}_F)$, uniformly on the compact subsets of $\Omega(C_F)-\{1, \lvert\cdot\rvert_F\}$. To see this, we proceed as follows, using Theorem 2.2.5.4(6).

Let $K\subset\mathbf{C}$ be a compact subset with non-empty interior.

Let $f\in\mathcal{S}(\mathbf{A}_F)$, and $\{f_m\}_{m\ge 0}\subset\mathcal{S}(\mathbf{A}_F)$ a sequence converging to $f$ in $\mathcal{S}(\mathbf{A}_{F,S})$. Then $\mathcal{B} := \{f_m\}_{m\ge 0}$ is a bounded subset of $\mathcal{S}(\mathbf{A}_F)$.

We let $N > 0$ be a fixed integer satisfying $N-1 > \max\{\lvert\mathrm{Re}(s)\rvert, \lvert 1-\mathrm{Re}(s)\rvert, s\in K\}$.

By Theorem 2.2.3.4(4), there exist real numbers $C_{\mathcal{B},N}, T_{\mathcal{B},N} > 0$ such that for all $g\in C_F$ satisfying $\lvert g\rvert_F > T_{\mathcal{B},N}$, then:

$$
\lvert\Phi_F(u)(g)\rvert\le C_{\mathcal{B},N}\lvert g\rvert^{-N}_F \tag{5.1.3.4}
$$

for all $u\in\mathcal{B}$. By Theorem 2.2.3.4(6), $T_{\mathcal{B},N}$ can be chosen to be $T_{\mathcal{B},N} = 1$ at the cost of replacing $C_{\mathcal{B},N}$ with a larger constant, still uniform over $\mathcal{B}$.

For each $u\in\mathcal{S}(\mathbf{A}_F)$, we have, by Theorem D.1.2.1, uniformly with respect to $c$ varying over the vertical strips of bounded width of the connected components of $\Omega(C_F)$:

$$
\int_{\mathrm{GL}_1(\mathbf{A}_F)^{>1}}u(g)c(g)\,\mathrm{d}\mu(g) = \int_{C_F^{>1}}\Phi_F(u)(g)c(g)\,\mathrm{d}\bar{\mu}(g). \tag{5.1.3.5}
$$

We therefore have, for every integer $m\ge 0$:

$$
\int_{\mathrm{GL}_1(\mathbf{A}_F)^{>1}}f_m(g)\chi(g)\lvert g\rvert^s_F\,\mathrm{d}\mu(g) = \int_{C_F^{>1}}\Phi_F(f_m)(g)\chi(g)\lvert g\rvert^s_F\,\mathrm{d}\bar{\mu}(g) \tag{5.1.3.6}
$$

where the integral in the right side of (5.1.3.6) converges to $\int_{C_F^{>1}}\Phi_F(f)(g)\chi(g)\lvert g\rvert^s_F\,\mathrm{d}\bar{\mu}(g)$ by Dominated Convergence, applied to the sequence $\mathcal{B}$ using $C_{\mathcal{B},N}\lvert g\rvert^{-N}_F$ as majorant by (5.1.3.4), uniformly over $K$.

Another application of Theorem D.1.2.1 gives the sequential continuity of the formation of the first of the two integrals in the right side of (5.1.3.3). The same argument, and the same constant $C_{\mathcal{B},N}$, apply to the image of $\mathcal{B}$ under the Fourier transform (which is again a bounded subset of $\mathcal{S}(\mathbf{A}_F)$ since the Fourier transform is a linear topological automorphism of $\mathcal{S}(\mathbf{A}_F)$), proving the sequential continuity of the second of the two integrals from (5.1.3.3).

It follows that the operator $Z(\cdot,c) : \mathcal{S}(\mathbf{A}_F)\to\mathscr{M}(\Omega(C_F))$ is sequentially continuous.

Since $\mathcal{S}(\mathbf{A}_F)$ is Hausdorff complete and a locally convex inductive limit of Fréchet spaces by Proposition 2.1.3.2(1), it is bornological by [Scha, Ch.II,§8,Cor.1,p.62], and by [NB, Thm.13.2.12] it is ultrabornological.

## PDF page 229

**5.1. THE TOPOLOGICAL VECTOR SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC $Z$-FUNCTIONS** · **229**

The Hausdorff locally convex topological $\mathbf{C}$-vector space $\mathscr{M}(\Omega(C_F),D)$ is a Fréchet space, topologized in the manner discussed in the prelude to the Lemma.

In particular, it is webbed by [NB, Thm.14.6.2]. It follows that by [NB, Thm.14.7.3] the operator $Z(\cdot,c)$ is continuous (see also [Jar, Part I,Ch.5,§5.4,Thm.2,p.94], noting that Fréchet spaces are Baire, by [Jar, Part I,Ch.5,§5.1,Thm.1,p.87]).

The identity in (5.1.3.1) is a consequence of invariance of the Haar measure $\mu$ on $\mathrm{GL}_1(\mathbf{A}_F)$ for $c\in\Omega(C_F)_{>1}$, and it holds for all $c\in\Omega(C_F)$ by analytic continuation.

(2) : For every $c\in\Omega(J_{F,S})_{>0}$, the function $Z_S(f,c)$ is given by:

$$
Z_S(f,c) = \int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}f(g)c(g)\,\mathrm{d}\mu_S(g) = \int_{J_{F,S}}\Phi_{F,S}(f)(g)c(g)\,\mathrm{d}\bar{\mu}_S(g) \tag{5.1.3.7}
$$

where the second identity holds over $\Omega(J_{F,S})_{>0}$ by Theorem D.1.2.1, uniformly as $c$ varies over the compact subsets of $\Omega(J_{F,S})_{>0}$.

By Dominated Convergence, formation of the rightmost integral in (5.1.3.7) is sequentially continuous on $\mathcal{S}(\mathbf{A}_{F,S})$, uniformly on the compact subsets of $\Omega(J_{F,S})_{>0}$.

To see this, we proceed as in (1), upon using Theorem 2.3.1.2(4) in the same role as Theorem 2.2.3.4(6) in the proof of (1).

It follows that the linear operator $Z_S(\cdot,c) : \mathcal{S}(\mathbf{A}_{F,S})\to\mathscr{H}(\Omega(J_{F,S})_{>0})$ is sequentially continuous, upon endowing the target with the topology of uniform convergence on the compact subsets of $\Omega(J_{F,S})_{>0}$.

Since $\mathcal{S}(\mathbf{A}_{F,S})$ is Hausdorff complete and a locally convex inductive limit of Fréchet spaces by Lemma 2.1.4.1, it is bornological by [Scha, Ch.II,§8,Cor.1,p.62], and by [NB, Thm.13.2.12] it is ultrabornological.

The complex vector space $\mathscr{H}(\Omega(J_{F,S})_{>0})$ of holomorphic functions over $\Omega(J_{F,S})_{>0}$, equipped with the topology of uniform convergence on the compact subsets of $\Omega(J_{F,S})_{>0}$ is a Fréchet space. In particular, it is webbed by [NB, Thm.14.6.2].

It follows that by [NB, Thm.14.7.3] the operator $Z_S : \mathcal{S}(\mathbf{A}_{F,S})\to\mathscr{H}(\Omega(J_{F,S})_{>0})$ is continuous.

By the functional equation from (3.3.1.2) of Theorem 3.3.1.1, $Z_S$ is continuous as an operator $Z_S : \mathcal{S}(\mathbf{A}_{F,S})\to\mathscr{M}(\Omega(J_{F,S}),D_S)$.

The identity in (5.1.3.2) is a consequence of invariance of the Haar measure $\mu_S$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})$ for $c\in\Omega(J_{F,S})_{>0}$, and it follows for all $c\in\Omega(J_{F,S})$ away from the poles of $L_S(c)$, by analytic continuation. $\square$

We now prove Theorem 5.1.1.3. Recall that the Theorem asserts that the kernels $\ker(\Phi_F)$, $\ker(\Phi_{F,S})$ of the adelic $\theta$-function operators and their homogeneous counterparts $\Phi_{F,\omega}$, $\Phi_{F,S,\omega}$, for continuous characters $\omega\in\widehat{C^1_F}$, respectively $\omega\in\widehat{J^1_{F,S}}$, are closed subspaces of $\mathcal{S}(\mathbf{A}_F)$, respectively $\mathcal{S}(\mathbf{A}_{F,S})$, which implies that the Hausdorff locally convex quotient topologies on the spaces of global, respectively $S$-local, adelic $\theta$-functions $\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}(\mathbf{A}_F))$ and $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$ are Hausdorff.

Proof of Theorem 5.1.1.3. (1) : Since, by Lemma 5.1.3.1(1), $Z$ is continuous as a linear operator $\mathcal{S}(\mathbf{A}_F)\to\mathscr{M}(\Omega(C_F),D)$, its kernel is closed. By Lemma 5.1.2.1, $\ker(\Phi_F) = \ker(Z)$ is closed as a linear subspace of $\mathcal{S}(\mathbf{A}_F)$. Similarly, by Lemma 5.1.3.1(2), $Z_S$ is continuous as a linear operator $\mathcal{S}(\mathbf{A}_{F,S})\to\mathscr{M}(\Omega(J_{F,S}),D_S)$, and hence its kernel is closed. By Lemma 5.1.2.2, $\ker(\Phi_{F,S}) = \ker(Z_S)$ is closed.

(2) : Let $\omega\in\widehat{C^1_F}$ be a continuous character. Then upon calling $j_{\omega} : \Omega(C_F)(\omega)\to\Omega(C_F)$ the open immersion, we have, by Lemma 5.1.2.1(2), $\ker(\Phi_{F,\omega}) = \ker(j_{\omega}^{*}Z)$, and since the image of $j_{\omega}$ is closed in $\Omega(C_F)$, the linear operator $j_{\omega}^{*}Z : \mathcal{S}(\mathbf{A}_F)\to\mathscr{M}(\Omega(C_F),D)(\omega))$ is continuous, and hence its kernel is closed.

(3) : Let $\omega\in\widehat{J^1_{F,S}}$ be a continuous character. Then upon calling $j_{\omega} : \Omega(J_{F,S})(\omega)\to\Omega(J_{F,S})$ the open immersion, we have, by Lemma 5.1.2.2(2), $\ker(\Phi_{F,S,\omega}) = \ker(j_{\omega}^{*}Z_S)$, and since the image of $j_{\omega}$ is closed in $\Omega(J_{F,S})$, the linear operator $j_{\omega}^{*}Z_S : \mathcal{S}(\mathbf{A}_{F,S})\to\mathscr{M}(\Omega(J_{F,S}),D_S)(\omega))$ is continuous, and hence its kernel is closed. $\square$

## PDF page 230

**230** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

$^1$

**5.2. Structure Theorem I: topology of the spaces of adelic $\theta$-functions**

In this section we use the results proved in Lemma 5.1.3.1, Lemma 5.1.2.1 and Lemma 5.1.2.2, to establish the first structural result on the Hausdorff locally convex topology of the spaces of adelic $\theta$-functions

$$
\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)),\quad \mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})).
$$

**5.2.1. Topology of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ and $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$.** We recall from Definition 5.1.1.1, that we defined, for a number field $F$ and for $S$ a finite set of places of $F$ containing all the Archimedean places, the spaces of Adelic (both $S$-local and global) $\theta$-functions $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ as the quotients:

$$
\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})):=\mathcal S(\mathbf A_{F,S})/\ker(\Phi_{F,S}),\quad \mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)):=\mathcal S(\mathbf A_F)/\ker(\Phi_F)
$$

where $\Phi_{F,S}$ and $\Phi_F$ are the $\theta$-function operators from Definition 2.2.3.1 and Definition 2.3.1.1.

We proved in Theorem 5.1.1.3 that their kernels are closed in $\mathcal S(\mathbf A_{F,S})$, respectively $\mathcal S(\mathbf A_F)$, and so we know that the quotient topology on the spaces of adelic $\theta$-functions is Hausdorff.

The following is the main result on the topology of the spaces of adelic $\theta$-functions:

THEOREM 5.2.1.1 (Structure Theorem I - topology of the spaces of adelic $\theta$-functions). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places.*

*(1) The Hausdorff locally convex topological vector spaces*

$$
\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)),\quad \mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))
$$

*are locally convex strict inductive limits of nuclear Fréchet spaces, hence strict LF-spaces. They are complete, nuclear and Montel. Their strong duals are complete, nuclear and Montel.*

*(2) For $S'$ a finite set of places of $F$ containing $S$, the continuous linear operator $\pi_{S,S'}$ from (2.1.4.3) induces a unique continuous linear map:*

$$
\bar\pi_{S,S'}:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'})) \tag{5.2.1.1}
$$

*compatible with enlargement of the finite set of places $S\subset S'$, and which is a linear topological embedding. The inductive system $\{\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\}_{S\subset\Sigma_F}$ is strict, and the inductive limit locally convex topological vector space admits a unique continuous linear map:*

$$
\bar\pi:\operatorname*{\mathrm{colim}}_{S\subset\Sigma_F}\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)) \tag{5.2.1.2}
$$

*which is a linear topological isomorphism, compatible with the continuous actions of $C_{F,S}$ on the source, through its quotient $J_{F,S}$, and as an open subgroup of $C_F$ on the target, for each $S\subset\Sigma_F$ containing $S_\infty$.*

*(3) Upon calling, for each finite set $S$ of places of $F$ containing $S_\infty$:*

$$
\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)) \tag{5.2.1.3}
$$

*the canonical continuous insertion operator induced by the linear topological isomorphism from (5.2.1.2), $\bar\pi_S$ is a linear topological embedding, compatible with the continuous action of $C_{F,S}$ on the source, through its quotient $J_{F,S}$, and as an open subgroup of $C_F$ on the target.*

We will be proving the Theorem only at the end of this Chapter. This subsection is devoted to stating the Theorem and its analog for the isotypes of the continuous left-translation actions of $J^1_{F,S}$ and $C^1_F$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ respectively, for then establishing some initial properties and discussing a few reductions.

---
$^1$Include version with $I$-exponentially decaying target.

## PDF page 231

**5.2. STRUCTURE THEOREM I: TOPOLOGY OF THE SPACES OF ADELIC $\theta$-FUNCTIONS** · **231**

$^2$

PROOF. (1) : By Theorem 5.1.1.3, the $\mathbf C$-linear spaces $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ and $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, endowed with the quotient topology, are Hausdorff and locally convex, since the kernel of the surjective linear operators $\Phi_F:\mathcal S(\mathbf A_F)\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ and $\Phi_{F,S}:\mathcal S(\mathbf A_{F,S})\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ are closed.

Since $\mathcal S(\mathbf A_F)$ is Hausdorff complete and a strict locally convex inductive limit of a sequence of nuclear Fréchet spaces (see Proposition 2.1.3.2), and the quotient of a Fréchet space by a closed subspace is a Fréchet space by [Scha, Ch.I,6.3,p.31], $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ is the locally convex inductive limit of a sequence nuclear Fréchet spaces. By [Scha, Ch.II,6.6], it is complete. By the same token, so is $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ (see Proposition 2.1.4.1).

By [Scha, Ch.III,Thm.7.4,p.103], they inherit nuclearity. By [Scha, Ch.II,§8,Cor.1,p.61] they are barrelled, and since they are complete and nuclear, they are both Montel spaces by [Scha, Ch.III,§7,Cor.2,p.101].

Since $\mathcal S(\mathbf A_F)$ is Hausdorff complete and a locally convex inductive limit of nuclear Fréchet spaces by Proposition 2.1.3.2(1), it is bornological by [Scha, Ch.II,§8,Cor.1,p.62].

Similarly, since $\mathcal S(\mathbf A_{F,S})$ is Hausdorff complete and a locally convex inductive limit of nuclear Fréchet spaces by Proposition 2.1.4.1, it is bornological by [Scha, Ch.II,§8,Cor.1,p.62]. By [Scha, Ch.IV,§6,6.1], their strong duals are Hausdorff and complete.

By [Scha, Ch.IV,5.9,p.147], they are Montel (see also [MV, Part IV,Ch.24,Thm.24.25,p.286]). Since $\Phi_F:\mathcal S(\mathbf A_F)\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ is a quotient map, the adjoint linear map:

$$
\Phi'_F:\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta\to\mathcal S(\mathbf A_F)'_\beta \tag{5.2.1.4}
$$

is continuous by [NB, Thm.8.11.3(d)], injective by [NB, Thm.8.10.6(e)], and a linear topological embedding by [NB, Thm.8.13.5] applied to $A=\Phi'_F$, combined with [NB, Thm.8.13.4] applied to $A=\Phi_F$, which is open, being a quotient map, and with [NB, Thm.8.13.2] applied to $A=\Phi_F$, which implies that $\Phi'_F$ is weakly relatively open.

Since $\mathcal S(\mathbf A_F)'_\beta$ is nuclear by Proposition 2.1.3.2(2), so is $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta$ by [Scha, Ch.III,§7,Thm.7.4,p.103]. A similar argument shows that $\mathcal S(\mathbf A_{F,S})'_\beta$ is nuclear.

(2) and (3) follow from Proposition 2.1.4.1: indeed, upon writing $\mathcal S(\mathbf A_F)$ as $\operatorname*{\mathrm{colim}}_{S\subset\Sigma_F}\mathcal S(\mathbf A_{F,S})$ the index set being the set of the finite subsets $S\subset\Sigma_F$ containing $S_\infty$, the transition operators being the $\pi_{S,S'}$ from (2.1.4.12), the inductive limit is strict by Lemma 2.1.4.3 and the pre-image of the closed subspace $\ker(\Phi_F)$ under $\pi_S$ is closed in $\mathcal S(\mathbf A_{F,S})$.

Such closed subspace agrees with $\ker(\Phi_{F,S})$. To see this, it is enough to show that it agrees with $\ker(Z_S)$ by Lemma 5.1.2.2. Since by Theorem 3.4.1.1 we have $Z(\pi_S(f_S),c)=Z_S(f_S,\psi_{F,S}(c))L_{\Sigma_F-S}(\chi,s)$ for $c=\chi|\cdot|^s_F$ unramified outside of $S$, then by Lemma 3.1.2.2(1), which applies since $c$ is in the open subset $\Omega_S(C_F)(\chi)$, then $f_S\in\ker(\Phi_{F,S})$ if and only if $\pi_S(f_S)\in\ker(\Phi_F)$, which proves that we have $\pi_S^{-1}(\ker(\Phi_F))=\ker(\Phi_{F,S})$. This identity holds as subspaces of $\mathcal S(\mathbf A_{F,S})$.

The induced operator $\bar\pi_{S,S'}:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$ for any inclusion $S\subset S'$ is therefore injective, linear and continuous by functoriality of the quotient topology, and it induces on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ the subspace topology. To see this, we observe that we have $\bar\Pi_S(\ker(\Phi_F))=\ker(\Phi_F)\cap\pi_S(\mathcal S(\mathbf A_{F,S}))=\pi_S(\ker(\Phi_{F,S}))\subset\ker(\Phi_F)$, and so $\bar\Pi_S$ descends to a unique continuous linear operator $\bar\Pi_S:\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ whose range is the image in $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ of $\pi_S(\mathcal S(\mathbf A_{F,S}))$, i.e. $\bar\pi_S(\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})))$, which is the identity on $\bar\pi_S(\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})))$, and satisfies $\bar\Pi_S^2=\bar\Pi_S$ on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$. This proves (3), and it shows that $\bar\pi_S(\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})))$ is a closed subspace of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$. As such, $\bar\pi_S$ is a continuous linear bijection onto its image, with closed range, and hence a linear topological embedding. Since it factors through $\bar\pi_{S,S'}$ and $\bar\pi_{S'}$, this latter being a linear

---
$^2$WORK 1: adjust this Theorem.

## PDF page 232

**232** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

topological embedding by the same token, then the range of $\bar\pi_{S,S'}$, which is $\bar\pi_{S'}^{-1}(\bar\Pi_{S'}(\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))))$, is closed in $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$, and $\bar\pi_{S,S'}$ is a continuous linear bijection onto its image, with closed range, hence a linear topological embedding. This proves (2).

The same argument as in Corollary 2.1.4.4 shows that the net $\{\bar\Pi_S\}_{S\subset\Sigma_F}$ indexed by the set of finite subsets of $\Sigma_F$ containing $S_\infty$, filtered by inclusion, converges uniformly on the bounded subsets of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ to the identity. $\square$

**5.2.2. Isotypes of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ and $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$.** $^3$

From the discussion in §3.1.1 we have

$$
\Omega(C_F)=\coprod_{\omega\in\widehat{C^1_F}}\Omega(C_F)(\omega),\quad \Omega(J_{F,S})=\coprod_{\omega\in\widehat{J^1_{F,S}}}\Omega(J_{F,S})(\omega) \tag{5.2.2.1}
$$

where $\Omega(C_F)(\omega)$, respectively $\Omega(J_{F,S})(\omega)$, are defined in §3.1.1 and are bi-holomorphic to the complex plane upon choosing an idelic, respectively $S$-idelic quasi-character $c_0$ such that $c_0|_{C^1_F}=\omega$, respectively $c_0|_{J^1_{F,S}}=\omega$, to write any point in $\Omega(C_F)(\omega)$, respectively $\Omega(J_{F,S})(\omega)$, as $c=c_0|\cdot|^s_F$, respectively $c=c_0|\cdot|^s_{F,S}$, for a unique complex number $s$.

The decomposition of $\Omega(C_F)$ and $\Omega(J_{F,S})$ from (5.2.2.1) into connected components induces a $\mathbf C$-linear product decomposition:

$$
\mathscr M(\Omega(C_F))=\prod_{\omega\in\widehat{C^1_F}}\mathscr M(\Omega(C_F)(\omega)),\quad \mathscr M(\Omega(J_{F,S}))=\prod_{\omega\in\widehat{J^1_{F,S}}}\mathscr M(\Omega(J_{F,S})(\omega)). \tag{5.2.2.2}
$$

Recall that we have defined (see (5.1.1.1) from Definition 5.1.1.4) $\mathscr M(\Omega(C_F))$ to be the $\mathbf C$-linear space of all meromorphic functions on $\Omega(C_F)$ whose only poles are at most of order $1$ and are contained within the subset $\{1,|\cdot|_F\}$, and $\mathscr M(\Omega(J_{F,S}))$ to be the $\mathbf C$-linear space of all meromorphic functions whose only poles $c\in\Omega(J_{F,S})$ are contained in the set $\mathcal U_S$ of the poles of the meromorphic function $\rho_S(c)$ from (3.3.1.3), and such that the order of pole of $c$ is at most $\mathrm{ord}_{c'=c}\,\rho_S(c')$.

We have endowed in Lemma 5.1.3.1 the linear spaces $\mathscr M(\Omega(C_F))$ and $\mathscr M(\Omega(J_{F,S}))$ with the topology of uniform convergence on compact subsets of $\Omega(C_F)-\{1,|\cdot|_F\}$ and $\Omega(J_{F,S})-\mathcal U_S$. We will retain this choice of topology on $\mathscr M(\Omega(C_F))$ and $\mathscr M(\Omega(J_{F,S}))$ throughout this subsection.

DEFINITION 5.2.2.1. Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places.

We define:

(1) For each $\omega\in\widehat{C^1_F}$, the complex vector space of continuous co-invariants of the continuous representation $\omega$ of $C^1_F$ on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$:

$$
\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)):=\mathcal S(\mathbf A_F)/\ker(\Phi_{F,\omega}) \tag{5.2.2.3}
$$

(2) For each $\omega\in\widehat{J^1_{F,S}}$, the complex vector space of continuous co-invariants of the continuous representation $\omega$ of $J^1_{F,S}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$:

$$
\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})):=\mathcal S(\mathbf A_{F,S})/\ker(\Phi_{F,S,\omega}). \tag{5.2.2.4}
$$

We note that the continuous co-invariants $\mathrm H_{0,\mathrm{cont}}(\omega,\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)))$ of the continuous representation $\omega$ of $C^1_F$, respectively $C^1_{F,S}$, on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, respectively $\mathrm H_{0,\mathrm{cont}}(\omega,\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})))$, are obtained as the quotient of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, respectively $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, by the closure of the $\mathbf C$-linear subspace $\mathbf C$-linearly generated by the elements $\{\phi(x)-\bar\omega(g)\phi(g^{-1}x),\,g\in C^1_F,\,\phi\in\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\}$, respectively $\{\phi(x)-\bar\omega(g)\phi(g^{-1}x),\,g\in C^1_{F,S},\,\phi\in\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\}$.

---
$^3$WORK 2: adjust this introduction.

## PDF page 233

**5.2. STRUCTURE THEOREM I: TOPOLOGY OF THE SPACES OF ADELIC $\theta$-FUNCTIONS** · **233**

This is a consequence of Lemma 4.3.3.1. Such description of the kernels of $\Phi_{F,S}$ and $\Phi_{F,S,\omega}$ and their global analog will be provided in Remark 5.2.3.4 at the end of this section.

**5.2.3. First Structure Theorem on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$, $\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$.** $^4$

THEOREM 5.2.3.1 (First Structure Theorem - isotypes). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places. Let $\omega\in\widehat{C^1_F}$ be a continuous character, unramified outside $S$, and let $\omega_S$ be the unique continuous character induced by $\omega|_{C^1_{F,S}}$ to $J^1_{F,S}$ under the quotient homomorphism $C_{F,S}\to J_{F,S}$.*

*(1) For $S'$ a finite set of places of $F$ containing $S$, the continuous linear operator $\pi_{S,S'}$ from (5.2.1.1) induces a unique continuous linear map:*

$$
\bar\pi_{S,S'}:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega_{S'},\mathcal S(\mathbf A_{F,S'})) \tag{5.2.3.1}
$$

*compatible with enlargement of the finite set of places $S'$, and which is a linear topological embedding, compatible with the continuous actions of $C_{F,S}$ on the source, through its quotient $J_{F,S}$, and on target through the continuous homomorphism $C_{F,S}\to C_{F,S'}$. The inductive system $\{\mathrm H_{0,\mathrm{cont}}(\omega_{S'},\mathcal S(\mathbf A_{F,S'}))\}_{S\subset S'\subset\Sigma_F}$ is strict, and the inductive limit locally convex topological vector space admits a unique continuous linear map:*

$$
\bar\pi:\operatorname*{\mathrm{colim}}_{S\subset\Sigma_F}\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)) \tag{5.2.3.2}
$$

*which is a linear topological isomorphism.*

*(2) The Hausdorff locally convex topological vector spaces $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ and $\mathrm H_{0,\mathrm{cont}}(\omega_{S'},\mathcal S(\mathbf A_{F,S'}))$, for each finite set of places $S'$ of $F$ containing $S$, are locally convex inductive limits of nuclear Fréchet spaces, and hence LF-spaces. They are complete, nuclear, Montel spaces. Their strong duals are complete nuclear and Montel.*

*(3) Upon calling, for each $S'$ finite set of places of $F$ containing $S$, $\bar\pi_{S'}$ the canonical continuous insertion operator induced by the linear topological isomorphism from (5.2.3.2), there exists a continuous linear operator*

$$
\bar\Pi_{S'}:\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)) \tag{5.2.3.3}
$$

*whose image is $\bar\pi_{S'}(\mathrm H_{0,\mathrm{cont}}(\omega_{S'},\mathcal S(\mathbf A_{F,S'})))$, which is the identity on $\bar\pi_{S'}(\mathrm H_{0,\mathrm{cont}}(\omega_{S'},\mathcal S(\mathbf A_{F,S'})))$, and satisfies $\bar\Pi_{S'}^2=\bar\Pi_{S'}$. The net $\{\bar\Pi_{S'}\}_{S\subset S'\subset\Sigma_F}$ indexed by the finite subsets $S'\subset\Sigma_F$ containing $S$, converges to the identity on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ in $\mathscr L_\beta(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)))$, i.e. with respect to the topology of uniform convergence on the bounded subsets of $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$.*

PROOF. (1) : The continuous linear operator $\bar\pi_{S,S'}$ from (5.2.1.1) is compatible with the action of $C_{F,S}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ on the source, which is through the quotient $J_{F,S}$, and $C_{F,S'}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$ on the target, where $C_{F,S}$ acts on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$ through the continuous injective homomorphism $C_{F,S}\to C_{F,S'}$ induced by $\mathrm{GL}_1(\mathbf A_{F,S})\times\prod_{v\in S'-S}\mathcal O_{F_v}^\times\to\mathrm{GL}_1(\mathbf A_{F,S'})$, which is in turn defined by sending an $S$-idele to the $S'$-idele whose $S$-indexed components are unchanged, and the $(S'-S)$-indexed components are all $1$. Since $\omega_S$ and $\omega_{S'}$ are each the restriction to $C^1_{F,S}$, respectively $C^1_{F,S'}$, descended to $J^1_{F,S}$, respectively $J^1_{F,S'}$, of a continuous character $\omega\in\widehat{C^1_F}$, then if $f\in\ker(\Phi_{F,S,\omega_S})$, we also have $\pi_{S,S'}(f)\in\ker(\Phi_{F,S',\omega_{S'}})$. Indeed, by Lemma 5.1.2.2, we have $Z_S(f,c)=0$ for all $c\in\Omega(J_{F,S})(\omega_S)$, and

$$
L_{S'}(\pi_{S,S'}(f),c)=Z_S(f,c)\prod_{v\in S'-S}(1-c(\pi_v))^{-1} \tag{5.2.3.4}
$$

for all $c\in\Omega(J_{F,S'})(\omega_{S'})$ (noting that every $c\in\Omega(J_{F,S'})(\omega_{S'})$ is unramified outside $S$). In the identity in (5.2.3.4), $Z_S(f,c)$ is $Z_S(f,c')$ evaluated at the quasi-character $c'$ obtained by lifting $c$ to $C_{F,S'}$ along the

---
$^4$WORK 3: adjust this Theorem.

## PDF page 234

**234** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

continuous quotient homomorphism $C_{F,S'}\to J_{F,S'}$, restricting it to $C_{F,S}$ along the continuous homomorphism $C_{F,S}\to C_{F,S'}$, and, being such restriction unramified outside $S$, since $c$ is, factoring it through the quotient $J_{F,S}$. Such $c'$ is denoted by $c$ again in (5.2.3.4), as are its $v$-indexed components in the finite product $\prod_{v\in S'-S}(1-c(\pi_v))^{-1}$.

This forces $L_{S'}(\pi_{S,S'}(f),c)=0$ for all $c$ by the Identity Theorem, and hence $\pi_{S,S'}(f)\in\ker(\Phi_{F,S',\omega_{S'}})$.

The continuous linear operator $\bar\pi_{S,S'}$ from (5.2.1.1) therefore descends to a continuous linear operator $\bar\pi_{S,S'}$ as in (5.2.3.1).

By (5.2.3.4), we deduce that $\bar\pi_{S,S'}$ is injective. Indeed, let $f\in\mathcal S(\mathbf A_{F,S})$ be such that $\bar\pi_{S,S'}(\Phi_{F,S,\omega_S}(f))=0$. Then $L_{S'}(\pi_{S,S'}(f),c)=0$ for all $c\in\Omega(J_{F,S'})(\omega_{S'})$, and by (5.2.3.4) and the Identity Theorem we deduce $Z_S(f,c)=0$ for all $c\in\Omega(J_{F,S})(\omega_S)$, which implies $f\in\ker(\Phi_{F,S,\omega_S})$ by Lemma 5.1.2.2.

Since $\bar\pi_{S,S'}$ from (5.2.1.1) is a linear topological embedding, and the linear topologies on $\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(\omega_{S'},\mathcal S(\mathbf A_{F,S'}))$ are the quotient topologies induced from $\mathcal S(\mathbf A_{F,S})$, respectively $\mathcal S(\mathbf A_{F,S'})$, by $\Phi_{F,S,\omega_S}$, respectively $\Phi_{F,S',\omega_{S'}}$, we deduce that $\bar\pi_{S,S'}$ from (5.2.3.1) is a linear topological embedding. To see this, we observe that the idempotent $\bar\Pi_S$ from (??) $^{5}$ on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ with range $\bar\pi_S(\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})))$ descends to each space $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ and has range $\bar\pi_S(\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S})))$, so long as $\omega$ is unramified outside $S$. It follows that $\bar\pi_S$ has closed range and it is a continuous linear bijection onto its image, and it is therefore a linear topological embedding, for every $S$ such that $\omega$ is unramified outside $S$. This implies that $\bar\pi_{S,S'}$ also has closed range, given by $\bar\pi_{S'}^{-1}(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)))$, and being a continuous linear bijection onto its image, it is a linear topological embedding.

We deduce that the inductive system $\{\mathrm H_{0,\mathrm{cont}}(\omega_{S'},\mathcal S(\mathbf A_{F,S}))\}_{S\subset S'\subset\Sigma_F}$ is strict, and the locally convex inductive limit admits a unique continuous linear operator $\bar\pi$ to $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$, since each $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$ does compatibly with the continuous transition operators $\pi_{S,S'}$.

$\bar\pi$ is a continuous bijection. It is also a linear topological embedding: to see this, we observe that the linear topology on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ is the quotient topology induced from $\mathcal S(\mathbf A_F)$ by $\Phi_{F,\omega}$, and $\mathcal S(\mathbf A_F)$ is linearly topologically isomorphic to the strict locally convex inductive limit of the $\mathcal S(\mathbf A_{F,S})$ with the $\pi_{S,S'}$ from (2.1.4.2) as continuous transition operators, by Proposition 2.1.4.1. It follows that $\bar\pi$, pre-composed with the surjective continuous linear operator

$$
\operatorname*{\mathrm{colim}}_{S\subset S'\subset\Sigma_F}\mathcal S(\mathbf A_{F,S'})\to\operatorname*{\mathrm{colim}}_{S\subset S'\subset\Sigma_F}\mathrm H_{0,\mathrm{cont}}(\omega_{S'},\mathcal S(\mathbf A_{F,S'}))
$$

which is open by [Gro-f, Ch.4,§5,Thm.2(1),p.148] (see also [SN, §2,Cor.3,p.8]), equals the composition of the linear topological isomorphism $\pi$ from (2.1.4.4) of Proposition 2.1.4.1, followed by $\Phi_{F,\omega}$, which is a quotient map. In particular, $\bar\pi$ is open, and hence a linear topological isomorphism.

(2) : Since $\mathcal S(\mathbf A_{F,S})$ is a strict locally convex inductive limit of nuclear Fréchet spaces, then its separated quotient $\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$ is a locally convex inductive limit of nuclear Fréchet spaces (possibly non-strict). Indeed, by Lemma 5.1.2.2 the kernel of $\Phi_{F,S}$ is $\ker(Z_S)$, and by Lemma 5.1.2.1, $\ker(\Phi_F)$ is $\ker(Z)$. As in the proof of (2) from Theorem 5.2.1.1, $\pi_S^{-1}\ker(\Phi_F)=\ker(\Phi_{F,S})$, and by Lemma 5.1.2.2 and Lemma 5.1.2.1 formation of such kernels and pre-images under $\pi_S$ is compatible with passage to $\omega$-, respectively $\omega_S$-isotypes.

This proves that the continuous linear operator $\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ is compatible with $\omega_S$-, respectively $\omega$-isotypes. By Theorem 5.2.1.1, such induced continuous linear operator $\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ is a linear topological embedding, and to see that $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ is an LF-space, by (1) it is enough to show that so is each $\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$. Since $\mathcal S(\mathbf A_{F,S})$ is, and by Theorem 5.1.1.3(3) $\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$ is a separated quotient of an LF-space, $\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$ is an LF-space.

The same argument applies to $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$.

---
$^5$Return here.

## PDF page 235

**5.2. STRUCTURE THEOREM I: TOPOLOGY OF THE SPACES OF ADELIC $\theta$-FUNCTIONS** · **235**

As such, $\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$ is Hausdorff, locally convex and complete. It is nuclear (by [Scha, Ch.III,Thm.7.4]) and barrelled (by [Scha, Ch.II,§8,Cor.2,p.61]). It is Montel by completeness combined with [Tre, Part III,Ch.50,Prop.50.2(5.12)], which applies by nuclearity (see also [Scha, Ch.III,§7,Cor.2,p.101]).

Being these properties stable under passage to locally convex inductive limits, they are inherited by $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ by (1). By [Scha, Ch.IV,§6,6.1,p.148] (which applies since $\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ are bornological by [Scha, Ch.II,§8.8.2,Cor.2,p.62], being separated quotients of $\mathcal S(\mathbf A_{F,S})$, respectively $\mathcal S(\mathbf A_F)$) and [Scha, Ch.IV,§5,5.9,p.147] (see also [Jar, Part II,Ch.11,§11.5,Prop.4(f),p230]), the strong duals $(\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S})))'_\beta$ and $(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)))'_\beta$ are complete and Montel.

The strong duals $(\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S})))'_\beta$ and $(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)))'_\beta$ are nuclear by [Scha, Ch.III,§7,Thm.7.4,p.103], because, being $\Phi_{F,S,\omega_S}$, respectively $\Phi_{F,\omega}$, are quotient maps, and hence the adjoints $\Phi'_{F,S,\omega_S}$ and $\Phi'_{F,\omega}$ are linear topological embeddings: to see this, we use [NB, Thm.8.11.3(b)] to deduce that $\Phi_{F,S,\omega_S}$ and $\Phi_{F,\omega}$ are weakly continuous, and being surjective, by [NB, Thm.8.13.2] their adjoints are weakly relatively open and injective. By Theorem 5.1.1.3, since $\ker(\Phi_{F,S,\omega_S})$ and $\ker(\Phi_{F,\omega})$ are closed, then by [NB, Thm.8.12.4(b)], the assumptions of [NB, Thm.8.13.4] are satisfied by $A:=\Phi'_{F,S,\omega_S}$, respectively $A:=\Phi'_{F,\omega}$, proving that they are both linear topological embeddings.

(3) : Since $\bar\pi_{S,S'}$ from (5.2.3.1), and hence the unique continuous linear topological embedding $\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$, are compatible with the local and global $\theta$-function operators $\Phi_{F,S,\omega_S}$ and $\Phi_{F,\omega}$ and the continuous linear topological embeddings $\pi_S$ from (2.1.4.5) of Proposition 2.1.4.1, the existence and properties of $\bar\Pi_S$ follow from Lemma 2.1.4.3 and the convergence $\bar\Pi_S\to\mathrm{id}$ in $\mathscr L_\beta(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)))$ is shown by means of the same argument as in Corollary 2.1.4.4, using closedness of the linear image of $\bar\pi_{S,S'}$ from (5.2.3.1) for every $S$ and [Scha, Ch.II,§6,6.5,p.59] to deduce that every bounded subset $B\subset\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ is the image under $\bar\pi_{S_0}$ of a bounded subset $B_0\subset\mathrm H_{0,\mathrm{cont}}(\omega_{S_0},\mathcal S(\mathbf A_{F,S_0}))$ for a large enough $S_0$. $\square$

$^6$

We denote by

$$
\rho_F:C_F\times\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)) \tag{5.2.3.5}
$$

and

$$
\rho_{F,S}:J_{F,S}\times\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})) \tag{5.2.3.6}
$$

the continuous actions of $C_F$, respectively $J_{F,S}$, on the Hausdorff locally convex topological vector spaces $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ and $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$.

Let $\omega$ be a continuous character of $C^1_F$, respectively $J^1_{F,S}$.

In Proposition 5.2.3.2 below, we will be proving that there exist continuous open linear projectors defined on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ surjective onto the closed subspace:

$$
\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))(\omega):=\{\phi\in\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})):\rho_{F,S}(g,\phi)=\omega(g)\phi\text{ for all }g\in J^1_{F,S}\} \tag{5.2.3.7}
$$

and similarly on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, surjective onto the closed subspace:

$$
\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))(\omega):=\{\phi\in\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)):\rho_F(g,\phi)=\omega(g)\phi\text{ for all }g\in C^1_F\}. \tag{5.2.3.8}
$$

Such projectors factor through the quotients $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$, respectively $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$, therefore identifying them with (5.2.3.7) and (5.2.3.8), respectively.

We refer to the closed subspaces from (5.2.3.7) and (5.2.3.8) as the $\omega$-isotypes of $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, respectively $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$.

This leads to the following:

---
$^6$WORK 4: Arrive here and stop for today.

## PDF page 236

**236** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

PROPOSITION 5.2.3.2. *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places. Let $\omega$ be a continuous character of $C^1_F$, respectively of $J^1_{F,S}$.*

*(1) The integrals:*

$$
P_{F,\omega}:=\int_{C^1_F}\overline{\omega(g)}\rho_F(g,\cdot)\,\mathrm{d}\bar\mu_1(g),\quad P_{F,S,\omega}:=\int_{J^1_{F,S}}\overline{\omega(g)}\rho_{F,S}(g,\cdot)\,\mathrm{d}\bar\mu_{S,1}(g) \tag{5.2.3.9}
$$

*exist in the sense of Pettis, and define surjective open continuous linear operators:*

$$
P_{F,\omega}:\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))(\omega),\quad P_{F,S,\omega}:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))(\omega) \tag{5.2.3.10}
$$

*inducing linear topological isomorphisms:*

$$
P_{F,\omega}:\mathrm H_{0,\mathrm{cont}}(\omega,\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))(\omega) \tag{5.2.3.11}
$$

*and:*

$$
P_{F,S,\omega}:\mathrm H_{0,\mathrm{cont}}(\omega,\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))(\omega). \tag{5.2.3.12}
$$

*(2) The induced continuous linear operators:*

$$
P_F:\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\to\prod_{\omega\in\widehat{C^1_F}}\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)),\quad P_{F,S}:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\prod_{\omega\in\widehat{J^1_{F,S}}}\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})) \tag{5.2.3.13}
$$

*to the Hausdorff locally convex products, are continuous and injective.*

*(3) The operators $L$ and $L_S$ induce continuous injective $\mathbf C$-linear operators:*

$$
Z:\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))\to\mathscr M(\Omega(C_F)(\omega)),\quad Z_S:\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))\to\mathscr M(\Omega(J_{F,S})(\omega)) \tag{5.2.3.14}
$$

*compatible with the $\mathbf C$-linear decompositions of $\mathscr M(\Omega(C_F))$ and $\mathscr M(\Omega(J_{F,S}))$ from (5.2.2.2).*

*If $\omega$ is unramified outside $S$, the following diagram of continuous linear operators between Hausdorff locally convex topological vector spaces:*

(5.2.3.15)

```latex
\begin{tikzcd}
\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})) \arrow[r, "\bar\pi_S"] \arrow[d, "P_{F,S,\omega_S}"'] & \mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)) \arrow[d, "P_{F,\omega}"] \\
\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S})) \arrow[r, "\bar\pi_S"'] & \mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))
\end{tikzcd}
```

*commutes, where $\omega_S$ is the continuous character obtained from $\omega$ by restriction to $C^1_{F,S}$, descended to the quotient $J^1_{F,S}$.*

REMARK 5.2.3.3. We note that the constraint on $\omega$ being unramified outside $S$ is necessary to ensure that $\omega|_{C^1_{F,S}}$ descends to a character $\omega_S$ of $J^1_{F,S}$ along the quotient homomorphism $C^1_{F,S}\to J^1_{F,S}$. This happens precisely when $\omega$ is unramified outside $S$.

We note that the products in Lemma 5.2.3.2 are endowed with the product topology, which is Hausdorff locally convex by [Scha, Ch.II,p.52].

PROOF. $^7$ (1) : Upon defining, for $G:=C^1_F$, respectively $G:=J^1_{F,S}$, both compact Hausdorff abelian groups, and upon choosing $\mu_G$ to be $\bar\mu_1$, respectively $\bar\mu_{S,1}$, each induced by a choice of continuous homomorphic section to the idelic norm, respectively the $S$-idelic norm, the continuous $G$-action on $E:=\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, respectively $E:=\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ defined as $\rho_G:=\bar\omega(\cdot)\rho_F$, respectively $\rho_G:=\bar\omega(\cdot)\rho_{F,S}$, Lemma 4.3.3.1 applies, since by Theorem 5.2.1.1(1), $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ and $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ are Hausdorff locally

---
$^7$Return here.

## PDF page 237

**5.2. STRUCTURE THEOREM I: TOPOLOGY OF THE SPACES OF ADELIC $\theta$-FUNCTIONS** · **237**

convex and complete, hence quasi-complete by [Scha, Ch.III,§4,Corollary,p.85], and the continuous $G$-action defined in the foregoing is uniformly continuous, since the operator $L$ from (5.1.1.1), respectively $L_S$ from (5.1.1.2), combined with Lemma 5.1.2.2 showing that $L$, respectively $L_S$, factors through $E$, exhibits it as being isomorphic to a diagonal multiplication action by the image of $\bar\omega$ in $\mathrm U(1)$ (see Lemma 5.1.3.1), hence uniformly continuous since such action on any Hausdorff locally convex $\mathbf C$-linear space satisfies the uniform continuity condition of Lemma 4.3.3.1 by absolute homogeneity of any seminorm on a $\mathbf C$-linear space.

Lemma 4.3.3.1 therefore gives (1), since both $P_{F,\omega}$ and $P_{F,S,\omega}$ are of the form $\Phi_G$.

(2) : The operators $P_F$ and $P_{F,S}$ from (5.2.3.13) are injective because if $\phi\in\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ is such that $P_F(\phi)=0$, then by Lemma 4.3.2.2 $\phi=0$ in $L^2(C_F,\bar\mu)$, and hence $\phi=0$ in $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ since $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\subset L^2(C_F,\bar\mu)$ as $\mathbf C$-linear spaces, as the elements of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ are continuous functions on $C_F$, square $\bar\mu$-integrable by Proposition 2.2.3.4. The same argument shows that $P_{F,S}$ is injective, upon using Proposition 2.3.1.2 to see that $|\cdot|^\varepsilon_{F,S}\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ is a $\mathbf C$-linear subspace of $L^2(C_{F,S},\bar\mu_S)$ for every real number $\varepsilon>0$. Indeed, if $P_{F,S}(\phi)=0$, then $|\cdot|^\varepsilon_{F,S}P_{F,S}(\phi)=0$ and so $|\cdot|^\varepsilon_{F,S}\phi=0$ as an element of $|\cdot|^\varepsilon_{F,S}\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, and hence $\phi=0$.

We define, for any $\phi\in\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$:

$$
Z(\phi,c):=Z(\Phi_{F,\omega}(f),c),\,c\in\Omega(C_F)
$$

for some $f\in\mathcal S(\mathbf A_F)$ such that $\Phi_{F,\omega}(f)=\phi$. This assignment is well-defined by design of $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$. Continuity is a consequence of the fact that the Hausdorff locally convex topology on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ is the quotient topology of the Hausdorff locally convex topology on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, and so continuity of $L$ is a consequence of continuity of $L$.

Similarly, we define, for any $\phi\in\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$:

$$
Z_S(\phi):=Z_S(\Phi_{F,S,\omega}(f))
$$

for some $f\in\mathcal S(\mathbf A_{F,S})$ such that $\Phi_{F,S,\omega}(f)=\phi$, and $L_S$ is continuous because $L_S$ is.

Commutativity of the diagram in (5.2.3.15) is a consequence of the identities $\Phi_{F,\omega}=P_{F,\bar\omega}\circ\Phi_F$ and $\Phi_{F,S,\omega_S}=P_{F,S,\overline{\omega_S}}\circ\Phi_{F,S}$, and compatibility of $\Phi_F$, $\Phi_{F,S}$ with the continuous linear operators $\pi_S$ on $\mathcal S(\mathbf A_{F,S})$ and $\bar\pi_S$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$. $\square$

REMARK 5.2.3.4. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

(1) Let $V_{F,S}$ be the $\mathbf C$-linear subspace of $\mathcal S(\mathbf A_{F,S})$ generated by the elements $f_\xi(x):=f(x)-f(\xi^{-1}x)$ as functions of $x\in\mathbf A_{F,S}$, as $f\in\mathcal S(\mathbf A_{F,S})$ and $\xi\in\mathcal O_{F,S}^\times$. The kernel of $\Phi_{F,S}$ is the closure of $V_S$ with respect to the Hausdorff locally convex topology on $\mathcal S(\mathbf A_{F,S})$ induced by $\Phi_{F,S}$.

(2) Let $V_F$ be the $\mathbf C$-linear subspace of $\mathcal S(\mathbf A_F)$ generated by the elements $f_\xi(x):=f(x)-f(\xi^{-1}x)$ as functions of $x\in\mathbf A_F$, as $f\in\mathcal S(\mathbf A_F)$ and $\xi\in F^\times$. The kernel of $\Phi_F$ is the closure of $V_F$ with respect to the Hausdorff locally convex topology on $\mathcal S(\mathbf A_F)$ induced by $\Phi_F$.

Both assertions are a consequence of the fact that upon endowing $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ with the quotient topology inherited from $\mathcal S(\mathbf A_{F,S})$, respectively $\mathcal S(\mathbf A_F)$, then the kernel of $\Phi_{F,S}$ and the kernel of $\Phi_F$ are the closure of $0$ in $\mathcal S(\mathbf A_{F,S})$, respectively $\mathcal S(\mathbf A_F)$, with respect to the topology induced by $\Phi_{F,S}$, respectively $\Phi_F$. This is a consequence of the definition of quotient topology. To see (1) and (2) it is therefore sufficient to observe that we have $V_{F,S}\subset\ker(\Phi_{F,S})$, and $V_F\subset\ker(\Phi_F)$.

Similar assertions hold for $\ker(\Phi_{F,S,\omega})$, respectively $\ker(\Phi_{F,\omega})$, for $\omega\in\widehat{J^1_{F,S}}$, respectively $\omega\in\widehat{C^1_F}$.

This justifies to some extent the use of the notation $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, respectively $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, for the quotients of $\mathcal S(\mathbf A_{F,S})$ and $\mathcal S(\mathbf A_F)$ by $\ker(\Phi_{F,S})$ and $\ker(\Phi_F)$.

A full justification for the use of such notation is indeed available: we note that both Hausdorff locally convex topological $\mathbf C$-vector spaces $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ are bornological. Upon

## PDF page 238

**238** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

forgetting their topologies and retaining only their von Neumann bornology, i.e. the bornology of all bounded subsets, we obtain the two underlying “bornological spaces” in the sense of [Me3]. As such, each is indeed the degree-zero homology of the bornologically smooth (in the sense of [Me3, Prop.4.7,p.22]) $\mathbf C[\mathcal O_{F,S}^\times]$-module $\mathcal S(\mathbf A_{F,S})$, respectively of the bornologically smooth (in the sense of [Me3, Prop.4.7,p.22]) $\mathbf C[F^\times]$-module $\mathcal S(\mathbf A_F)$, in the usual sense of derived functor homology and cohomology.

Both $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ are then seen to be smooth $\mathcal D(J_{F,S})$-, respectively smooth $\mathcal D(C_F)$-modules, where $\mathcal D(J_{F,S})$ and $\mathcal D(C_F)$ are the convolution algebras of test functions on $J_{F,S}$ and $C_F$ (in the sense of [Bru, §4], seen as bornological algebras as in [Me3, §4]). We will only need the structure of continuous modules over such algebras, and the smoothness (in the sense of linear topological representations) will play an indirect role through the existence and continuity of certain infinitesimal generators. It will be our preference to retain the topologies throughout, to access robust and well established literature on nuclear operators.

The kernels of $\Phi_{F,S}$ and $\Phi_F$ turn out to be the bornological closure of the linear subspaces $V_{F,S}$ and $V_F$ in $\mathcal S(\mathbf A_{F,S})$, respectively $\mathcal S(\mathbf A_F)$. In particular, our $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ recover, upon forgetting their topologies and only retaining their von Neumann bornologies, the bornological spaces $\mathcal S(\mathbf A_{F,S})/\mathcal O_{F,S}^\times$ and $\mathcal S(\mathbf A_F)/F^\times$ of [Me1, §4.5].

We will never be using the fact that both $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, as bornological spaces in the sense of [HN] (see also [Me2]), are indeed degree-zero homologies in the classical sense of homological algebra, although within the context of bornological spaces (see [Me3, Thm.4.15,p.28]).

We will only be using, throughout the remainder of this Chapter, that each is equipped with a linear surjective map from $\mathcal S(\mathbf A_{F,S})\otimes_{\mathbf C[\mathcal O_{F,S}^\times]}\mathbf C=\mathrm H_0(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, respectively $\mathcal S(\mathbf A_F)\otimes_{\mathbf C[F^\times]}\mathbf C=\mathrm H_0(F^\times,\mathcal S(\mathbf A_F))$. Indeed, we have:

$$
\mathcal S(\mathbf A_{F,S})\otimes_{\mathbf C[\mathcal O_{F,S}^\times]}\mathbf C=\mathcal S(\mathbf A_{F,S})/V_{F,S},\quad \mathcal S(\mathbf A_F)\otimes_{\mathbf C[F^\times]}\mathbf C=\mathcal S(\mathbf A_F)/V_F
$$

and, as discussed in the foregoing, $V_{F,S}\subset\ker(\Phi_{F,S})$ and $V_F\subset\ker(\Phi_F)$. This will facilitate calculations.

REMARK 5.2.3.5. We recall from Proposition 5.2.3.2 that $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$, for $\omega\in\widehat{C^1_F}$, is identified with the $\omega$-isotype:

$$
\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))(\omega)
$$

under the continuous open linear operator $P_{F,\omega}$ on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, which factors through $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ and surjects onto $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))(\omega)$.

The restriction of $L$ to the closed subspace $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))(\omega)$ is, however, not the operator that $L$ induces on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$, but it is so only after multiplication by the scalar $\bar\mu_1(C^1_F)$.

A similar observation holds for the $\omega$-isotypes in $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ for any $\omega\in\widehat{J^1_{F,S}}$.

**5.2.4. Interaction with the Fourier Transform.** Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places.

The $S$-adelic Fourier transform is a linear topological automorphism on $\mathcal S(\mathbf A_{F,S})$. We denote it $\mathcal F_S:\mathcal S(\mathbf A_{F,S})\to\mathcal S(\mathbf A_{F,S})$.

In this subsection we prove that it descends to a linear topological automorphism of $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, which, as $S$ tends to $\Sigma_F$, tends to the inversion automorphism on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$.

THEOREM 5.2.4.1 (Equivariant Fourier Transform). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places.*

*(1) There exists a unique linear topological automorphism:*

$$
\mathcal F_S:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})) \tag{5.2.4.1}
$$

## PDF page 239

**5.2. STRUCTURE THEOREM I: TOPOLOGY OF THE SPACES OF ADELIC $\theta$-FUNCTIONS** · **239**

*satisfying $\mathcal F_S^2=\mathrm{id}$, making the following diagram of continuous linear operators between Hausdorff locally convex topological vector spaces:*

(5.2.4.2)

```latex
\begin{tikzcd}
\mathcal S(\mathbf A_{F,S}) \arrow[r, "\mathcal F_S"] \arrow[d, "\Phi_{F,S}"'] & \mathcal S(\mathbf A_{F,S}) \arrow[d, "\Phi_{F,S}"] \\
\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})) \arrow[r, "\mathcal F_S"'] & \mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))
\end{tikzcd}
```

*commute, compatibly with enlargement of $S$ and passage to $\omega_S$-isotypes (exchanging the $\omega_S$ and the $\bar\omega_S$-isotypes), for any continuous character $\omega\in\widehat{C^1_F}$.*

*(2) There exists a unique linear topological automorphism:*

$$
\mathcal F:\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)) \tag{5.2.4.3}
$$

*satisfying $\mathcal F^2=\mathrm{id}$, making the following diagram of continuous linear operators between Hausdorff locally convex topological vector spaces:*

(5.2.4.4)

```latex
\begin{tikzcd}
\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})) \arrow[r, "\bar\pi_S"] \arrow[d, "\mathcal F_S"'] & \mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)) \arrow[d, "\mathcal F"] \\
\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})) \arrow[r, "\bar\pi_S"'] & \mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))
\end{tikzcd}
```

*commute, compatibly with enlargement of $S$ and passage to $\omega$- and $\omega_S$-isotypes, for any continuous character $\omega\in\widehat{C^1_F}$.*

PROOF. (1) : By Lemma 5.1.2.2, we have $\ker(\Phi_{F,S})=\ker(Z_S)$. Let $f\in\mathcal S(\mathbf A_{F,S})$ be such that $\Phi_{F,S}(f)=0$. We have, for $c\in\Omega(J_{F,S})_{>0}$:

$$
\int_{C_{F,S}}\Phi_{F,S}(\widehat{f})(g)c(g)\,\mathrm{d}\bar\mu_S(g)=\rho_S(c)Z_S(f,\widehat{c})
$$

by (3.3.1.2) from Theorem 3.3.1.1.

Since $f\in\ker(\Phi_{F,S})$, we have $Z_S(f,\widehat{c})=0$ for all $\widehat{c}\in\Omega(J_{F,S})$, and hence $Z_S(\widehat{f},c)=0$ over $\Omega(J_{F,S})_{>0}$, and so $Z_S(\widehat{f},c)=0$ everywhere over $\Omega(J_{F,S})$ by the Identity Theorem. We deduce that we have $\mathcal F_S(f)=\widehat{f}\in\ker(\Phi_{F,S})$, and so $\mathcal F_S$ induces a unique continuous linear operator $\mathcal F_S:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ making the diagram in (5.2.4.2) commute. The same argument applies to $\mathcal F_S^{-1}$. Since $-1\in\mathcal O_{F,S}^\times$, the induced continuous linear operator $\mathcal F_S^{-1}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ satisfies $\mathcal F_S^2=\mathrm{id}$. Uniqueness implies compatibility with enlargement of $S$ and passage to isotypes.

(2) : By Lemma 5.1.2.1, we have $\ker(\Phi_F)=\ker(Z)$. Let $f\in\mathcal S(\mathbf A_F)$ be such that $\Phi_F(f)=0$. We have, for $c\in\Omega(C_F)_{>1}$:

$$
\int_{C_F}\Phi_F(\widehat{f})(g)c(g)\,\mathrm{d}\bar\mu(g)=Z(f,\widehat{c})
$$

by (3.2.2.2) from Theorem 3.2.2.1.

Since $f\in\ker(\Phi_F)$, we have $Z(f,\widehat{c})=0$ for all $\widehat{c}\in\Omega(C_F)$, and hence $Z(\widehat{f},c)=0$ over $\Omega(C_F)_{>1}$, and so $Z(\widehat{f},c)=0$ everywhere over $\Omega(C_F)$ by the Identity Theorem. We deduce that we have $\mathcal F(f)=\widehat{f}\in\ker(\Phi_F)$, and so $\mathcal F$ induces a unique continuous linear operator $\mathcal F:\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ making the diagram in (5.2.4.4) commute. The same argument applies to $\mathcal F^{-1}$. Since $-1\in F^\times$, the induced continuous linear operator $\mathcal F^{-1}$ on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ satisfies $\mathcal F^2=\mathrm{id}$. Uniqueness implies compatibility with enlargement of $S$ and passage to isotypes. The assertion on $\mathcal F_S$ exchanging the $\omega_S$ and the $\bar\omega_S$-isotypes follows from the functional equation of (3.3.1.2) from Theorem 3.3.1.1. $\square$

## PDF page 240

**240** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

**5.3. Weil’s Principal Value Operators**

In this section we discuss continuous operators on $\mathcal S(\mathbf A_{F,S})$ and $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, that have the effect of removing the poles of the $S$-idelic Zeta functions $Z_S(f,c)$ on $\Omega(J_{F,S})$ in a controlled manner, enabling a detailed study of the topology of $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and its isotypes, which will in turn enable the remaining of the Structure Theorems in this Chapter to be stated and proved, and upon which several constructions in sequel Chapters rest.

**5.3.1. Non-Archimedean Principal Value Operators.** Let $F$ be a number field.

Lemma 5.3.1.1. *Let $F$ be a number field, $v$ a finite place, $\pi_v$ a choice of uniformizer at $v$. The linear operator:*

$$
P_v:\mathcal S(F_v)\to\mathcal S(F_v) \tag{5.3.1.1}
$$

*defined by $P_v(f):=f-\rho_v(\pi_v,f)$, does not depend on the choice of $\pi_v$, and it is a linear topological embedding. Its range is the kernel of the continuous functional $\delta_0\in\mathcal S(F_v)'_\beta$.*

Proof. The range of $P_v$ is closed by Proposition C.2.5.1, since $\mathcal S(F_v)$ carries the finest locally convex topology by Proposition 2.1.2.4. It is contained in the kernel of $\delta_0\in\mathcal S(F_v)'_\beta$. Assume $f\in\mathcal S(F_v)$ is such that $f(0)=0$.

Since $\delta_0$ is $\mathcal O_{F_v}^\times$-invariant, we may write its kernel, up to linear topological isomorphism, as $\bigoplus_{\omega\in\widehat{\mathcal O_{F_v}^\times}}\ker(\delta_0)(\omega)$, compatibly with the linear and topological decomposition $\mathcal S(F_v)\simeq\bigoplus_{\omega\in\widehat{\mathcal O_{F_v}^\times}}\mathcal S(F_v)(\omega)$, and since $P_v$ is compatible with both decompositions and multiplication by $\omega^{-1}$ is a bounded invertible linear operator on $\ker(\delta_0)$ permuting the linear topological direct summands, we may assume without loss of generality that $f$ is $\mathcal O_{F_v}^\times$-invariant.

Since $f$ is compactly supported away from $0\in F_v$, there exists an integer $N\ge 0$ such that the support of $f$ is contained within $\bigcup_{-N\le m\le N}\pi_v^m\mathcal O_{F_v}$. The constant value $c_m$ of $f$ over $\pi_v^m\mathcal O_{F_v}-\pi_v^{m+1}\mathcal O_{F_v}$ is such that $f-c_m\cdot\mathrm{1}_{\pi_v^m\mathcal O_{F_v}^\times}$ is supported over $\bigcup_{-N\le m\le N}\pi_v^m\mathcal O_{F_v}-\pi_v^m\mathcal O_{F_v}^\times$, and we may iteratively write $f=\sum_{-N\le m\le N}c_m\cdot\mathrm{1}_{\pi_v^m\mathcal O_{F_v}^\times}$. We may therefore assume $f=\mathrm{1}_{\pi_v^m\mathcal O_{F_v}^\times}$ for some $m\in\mathbf Z$. Indeed we have, since $\mathcal O_{F_v}^\times=\mathcal O_{F_v}-\pi_v\mathcal O_{F_v}$, $f=P_v(\mathrm{1}_{\mathcal O_{F_v}})$. $\square$

We recall here the definition of the operators:

$$
P_v:\mathcal S(F_v)\to\mathcal S(F_v) \tag{5.3.1.2}
$$

for $v$ any finite place of $F$, defined in (5.3.1.1).

We recall from Theorem 3.4.3.3 that for each non-Archimedean place $v$ of $F$, and for each $c_v\in\Omega(F_v^\times)$, there exists a unique local eigendistribution $\Delta'_v\in\mathcal S(F_v)'_\beta$ (see Theorem 3.4.3.3(1)) such that:

$$
\langle\Delta'_v(c_v),\mathrm{1}_{\mathcal O_{F_v}^\times}\rangle_{\mathcal S(F_v)'_\beta,\mathcal S(F_v)}=1 \tag{5.3.1.3}
$$

if $c_v$ is unramified at $v$, and

$$
\langle\Delta'_v(c_v),c_v^{-1}\mathrm{1}_{\mathcal O_{F_v}^\times}\rangle_{\mathcal S(F_v)'_\beta,\mathcal S(F_v)}=1 \tag{5.3.1.4}
$$

if $c$ is ramified at $v$.

Note that by Theorem 3.4.3.3(1.c), for $f_v=\overline{\chi}\cdot\mathrm{1}_{\mathcal O_{F_v}^\times}$ with $\chi\in\widehat{F_v^\times}$ a continuous character, we have $Z_v(f_v,c_v)=\mu_v(\mathcal O_{F_v}^\times)$ for $c_v\in\Omega(F_v^\times)(\chi)$, and $Z_v(f_v,c_v)=0$ otherwise.

For $\pi_v\in F_v$ a choice of uniformizer at $v$, $P_v$ is defined by sending $f\in\mathcal S(F_v)$ to the Schwartz-Bruhat function of $x\in F_v$ defined by $f(x)-f(\pi_v^{-1}x)$. Upon denoting by $\rho_v:F_v^\times\times\mathcal S(F_v)\to\mathcal S(F_v)$ the continuous left-translation action of $F_v^\times$ on $\mathcal S(F_v)$, we have $P_v(f)=f-\rho_v(\pi_v,f)$.

## PDF page 241

**5.3. WEIL’S PRINCIPAL VALUE OPERATORS** · **241**

Lemma 5.3.1.1 described the range of $P_v$: it is the kernel of $\delta_0\in\mathcal S(F_v)'_\beta$. The kernel of $P_v$ is trivial: indeed, if $f(x)=f(\pi_v^{-1}x)$ for all $x\in F_v$, then we also have $f(\pi_v^{\mathbf Z}x)=f(x)$ for all $x\in F_v$, and since $f$ is compactly supported, say over $K_v\subset F_v$, and $\pi_v^{\mathbf Z}K_v\cap K_v$ is finite, we see that $f$ must vanish identically, since for each $x\in K_v$ there exists $m\in\mathbf Z$ such that $\pi_v^mx\notin K_v$.

Lemma 5.3.1.1 proves that $P_v$ is relatively open (in fact, a linear topological embedding onto its closed range), thanks to the Hausdorff locally convex topology on $\mathcal S(F_v)$ being the finest locally convex topology (see Proposition 2.1.2.4).

We introduce the following:

Definition 5.3.1.2. Let $F$ be a number field, $v$ a finite place of $F$.

We define:

$$
\mathrm{PV}_v:\mathcal S(F_v)\to\mathcal S(F_v) \tag{5.3.1.5}
$$

to be the unique continuous linear operator uniquely determined by the following conditions: for any continuous character $\omega\in\widehat{\mathcal O_{F_v}^\times}$:

(1) $\mathrm{PV}_v(\mathcal S(F_v)(\omega))\subset\mathcal S(F_v)(\omega)$.

(2) $\mathrm{PV}_v$ induces the identity operator on $\mathcal S(F_v)(\omega)$ if $\omega$ is non-trivial.

(3) $\mathrm{PV}_v=P_v$ on $\mathcal S(F_v)(\omega)$ if $\omega$ is trivial.

We refer to $\mathrm{PV}_v$ as Weil’s Principal Value operator on $\mathcal S(F_v)$.

Lemma 5.3.1.3. *Let $F$ be a number field, $v$ a finite place of $F$. Then Weil’s Principal Value operator $\mathrm{PV}_v:\mathcal S(F_v)\to\mathcal S(F_v)$ exists and is continuous. It is a linear topological embedding with closed range, compatible with passage to isotypes.*

Proof. Since $\mathcal O_{F_v}^\times$ is compact Hausdorff, and $\mathcal S(F_v)$ is Hausdorff, locally convex, complete, with $\mathcal O_{F_v}^\times$ acting on $\mathcal S(F_v)$ uniformly continuously (see Lemma 2.1.2.10) by left-translation, Lemma 4.3.3.1 applies to give that the operator $f\mapsto\Phi_{v,\omega}(f)(x):=\mu_v(\mathcal O_{F_v}^\times)^{-1}\int_{\mathcal O_{F_v}^\times}\overline{\omega}(g)f(g^{-1}x)\,\mathrm{d}\mu_v(g)$ is continuous, linear, with closed range, and surjective onto $\mathrm H^0(\omega,\mathcal S(F_v))$. Moreover, $\Phi_{v,\omega}$ is idempotent on $\mathrm H^0(\omega,\mathcal S(F_v))$, a closed subspace of $\mathcal S(F_v)$.

It follows that $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$ splits off as a linear topological direct summand, i.e. $\mathcal S(F_v)=\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))\oplus W$, where $W$ is the closure of $\mathrm H^0(\omega,\mathcal S(F_v))$ for all non-trivial continuous characters $\omega$ of $\mathcal O_{F_v}^\times$.

On $W$, indeed $\bigoplus_{\omega\ne 1}(\mathrm{Id}:\mathrm H^0(\omega,\mathcal S(F_v))\to\mathrm H^0(\omega,\mathcal S(F_v)))=\mathrm{Id}_W$, the identity, has the same effect as $\mathrm{PV}_v|_W$, if $\mathrm{PV}_v$ exists. On $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$, $P_v$ has the same effect as $\mathrm{PV}_v$, if $\mathrm{PV}_v$ exists.

$\mathrm{PV}_v:=P_v\oplus\mathrm{Id}_W$ extends by continuity to $\mathcal S(F_v)$, since the finite direct sum $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))\oplus W$ is already complete by [Scha, Ch.II,§6,Thm.6.2,p.55].

This definition of $\mathrm{PV}_v$ indeed satisfies all the requirements, and any other continuous linear operator on $\mathcal S(F_v)$ that does, agrees with $\mathrm{PV}_v$ on both $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$ and $W$, and hence agrees with $\mathrm{PV}_v$.

To show that $\mathrm{PV}_v$ is a linear topological embedding with closed range, it is enough to show that it is injective and with closed range. This reduces to showing that $P_v$ satisfies the same conditions, as a continuous linear operator on $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$, which is indeed the case by Lemma 5.3.1.1 and closedness of $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$ as a $P_v$-stable linear subspace of $\mathcal S(F_v)$. $\square$

Definition 5.3.1.4. Let $F$ be a number field. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Let $S_0 \subset S$ be a finite subset of finite places.

We define:

(1) Weil’s $S$-local Principal Value operator:

$$
\mathrm{PV}_{S,S_0}:\mathcal S(\mathbf A_{F,S}) \to \mathcal S(\mathbf A_{F,S}) \tag{5.3.1.6}
$$

## PDF page 242

**242** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

as the composition of the linear topological isomorphism:

$$
\mathcal S(\mathbf A_{F,S})\simeq\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F_v) \tag{5.3.1.7}
$$

provided by (2.1.4.1) from Proposition 2.1.4.1, followed by the tensor product of the identity $\mathrm{Id}_{\mathcal S(\mathbf A_{F,S_\infty})}$ on $\mathcal S(\mathbf A_{F,S_\infty})$ and the unique continuous linear operator on $\bigotimes_{v\in S_f}\mathcal S(F_v)$ obtained as the tensor product of the identity $\mathrm{Id}_{\mathcal S(F_v)}$ if $v\in S-S_0$, and of $\mathrm{PV}_v$ if $v\in S_0$.

(2) Weil’s Global Principal Value operator:

$$
\mathrm{PV}_{S_0}:\mathcal S(\mathbf A_F)\to\mathcal S(\mathbf A_F) \tag{5.3.1.8}
$$

as the tensor product of $\mathrm{PV}_{S,S_0}$ with the identity on $\mathcal S(\widehat{\prod}_{\Sigma_F-S}(F_v,\mathcal O_{F_v}))$.

By design of $\mathrm{PV}_{S_0}$, we have that formation of $\mathrm{PV}_{S_0}$ and $\mathrm{PV}_{S,S_0}$ from (5.3.1.6) and (5.3.1.8) is compatible with the transition operators $\pi_{S,S'}$ from (2.1.4.2) of Proposition 2.1.4.1, and $\pi_S$.

We note that since $\mathcal S(\mathbf A_{F,S_\infty})$ is nuclear by Proposition 2.1.4.1(3), we have, by Proposition 2.1.4.1(2) and [Jar, Part III,Ch.16,§16.2,Cor.3,p.348], that $\mathrm{PV}_{S,S_0}$ and $\mathrm{PV}_{S_0}$ are, respectively, linear topological embeddings with closed (as a consequence of Lemma 5.3.1.3 and [Jar, Part III,Ch.15,§15.2,Prop.1,p.326]) range, by Lemma 5.3.1.3.

Formation of $\mathrm{PV}_{S,S_0}$ commutes with the continuous left-translation action of $\mathcal O_{F,S}^\times$ on $\mathcal S(\mathbf A_{F,S})$, and it is compatible with the operators $\pi_{S,S'}$ from (5.2.1.1) for any finite subset $S'\subset\Sigma_F$ containing $S$. It follows that $\mathrm{PV}_{S,S_0}$ descends to a unique continuous linear operator:

$$
\mathrm{PV}_{S,S_0}:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})) \tag{5.3.1.9}
$$

and similarly $\mathrm{PV}_{S_0}$ on $\mathcal S(\mathbf A_F)$ descends to a unique continuous linear operator:

$$
\mathrm{PV}_{S_0}:\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)) \tag{5.3.1.10}
$$

both compatible with formation of $J_{F,S}^1$-, respectively $C_F^1$-isotypes.

Lemma 5.3.1.5. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places, $S_0\subset S$ a non-empty finite subset of finite places. The operators $\mathrm{PV}_{S_0}$ from (5.3.1.9) and (5.3.1.10) are linear topological embeddings with closed range, compatible with passage to isotypes, and whose formation is compatible with the transition operators $\bar\pi_{S,S'}$ for any finite subset $S'\subset\Sigma_F$ containing $S$, and $\bar\pi_S$, provided by Theorem 5.2.1.1.*

Proof. To see this, it is enough to observe that it is injective by the Identity Theorem, since $L_S\circ \mathrm{PV}_{S,S_0}$, respectively $L\circ \mathrm{PV}_{S_0}$, is the operator sending $Z(f,c)$ for some $f\in\mathcal S(\mathbf A_{F,S})$, respectively $f\in\mathcal S(\mathbf A_F)$, as meromorphic functions on $\Omega(J_{F,S})$, respectively $\Omega(C_F)$, to the products $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q_v^{-s-it_v})Z_S(f,\chi\lvert\cdot\rvert_{F,S}^s)$, respectively $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q_v^{-s-it_v})Z(f,\chi\lvert\cdot\rvert_F^s)$, where, for $\chi\in\widehat{J_{F,S}}$, respectively $\chi\in\widehat{C_F}$, $S_\chi$ is the finite set of places of $F$ contained in $S$, respectively of $F$, at which $\chi$ is ramified.

$\mathrm{PV}_{S,S_0}$, respectively $\mathrm{PV}_{S_0}$, is therefore a linear topological embedding onto its closed range, since it is injective and its composition with $\Phi_{F,S}$, respectively $\Phi_F$, is the composition of the relatively open continuous linear operators $\mathrm{PV}_{S,S_0}$ from (5.3.1.6), respectively $\mathrm{PV}_{S_0}$ from (5.3.1.8), followed by $\Phi_{F,S}$, respectively $\Phi_F$.

As such, each $\mathrm{PV}_{S,S_0}$ from (5.3.1.9) and $\mathrm{PV}_{S_0}$ from (5.3.1.10) is a linear topological embedding.

Since the continuous insertion operator $\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ induced by the operators from (5.2.1.1) is, by the First Structure Theorem (see Theorem 5.2.1.1), a linear topological embedding with closed range into $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, and formation of $\mathrm{PV}_{S,S_0}$, $\mathrm{PV}_{S_0}$ and $\bar\pi_S$ is compatible, we see that the range of $\mathrm{PV}_{S_0}$ in $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ is the image under $\bar\pi_S$ of the range of $\mathrm{PV}_{S,S_0}$ in $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, and it is therefore closed.

Compatibility with passage to isotypes is a consequence of Lemma 5.3.1.3. $\square$

## PDF page 243

**5.3. WEIL’S PRINCIPAL VALUE OPERATORS** · **243**

**5.3.2. Preparations on tempered distributions supported at the origin.** We record here results describing the topology on the space of tempered distributions on a finite product of Archimedean local fields, whose support is contained in a union of standard hyperplanes.

We begin with the two cases of interest, $\mathbf R$, $\mathbf C$.

We recall here that the bi-dual of a Hausdorff locally convex topological $\mathbf C$-vector space is defined to be the continuous dual of the strong dual; see [Jar, Part II,Ch.11,§11.2]. This convention, adopted throughout this work, is also in force throughout [Kothe-I, Kothe-II] (see [Kothe-I, Ch.V,§23,p.298]), as is in [Scha, Ch.IV,p.143], from which we shall be referring on occasion throughout this subsection, concerning topologies on the bi-dual.

Recall that the support of a tempered distributions $T\in\mathcal S(\mathbf R^m)$ for each integer $m\ge 0$, is defined to be the smallest closed subset $\mathrm{supp}(T)$ of $\mathbf R^m$ such that for any $x\in\mathbf R^m-\mathrm{supp}(T)$, there exists an open neighborhood $U\subset\mathbf R^m-\mathrm{supp}(T)$ of $x$ such that for any $f\in\mathcal S(\mathbf R^m)$ whose support is entirely contained in $U$, then $\langle T,f\rangle_{\mathcal S(\mathbf R^m)'_\beta,\mathcal S(\mathbf R^m)}=0$.

We refer the reader to [Horm, Ch.II,§2.2,Def.2.2.2], which applies by definition to elements of $\mathcal S(\mathbf R^m)'_\beta$ too, since $\mathcal S(\mathbf R^m)'_\beta$ is a $\mathbf C$-linear subspace of $\mathcal D(\mathbf R^m)'_\beta$ equipped with a finer topology, and to Definition D.1.8.2, which shows how to generalize this definition to tempered distributions Hausdorff locally compact abelian groups.

Theorem 5.3.2.1. *Let $T\in\mathcal S(\mathbf R)'_\beta$ be supported at $0\in\mathbf R$. Then there exists an integer $N\ge 0$, complex numbers $c_0,\dots,c_N$, such that, as elements of $\mathcal S(\mathbf R)'_\beta$, we have:*

$$
T=\sum_{0\le k\le N}c_k\delta_0^{(k)}. \tag{5.3.2.1}
$$

(1) *Let $\mathcal S_{00}(\mathbf R)$ be the closed subspace defined as $\bigcap_{k\ge 0}\ker(\delta_0^{(k)})$. The orthogonal in $\mathcal S(\mathbf R)'_\beta$ of $\mathcal S_{00}(\mathbf R)$ with respect to the duality $\langle\mathcal S(\mathbf R),\mathcal S(\mathbf R)'_\beta\rangle$ is a linear subspace of $\mathcal S(\mathbf R)'$ linearly isomorphic to the continuous dual of the quotient $\mathcal S(\mathbf R)/\mathcal S_{00}(\mathbf R)$, which, topologized with the strong topology on the continuous dual of the quotient, is linearly and topologically isomorphic to the $\mathbf C$-linear space underlying the polynomial algebra $\mathbf C[X]$ equipped with the finest locally convex topology, equivalently the topology induced by the family of seminorms $\{p_N\}_{N\ge 0}$ with:*

$$
p_N(c_0+c_1X+\dots+c_NX^N):=\sup_{0\le k\le N}\lvert c_k\rvert \tag{5.3.2.2}
$$

*the isomorphism being uniquely determined by the assignment $X^N\mapsto\frac{1}{N!}\delta_0^{(N)}$, and matching the degree of a polynomial with the finite order of the resulting distribution supported at $0\in\mathbf R$.*

(2) *The quotient $\mathcal S(\mathbf R)/\mathcal S_{00}(\mathbf R)$, equipped with the quotient topology, is linearly and topologically isomorphic to the $\mathbf C$-linear space underlying the formal power series algebra $\mathbf C[[X]]$ equipped with the Hausdorff locally convex topology induced by the family of seminoms $\{q_N\}_{N\ge 0}$:*

$$
q_N(\sum_{k\ge 0}c_kX^k):=\sup_{0\le k\le N}\lvert c_k\rvert \tag{5.3.2.3}
$$

*the isomorphism being defined by sending each $f\in\mathcal S(\mathbf R)'_\beta$ to the formal power series $\sum_{k\ge 0}\frac{f^{(k)}(0)}{k!}X^k$.*

Remark 5.3.2.2. Note that the strong topology of the quotient topology of $\mathcal S_{00}(\mathbf R)^\perp$ is equivalent to the subspace topology of the strong topology on $\mathcal S(\mathbf R)'$, since $\mathcal S(\mathbf R)$ is quasi-normable and its bounded subsets are pre-compact, by nuclearity (see [Jar, Part II,Ch.10,§10.7,Cor.3]). See Lemma 4.2.1.3. There is, in particular, no ambiguity on how to topologize $\mathcal S_{00}(\mathbf R)^\perp$.

Proof. By [Horm, Ch.VII,Thm.7.1.18,p.168], since, if $T\in\mathcal D(\mathbf R)'_\beta$ is supported at $0\in\mathbf R$, then its restriction (see [Horm, Ch.II,§2.2,p.41]) to $\mathbf R-\{0\}$ is homogeneous of degree $a\in\mathbf R$ (see [Horm,

## PDF page 244

**244** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

Ch.III,Def.3.2.2,p.74]) for any $a\in\mathbf R$, and hence $T$ is tempered and supported at the origin. If $T\in\mathcal S(\mathbf R)'_\beta$ is supported at the origin, then, since the continuous injective linear operator $\mathcal D(\mathbf R)\to\mathcal S(\mathbf R)$ induces a continuous injective (by denseness of $\mathcal D(\mathbf R)\subset\mathcal S(\mathbf R)$; see [Hörm, Ch.VII,Lemma 7.1.8,p.163]) linear operator $\mathcal S(\mathbf R)'_\beta\to\mathcal D(\mathbf R)'_\beta$, $T$ is also a distribution supported at $0$.

The continuous injective linear operator $\mathcal S(\mathbf R)'_\beta\to\mathcal D(\mathbf R)'_\beta$ therefore induces a linear bijection from the space of tempered distributions supported at $0\in\mathbf R$, and the space of distributions supported at $0\in\mathbf R$.

We note that every distribution $T\in\mathcal D(\mathbf R)'_\beta$ supported at $0\in\mathbf R$ is of finite order (see [Hörm, Ch.II,Example 2.1.2,p.34]). By [Hörm, Ch.II,Thm.2.3.4,p.46], $T=\sum_{0\le k\le N}c_k\delta_0^{(k)}$, for $N$ the finite order of $T$.

(1) : Let $T\in\mathcal S(\mathbf R)'_\beta$ be a tempered distribution such that $T(\mathcal S_{00}(\mathbf R))=0$, i.e. an element of $\mathcal S_{00}(\mathbf R)^\perp\subset\mathcal S(\mathbf R)'_\beta$. Let $x\in\mathbf R$, $x\ne 0$. For any open neighborhood $U\subset\mathbf R$ of $x$ such that $0\notin U$, we let $\phi\in\mathcal D(\mathbf R)$ be supported within $U$.

Then $\phi\in\mathcal S_{00}(\mathbf R)$, and hence $T(\phi)=0$. It follows that $T$ is supported at $0$, and hence of the form as in (5.3.2.1). Conversely, every tempered distribution of the form as in (5.3.2.1) is an element of $\mathcal S_{00}(\mathbf R)^\perp$.

This shows that indeed the assignment $X^N\mapsto\frac{1}{N!}\delta_0^{(N)}$ is a linear isomorphism $\mathbf C[X]\to\mathcal S_{00}(\mathbf R)^\perp$, and the degree $N$ of a polynomial matches the order of the resulting tempered distribution supported at $0\in\mathbf R$.

The linear operator $\mathbf C[X]\to\mathcal S_{00}(\mathbf R)^\perp$ is continuous, upon endowing the source with the finest locally convex topology, and the target with the strong topology on the continuous dual on the quotient $\mathcal S(\mathbf R)/\mathcal S_{00}(\mathbf R)$, noting that by [NB, Thm.8.12.1(a)], the continuous dual of $\mathcal S(\mathbf R)/\mathcal S_{00}(\mathbf R)$ is linearly isomorphic to $\mathcal S_{00}(\mathbf R)^\perp$.

It is therefore a continuous bijection.

The source is a strict LF-space, and the target is the strong dual of the Fréchet space $\mathcal S(\mathbf R)/\mathcal S_{00}(\mathbf R)$. We call $F:=\mathcal S(\mathbf R)/\mathcal S_{00}(\mathbf R)$ the quotient Fréchet space.

Since both $\mathcal S(\mathbf R)$ and $\mathcal S_{00}(\mathbf R)$ are nuclear Fréchet (the former by Proposition 2.1.1.6, the latter by [Scha, Ch.III,§7,Thm.7.4,p.103]), so is $F$ (by [Scha, Ch.III,§7,Thm.7.4,p.103], since $F$ is a separated quotient of a nuclear Fréchet space), and hence $F$ is Montel (see [Tre, Part III,Ch.50,Prop.50.2,(50.12),p.519]), hence reflexive (see [Jar, Part II,Ch.11,§11.5,Prop.1,p.11] and the subsequent discussion).

We let $\{U_k\}_{k\ge 0}$ be a countable decreasing sequence of closed absolutely convex $0$-neighborhoods, and $p_k$ the Minkowski functional of $U_k$ for each integer $k\ge 0$, such that $\{U_k\}_{k\ge 0}$ is a countable $0$-neighborhood base. We define $F_k$ to be the completion of the quotient $F/p_k^{-1}(0)$ with respect to the normed topology generated by the norm that $p_k$ induces on the quotient $F/p_k^{-1}(0)$. In particular, the range of the continuous linear operator $F\to F_k$ is dense.

By the proof of the “only if” implication of [Val-a, §5,Thm.3,p.343], which applies since, being $F$ nuclear and Fréchet, all its quotients by a closed subspace are also nuclear Fréchet, and hence Montel, hence reflexive, we may and do assume that $F_k$ is a reflexive Banach space.

In particular, by [Jar, Part II,Ch.11,§11.5,Cor.6(b),p.229], $(F_k)_\beta'$ is also reflexive.

The canonical continuous linear operator $F\to\varprojlim_{k\ge 0}F_k$ is a linear topological isomorphism. The projective limit is reduced in the sense of [Scha, Ch.IV,§4,p.139].

The Mackey dual $F'_{\tau(F',F)}$ is therefore linearly and topologically isomorphic to the locally convex inductive limit $\varinjlim_{k\ge 0}(F_k)_{\tau(F_k',F_k)}'$ where the transition continuous operators are the continuous adjoints of the continuous operators $F_{k+1}\to F_k$ for each integer $k\ge 0$, in turn induced by the containments $U_{k+1}\subset U_k$.

By reflexivity of $(F_k)_\beta'$, $\tau(F_k',F_k)=\beta(F_k',F_k)$ by [Jar, Part II,Ch.11,§11.4,Prop.1.(2),p.227]. In particular, $(F_k)_{\tau(F_k',F_k)}'$ is a (reflexive) Banach space, since it is linearly and topologically isomorphic to $(F_k)_\beta'$, and hence, by [Scha, Ch.IV,§4,Thm.4.4,p.139], $F_{\tau(F',F)}'$ is linearly and topologically isomorphic to the locally convex inductive limit $\varinjlim_{k\ge 0}(F'_k)_\beta$, a countable locally convex inductive limit of Banach spaces, hence an LF-space.

Since, by [Jar, Part II,Ch.11,§11.4,Prop.1(2),p.227], $\beta(F',F)=\tau(F',F)$, being $F$ reflexive, then $F_\beta'$ is an LF-space.

The continuous operator $\mathbf C[X]\to F_\beta'$ is therefore a linear topological isomorphism by [SN, §2,Cor.3,p.8].

## PDF page 245

**5.3. WEIL’S PRINCIPAL VALUE OPERATORS** · **245**

It follows that the composition of the linear topological isomorphisms $\mathbf C[X]\to F_\beta'\simeq\mathcal S_{00}(\mathbf R)^\perp$, which is the linear operator $\mathbf C[X]\to\mathcal S_{00}(\mathbf R)^\perp$, is indeed a linear topological isomorphism.

(2) : That the continuous linear operator $\mathcal S(\mathbf R)/\mathcal S_{00}(\mathbf R)\to\mathbf C[[X]]$ is a linear topological isomorphism follows from (1) and [Tre, Part II,Ch.22,Thm.22.1(b),p.228] (see also [Tre, Part I,Ch.10,Example III,p.91] and [Tre, Part I,Ch.13,Example I,p.130]), which gives that its continuous adjoint is a linear topological isomorphism, by [NB, Thm.8.13.5] and [NB, Thm.14.4.5(b)]. $\square$

Theorem 5.3.2.3. *Let $m\ge 0$ be an integer. We denote by $x_k:\mathbf R^m\to\mathbf R$, $1\le k\le m$, the global smooth coordinates on $\mathbf R^m$. We denote by $H_k$ the standard hyperplane $x_k=0$. Let $Z\subset\{1,\dots,m\}$ be a non-empty subset, equipped with the induced total ordering.*

*For $x\in\mathbf R^m$, we denote by $x_Z$ the vector in $\mathbf R^{\lvert Z\rvert}$ whose coordinates are $(x_k)_{k\in Z}$, and by $x_{Z^c}$ the vector in $\mathbf R^{m-\lvert Z\rvert}$ whose coordinates are $(x_k)_{k\notin Z}$, adopting the same notation for the multi-indices $\alpha_Z$, $\alpha_{Z^c}$ associated to $\alpha\in\mathbf N^m$.*

*Let $T\in\mathcal D(\mathbf R^m)'_\beta$ be compactly supported within the closed subset $H_Z:=\bigcap_{k\in Z}H_k$. Assume $T$ is of finite order $N\ge 0$.*

*Let $R_{H_Z}:\mathcal D(\mathbf R^m)\to\mathcal D(\mathbf R^{m-\lvert Z\rvert})$ be the linear operator assigned by sending $f$ to the smooth function $R_{H_Z}(f)$ obtained by restriction of $f$ to $H_Z\simeq\mathbf R^{m-\lvert Z\rvert}$.*

Then:

(1) *$R_{H_Z}$ is valued in $\mathcal D(\mathbf R^{m-\lvert Z\rvert})$ and continuous, and the same assignment defines a continuous linear operator $R_{H_Z}:\mathcal S(\mathbf R^m)\to\mathcal S(\mathbf R^{m-\lvert Z\rvert})$.*

(2) *There exist $N^m$ distributions $T_\alpha\in\mathcal D(\mathbf R^{m-\lvert Z\rvert})'_\beta$, for $\alpha\in\mathbf N^m$ such that $\lvert\alpha\rvert\le N$, compactly supported and of order $N-\lvert\alpha\rvert$, and such that for all $\phi\in\mathcal D(\mathbf R^m)$, we have:*

$$
\langle T,\phi\rangle_{\mathcal D(\mathbf R^m)'_\beta,\mathcal D(\mathbf R^m)}=\sum_{\alpha\in\mathbf N^m:\lvert\alpha\rvert\le N}\langle R'_{H_Z}(T_\alpha),\partial_x^\alpha\phi\rangle_{\mathcal D(\mathbf R^m)'_\beta,\mathcal D(\mathbf R^m)}. \tag{5.3.2.4}
$$

(3) *For any $\phi\in\mathcal D(\mathbf R^m)$ of the form $\phi=\psi_1\otimes\psi_2$ with $\psi_1\in\mathcal D(\mathbf R^{\lvert Z\rvert})$ and $\psi_2\in\mathcal D(\mathbf R^{m-\lvert Z\rvert})$, the identity in (5.3.2.4) reads:*

$$
\langle T,\phi\rangle_{\mathcal D(\mathbf R^m)'_\beta,\mathcal D(\mathbf R^m)}=\sum_{\alpha\in\mathbf N^m:\lvert\alpha\rvert\le N}(\partial_{x_Z}^{\alpha_Z}\delta_0)(\psi_1)\cdot\langle\partial_{x_{Z^c}}^{\alpha_{Z^c}}T_\alpha,\psi_2\rangle_{\mathcal D(\mathbf R^{m-\lvert Z\rvert})'_\beta,\mathcal D(\mathbf R^{m-\lvert Z\rvert})}. \tag{5.3.2.5}
$$

(4) *For $T_\alpha\in\mathcal D(\mathbf R^{m-\lvert Z\rvert})'_\beta$ the distributions of order $N-\lvert\alpha\rvert$ from (1), we have:*

$$
T=\sum_{\alpha\in\mathbf N^m:\lvert\alpha\rvert\le N}(\partial_{x_Z}^{\alpha_Z}\delta_0)\otimes(\partial_{x_{Z^c}}^{\alpha_{Z^c}}T_\alpha). \tag{5.3.2.6}
$$

(5) *$T$ is tempered and so are the $T_\alpha$ from (5.3.2.6) and their derivatives, and (5.3.2.6) holds in $\mathcal S(\mathbf R^m)'_\beta$.*

Proof. (1) : The definition of $R_{H_Z}$ makes sense on $C^\infty(\mathbf R^m)$. The restriction to $H_Z$ of a smooth function on $\mathbf R^m$ is indeed smooth on $H_Z$, since $H_Z$ is a global smooth complete intersection in $\mathbf R^m$ defined as the vanishing locus of the coordinates $x_k:\mathbf R^m\to\mathbf R$ for $k\in Z$, and formation of the derivatives $\partial_{x_k}^{\alpha_k}$ for $k\in Z$ commutes with $R_{H_Z}$ on each $f\in C^\infty(\mathbf R^m)$.

For $\gamma,\gamma'\in\mathbf N^{m-\lvert Z\rvert}$, we define $\alpha:=(0,\gamma)\in\mathbf N^m$ and $\beta:=(0,\gamma')$, with $0$ denoting the origin in $\mathbf N^{\lvert Z\rvert}$. Then we have:

$$
\sup_{x\in H_Z}\lvert x_Z^{\gamma}\partial_{x_Z}^{\gamma'}f(x_Z,0)\rvert\le\sup_{x\in\mathbf R^m}\lvert x^\alpha\partial_x^\beta f(x)\rvert \tag{5.3.2.7}
$$

which implies that $R_{H_Z}(\mathcal S(\mathbf R^m))\subset\mathcal S(\mathbf R^{m-\lvert Z\rvert})$ and is continuous with respect to the Hausdorff locally convex topology on $\mathcal S(\mathbf R^m)$ and $\mathcal S(\mathbf R^{m-\lvert Z\rvert})$, since this is defined as being generated by the countable family of seminorms from (D.1.10.6).

## PDF page 246

**246** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

If $\phi\in\mathcal D(\mathbf R^m)$ is supported on the compact subset $K\subset\mathbf R^m$, then $R_{H_Z}(\phi)$ is smooth and it is supported on the compact subset $K_Z$ obtained as the compact image of $K$ under the continuous projection $\mathbf R^m\to H_Z$. In particular, $R_{H_Z}(\mathcal D(\mathbf R^m))\subset\mathcal D(\mathbf R^{m-\lvert Z\rvert})$.

The same estimate in (5.3.2.7) applied to $\gamma=0$ and to $f=\phi$ supported on $K$, implies that $R_{H_Z}$ is continuous as an operator $\mathcal D(\mathbf R^m)\to\mathcal D(\mathbf R^{m-\lvert Z\rvert})$.

(2) : This is [Hörm, Ch.II,§2.3,Thm.2.3.5,p.47].

(3) and (4) : If $\phi=\psi_1\otimes\psi_2$ with $\psi_1\in\mathcal D(\mathbf R^{\lvert Z\rvert})$ and $\psi_2\in\mathcal D(\mathbf R^{m-\lvert Z\rvert})$, then we have:

$$
\langle R'_{H_Z}(T_\alpha),\partial_x^\alpha\phi\rangle_{\mathcal D(\mathbf R^m)'_\beta,\mathcal D(\mathbf R^m)}=\langle T_\alpha,R_{H_Z}(\partial_x^\alpha\phi)\rangle_{\mathcal D(\mathbf R^m)'_\beta,\mathcal D(\mathbf R^m)} \tag{5.3.2.8}
$$

$$
=\langle T_\alpha,\delta_0(\partial_{x_Z}^{\alpha_Z}(\psi_1))\cdot\partial_{x_{Z^c}}^{\alpha_{Z^c}}\psi_2\rangle_{\mathcal D(\mathbf R^{m-\lvert Z\rvert})'_\beta,\mathcal D(\mathbf R^{m-\lvert Z\rvert})} \tag{5.3.2.9}
$$

$$
=\delta_0(\partial_{x_Z}^{\alpha_Z}(\psi_1))\cdot\langle T_\alpha,\partial_{x_{Z^c}}^{\alpha_{Z^c}}\psi_2\rangle_{\mathcal D(\mathbf R^{m-\lvert Z\rvert})'_\beta,\mathcal D(\mathbf R^{m-\lvert Z\rvert})} \tag{5.3.2.10}
$$

and hence, upon combining (5.3.2.8) with (5.3.2.4), we deduce that both (5.3.2.5) and (5.3.2.6) hold, since $\mathcal D(\mathbf R^{\lvert Z\rvert})\otimes\mathcal D(\mathbf R^{m-\lvert Z\rvert})\subset\mathcal D(\mathbf R^m)$ is sequentially dense by [Tre, Part III,Ch.39,Thm.39.2,p.406], hence dense.

(5) : Compactly supported distributions are tempered, and the continuous injective operator $\mathcal D(\mathbf R^m)\to\mathcal S(\mathbf R^m)$ is compatible with the dualities $\langle\mathcal D(\mathbf R^m),\mathcal D(\mathbf R^m)'_\beta\rangle$ and $\langle\mathcal S(\mathbf R^m),\mathcal S(\mathbf R^m)'_\beta\rangle$ (i.e. its adjoint $R_{H_Z}$ is strongly continuous, by [NB, Thm.8.11.3(d)]). It follows that (5.3.2.6) holds in $\mathcal S(\mathbf R^m)'_\beta$. $\square$

Remark 5.3.2.4. Note that $\mathcal D(\mathbf R^{\lvert Z\rvert})\otimes\mathcal D(\mathbf R^{m-\lvert Z\rvert})$ is indeed mapped onto a sequentially dense linear subspace of $\mathcal D(\mathbf R^m)$ under the canonical linear operator $\mathcal D(\mathbf R^{\lvert Z\rvert})\otimes\mathcal D(\mathbf R^{m-\lvert Z\rvert})\to\mathcal D(\mathbf R^m)$, by [Tre, Part III,Ch.39,Thm.39.2,p.406], but such operator only induces a linear topological isomorphism from the inductive tensor product of $\mathcal D(\mathbf R^{\lvert Z\rvert})$ and $\mathcal D(\mathbf R^{m-\lvert Z\rvert})$ onto $\mathcal D(\mathbf R^m)$, and not from their projective tensor product (nor injective, being this latter linearly and topologically isomorphic to the projective tensor product, as $\mathcal D(\mathbf R^{\lvert Z\rvert})$ is nuclear).

Theorem 5.3.2.5. *Let $T\in\mathcal S(\mathbf C)'_\beta$ be supported at $0\in\mathbf C$. Then there exists an integer $N\ge 0$, complex numbers $c_{k,k'}$ with $(k,k')\in\mathbf N^2$ such that $k+k'\le N$, such that, as elements of $\mathcal S(\mathbf C)'_\beta$, we have:*

$$
T=\sum_{\alpha\in\mathbf N^2,\lvert\alpha\rvert\le N}c_{k,k'}\partial_z^k\partial_{\bar z}^{k'}\delta_0. \tag{5.3.2.11}
$$

(1) *Let $\mathcal S_{00}(\mathbf C)$ be the closed subspace defined as $\bigcap_{(k,k')\in\mathbf N^2}\ker(\partial_z^k\partial_{\bar z}^{k'}\delta_0)$. The orthogonal in $\mathcal S(\mathbf C)'_\beta$ of $\mathcal S_{00}(\mathbf C)$ with respect to the duality $\langle\mathcal S(\mathbf C),\mathcal S(\mathbf C)'_\beta\rangle$ is a linear subspace of $\mathcal S(\mathbf C)'_\beta$ linearly isomorphic to the continuous dual on the quotient $\mathcal S(\mathbf C)/\mathcal S_{00}(\mathbf C)$, and, topologized with the strong topology on the continuous dual of the quotient, it is linearly and topologically isomorphic to the $\mathbf C$-linear space underlying the polynomial algebra $\mathbf C[X,Y]$ equipped with the finest locally convex topology, equivalently the topology induced by the family of seminorms $\{p_N\}_{N\ge 0}$ with:*

$$
p_N(\sum_{(k,k')\in\mathbf N^2,k+k'\le N}c_{k,k'}X^kY^{k'}):=\sup_{(k,k')\in\mathbf N^2,k+k'\le N}\lvert c_{k,k'}\rvert \tag{5.3.2.12}
$$

*the isomorphism being uniquely determined by the assignment $X^kY^{k'}\mapsto\frac{1}{k!(k')!}\partial_z^k\partial_{\bar z}^{k'}\delta_0$, and matching the degree of a polynomial with the finite order of the resulting distribution supported at $0\in\mathbf C$.*

(2) *The quotient $\mathcal S(\mathbf C)/\mathcal S_{00}(\mathbf C)$, equipped with the quotient topology, is linearly and topologically isomorphic to the $\mathbf C$-linear space underlying the formal power series algebra $\mathbf C[[X,Y]]$ equipped with the Hausdorff locally convex topology induced by the family of seminoms $\{q_N\}_{N\ge 0}$:*

$$
q_N(\sum_{(k,k')\in\mathbf N^2}c_{k,k'}X^kY^{k'}):=\sup_{(k,k')\in\mathbf N^2,k+k'\le N}\lvert c_{k,k'}\rvert \tag{5.3.2.13}
$$

*the isomorphism being defined by sending each $f\in\mathcal S(\mathbf C)'_\beta$ to the formal power series $\sum_{(k,k')\in\mathbf N^2}\frac{\partial_z^k\partial_{\bar z}^{k'}f(0)}{k!(k')!}X^kY^{k'}$.*

## PDF page 247

**5.3. WEIL’S PRINCIPAL VALUE OPERATORS** · **247**

Proof. We let $(x,y)$ be global smooth coordinates on $\mathbf R^2$ such that $(x,y)\mapsto z:=x+iy$ is an isomorphism $\mathbf R^2\to\mathbf C$ of Hausdorff locally compact abelian groups. In particular, it induces a linear topological isomorphism $\mathcal S(\mathbf C)\to\mathcal S(\mathbf R^2)$.

We have $2\partial_z=\partial_x-i\partial_y$ and $2\partial_{\bar z}=\partial_x+i\partial_y$ as continuous operators on $\mathcal S(\mathbf C)\simeq\mathcal S(\mathbf R^2)$.

We have $\delta_0=\delta_{0,x}\otimes\delta_{0,y}$, upon denoting $\delta_{0,x}:=R_{H_{x=0}}'(D_{0,x})$ and $\delta_{0,y}:=R_{H_{y=0}}'(D_{0,y})$, where $D_{0,x}$ denotes the evaluation at $x=0$ functional on $\mathcal S(\mathbf R)$, and similarly for $D_{0,y}$, and $R_{H_{x=0}}$ and $R_{H_{y=0}}$ are the continuous operators $\mathcal S(\mathbf R^2)\to\mathcal S(\mathbf R)$ from Theorem 5.3.2.3.

To see that indeed $\delta_0=\delta_{0,x}\otimes\delta_{0,y}$ in $\mathcal S(\mathbf C)'_\beta$, it is enough to test the identity on Schwartz-Bruhat functions on $\mathbf C$ pulled back from the lines $H_{x=0}$ and $H_{y=0}$. Let $f(x,y)=\psi_1(x)\otimes\psi_2(y)$ be any such function, as a function of $(x,y)\in\mathbf R^2$, with $\psi_k\in\mathcal S(\mathbf R)$ for $k=1,2$.

Then $\delta_0(f)=f(0,0)=\psi_1(0)\psi_2(0)=(\delta_{0,x}\otimes\delta_{0,y})(f)$. Since $\mathcal S(\mathbf R)\otimes\mathcal S(\mathbf R)\subset\mathcal S(\mathbf R^2)$ is dense by [Tre, Part III,Ch.51,Thm.51.6(51.3),p.530], we indeed have $\delta_0=\delta_{0,x}\otimes\delta_{0,y}$ in $\mathcal S(\mathbf R^2)'_\beta$.

We now let $T$ be a tempered distribution on $\mathbf C$ supported at the origin. We rename as $T$ its pull-back to $\mathcal S(\mathbf R^2)'_\beta$ along the isomorphism $\mathbf R^2\to\mathbf C$.

Then $T$ is of finite order $N\ge 0$. Indeed, let $K\subset\mathbf R^2$ be a compact subset with non-empty interior. If $0\in K$, then for any compact subset $K'\subset K$ with non-empty interior and any smooth compactly supported function $\rho_{K'}\in\mathcal D(\mathbf R^2)$ whose support is contained in $K'$ and contains $0$ in its interior, and such that it is identically $1$ on an open neighborhood of $0$, we have:

$$
\langle T,\phi\rangle_{\mathcal S(\mathbf R^2)'_\beta,\mathcal S(\mathbf R^2)}=\langle T,\rho_{K'}\cdot\phi\rangle_{\mathcal S(\mathbf R^2)'_\beta,\mathcal S(\mathbf R^2)}. \tag{5.3.2.14}
$$

Indeed, upon choosing a smooth compactly supported function $\rho$ supported over an open neighborhood of $K$ with compact closure, and whose value on $K$ is identically $1$, then $\rho-\rho_{K'}$ vanishes over an open neighborhood of $0\in\mathbf R^2$, and hence on its compact closure by continuity.

Since $T$ is supported at $0$, we have $\langle T,(\rho-\rho_{K'})\cdot\phi\rangle_{\mathcal S(\mathbf R^2)'_\beta,\mathcal S(\mathbf R^2)}=0$. This proves that (5.3.2.14) holds for all $\phi\in\mathcal D(\mathbf R^2)$.

Since $\mathcal D(\mathbf R^2)\subset\mathcal S(\mathbf R^2)$ is dense, then (5.3.2.14) holds for all $\phi\in\mathcal S(\mathbf R^2)$ by continuity of $T$. By [Horm, Ch.II,§2.1,Thm.2.1.5,p.35], $T$ is of finite order. We let $N\ge 0$ be its order.

By Theorem 5.3.2.3(4), there exist tempered distributions $T_{(k,k')}\in\mathcal S(\mathbf R)'_\beta$, with $k+k'\le N$, of order $N-k-k'$, and such that:

$$
T=\sum_{(k,k')\in\mathbf N^2,k+k'\le N}(\partial_x^k\delta_{0,x})\otimes(\partial_y^{k'}T_{(k,k')}) \tag{5.3.2.15}
$$

as elements of $\mathcal S(\mathbf R^2)'_\beta$. Since $T$ is supported at $0\in\mathbf R^2$, then each $T_{(k,k')}$ is supported at $0\in\mathbf R$, and it is of order $N-k-k'$. The support condition can be seen as follows. We let $\psi_{1,k}\in\mathcal D(\mathbf R)$ be such that the support of $\psi_{1,k}$ contains $0$ in its interior, and $\psi_{1,k}^{(j)}(0)=1$ for $j=k$ and vanishes for all integers $0\le j\le N$, $j\ne k$ (such $\psi_{1,k}$ indeed exists. For instance, we may define, for each integer $k>1$, $\phi_k(x):=\rho_{[-1,1]}(x)\cdot e^{x^k}$ for $\rho_{[-1,1]}$ a smooth compactly supported function whose support is contained in $[-1,1]$ and which is identically $1$ over $[-1/2,1/2]$. Then $\phi_k^{(j)}(0)=0$ for all integers $1\le j\le k-1$, and is nonzero for $j=0,k$. For $k=1$, the same assignment $\phi_k$ satisfies $\phi_k^{(j)}(0)\ne 0$ for all integers $j\ge 0$, and for $k=0$, $\phi_k(0)\ne 0$ and $\phi_k^{(j)}(0)=0$ for all integers $j>0$. This shows that the closed subspace of Schwartz functions vanishing at $0$ with order of zero exactly $N$, has codimension exactly $N+1$. Equivalently, that $\{\delta_{0,x}^{(k)},0\le k\le N\}$, is a $\mathbf C$-linear independent subset of $\mathcal S(\mathbf R)'_\beta$).

We now let $\rho\in\mathcal D(\mathbf R)$ be supported within an open subset of $\mathbf R$ whose compact closure does not contain $0\in\mathbf R$. Then $\phi_k:=\psi_{1,k}\otimes\rho$ is supported on a compact subset contained within an open subset of the form $U_1\times U_2$, with $0\in U_1\subset\mathbf R$ and $0\notin U_2\subset\mathbf R$.

## PDF page 248

**248** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

We have $\langle T,\phi_k\rangle_{\mathcal D(\mathbf R^2)'_\beta,\mathcal S(\mathbf R^2)}=0$, and by (5.3.2.15) this identity gives

$$
\sum_{k'\in\mathbf N,0\le k'\le N-k}\langle\partial_y^{k'}T_{(k,k')},\rho\rangle_{\mathcal S(\mathbf R)'_\beta,\mathcal S(\mathbf R)}=0 \tag{5.3.2.16}
$$

for each $0\le k\le N$. We deduce that $T_{(N,k')}$ is supported at $0\in\mathbf R$ and is of order $0$. It follows that there exists a unique complex number $c_{(N,0)}$ such that $T_{(N,0)}=c_{(N,0)}\delta_{0,y}$.

Moreover, upon applying (5.3.2.16) with $k=N-1$, we deduce that $T-c_{(N,0)}(\partial_x^N\delta_{0,x})\otimes\delta_{0,y}-\sum_{k'=0,1}\partial_y^{k'}T_{(N-1,k')}$ is again supported at $0\in\mathbf R^2$, and that $T_{(N-1,0)}$ is supported at $0\in\mathbf R$ if and only if $T_{(N-1,1)}$ is.

Descending induction on $N\ge 0$ therefore reduces the assertion to the case $N=0$. If $T$ is of order $N=0$, then so is the unique $T_{(0,0)}$ satisfying (5.3.2.15), by Theorem 5.3.2.3. By testing $T$ on $\phi_0$, we deduce that $T_{(0,0)}$ is supported at $0\in\mathbf R$, and of order $0$. There therefore exists a complex number $c_{(0,0)}$ such that $T_{(0,0)}=c_{(0,0)}\cdot\delta_{0,y}$.

This shows that there exist unique complex numbers $c_{(k,k')}$ such that:

$$
T=\sum_{(k,k')\in\mathbf N^2,k+k'\le N}c_{(k,k')}(\partial_x^k\delta_{0,x})\otimes(\partial_y^{k'}\delta_{0,y}) \tag{5.3.2.17}
$$

$$
=\sum_{(k,k')\in\mathbf N^2,k+k'\le N}c_{(k,k')}\partial_x^k\partial_y^{k'}(\delta_{0,x}\otimes\delta_{0,y}) \tag{5.3.2.18}
$$

$$
=\sum_{(k,k')\in\mathbf N^2,k+k'\le N}c_{(k,k')}\partial_x^k\partial_y^{k'}\delta_0 \tag{5.3.2.19}
$$

as elements of $\mathcal S(\mathbf R^2)'_\beta$.

Upon evaluating on the identity in (5.3.2.17) the linear topological isomorphism $\mathcal S(\mathbf R^2)'_\beta\simeq\mathcal S(\mathbf C)'_\beta$ induced by $(x,y)\mapsto z:=x+iy$, we obtain (5.3.2.11).

(1) : Let $T\in\mathcal S(\mathbf C)'_\beta$ be a tempered distribution such that $T(\mathcal S_{00}(\mathbf C))=0$, i.e. an element of $\mathcal S_{00}(\mathbf C)^\perp\subset\mathcal S(\mathbf C)'_\beta$. Let $z\in\mathbf C$, $z\ne 0$. For any open neighborhood $U\subset\mathbf C$ of $z$ such that $0\notin U$, we let $\phi\in\mathcal D(\mathbf C)$ be supported within $U$.

Then $\phi\in\mathcal S_{00}(\mathbf C)$, and hence $T(\phi)=0$. It follows that $T$ is supported at $0$, and hence of the form as in (5.3.2.11). Conversely, every tempered distribution of the form as in (5.3.2.11) is an element of $\mathcal S_{00}(\mathbf C)^\perp$.

This shows that indeed the assignment $X^kY^{k'}\mapsto\frac{1}{k!(k')!}\partial_z^k\partial_{\bar z}^{k'}\delta_0$ is a linear isomorphism $\mathbf C[X,Y]\to\mathcal S_{00}(\mathbf C)^\perp$, and the degree $N$ of a monomial matches the order of the resulting tempered distribution supported at $0\in\mathbf C$.

The linear operator $\mathbf C[X,Y]\to\mathcal S_{00}(\mathbf C)^\perp$ is continuous, upon endowing the source with the finest locally convex topology, hence a continuous bijection.

The source is a strict LF-space, and the target is the strong dual of the nuclear Fréchet space $\mathcal S(\mathbf C)/\mathcal S_{00}(\mathbf C)$ (we refer the reader to [NB, Thm.8.12.1(a)] for the linear isomorphism between $\mathcal S(\mathbf C)/\mathcal S_{00}(\mathbf C)$ and $\mathcal S_{00}(\mathbf C)^\perp$).

We call $F:=\mathcal S(\mathbf C)/\mathcal S_{00}(\mathbf C)$ the quotient Fréchet space.

Since both $\mathcal S(\mathbf C)$ and $\mathcal S_{00}(\mathbf C)$ are nuclear Fréchet (the former by Proposition 2.1.1.6, the latter by [Scha, Ch.III,§7,Thm.7.4,p.103]), so is $F$ (by [Scha, Ch.III,§7,Thm.7.4,p.103], since $F$ is a separated quotient of a nuclear Fréchet space), and hence $F$ is Montel (see [Tre, Part III,Ch.50,Prop.50.2,(50.12),p.519]), hence reflexive (see [Jar, Part II,Ch.11,§11.5,Prop.1,p.11] and the subsequent discussion). It is, in fact, totally reflexive, because every quotient by a closed subspace of $F$ inherits nuclearity and is a Fréchet space, hence Montel, hence reflexive (alternatively, note that any nuclear Fréchet space is the countable projective limit of a sequence of separable Hilbert spaces; see [Scha, Ch.III,§7.3,Cor.3,p.103]).

The same argument as for the rest of (1) from Theorem 5.3.2.3(1), resting on the proof of the “only if” implication of [Val-a, §5,Thm.3,p.343], then applies, and gives that $F'_\beta$ is an LF-space.

## PDF page 249

**5.3. WEIL’S PRINCIPAL VALUE OPERATORS** · **249**

The continuous operator $\mathbf C[X,Y]\to F'_\beta$ is therefore a linear topological isomorphism by [Gro-f, Ch.4,§5,Thm.2(1),p.148] (see also [SN, §2,Cor.3,p.8]).

It follows that the composition of the linear topological isomorphisms $\mathbf C[X,Y]\to F'_\beta\simeq\mathcal S_{00}(\mathbf C)^\perp$, which is the linear operator $\mathbf C[X,Y]\to\mathcal S_{00}(\mathbf C)^\perp$, is indeed a linear topological isomorphism with respect to the stated topologies.

We further refer the reader to Lemma 4.2.1.3 for the equivalence between the strong topology on the continuous dual of $\mathcal S(\mathbf C)/\mathcal S_{00}(\mathbf C)$, and the subspace topology inherited from the strong topology on $\mathcal S(\mathbf C)'$.

(2) : We topologize $\mathcal S_{00}(\mathbf C)^\perp$ with the strong topology on the continuous dual of the quotient. The adjoint of the linear topological isomorphism $\mathbf C[X,Y]\to\mathcal S_{00}(\mathbf C)^\perp$ is the linear operator sending $f\in\mathcal S(\mathbf C)$ to its Taylor expansion at $z=0$ as a formal power series, i.e. $\sum_{(k,k')\in\mathbf N^2,k+k'\le N}\frac{\partial_z^k\partial_{\bar z}^{k'}f(0)}{k!(k')!}X^kY^{k'}$. This assignment is well-defined modulo $\mathcal S_{00}(\mathbf C)$, since the coefficients $\partial_z^k\partial_{\bar z}^{k'}f(0)$ all vanish for every $f\in\mathcal S_{00}(\mathbf C)$, and hence it indeed induces a linear operator $\mathcal S(\mathbf C)/\mathcal S_{00}(\mathbf C)\to\mathbf C[[X,Y]]$.

To show that it is a linear topological isomorphism with respect to the topology induced on $\mathbf C[[X,Y]]$ by the countable family of seminorms defined in (5.3.2.13), by [NB, Thm.8.13.5] it is enough to show that this is a Hausdorff locally convex topology such that $(\mathbf C[[X,Y]])'_\beta$ is linearly and topologically isomorphic to $\mathbf C[X,Y]$ equipped with the finest locally convex topology. This follows from [Tre, Part II,Ch.22,Thm.22.1(b),p.228]. $\square$

**5.3.3. Smoothness and rapid decay of extensions by zero.** We recall that we defined, in Definition D.3.3.1 of §D.3 from Appendix D, the Hausdorff locally convex topological $\mathbf C$-vector spaces $\mathcal S_I(G)$ of Schwartz-Bruhat functions on a Hausdorff locally compact $\mathbf R_{>0}$-modulated abelian group $G$ with $I$-exponential decay, for $I\subset\mathbf R$ a non-empty connected interval.

These are functions $f:G\to\mathbf C$ such that $\lvert\cdot\rvert_G^a f\in\mathcal S(G)$ for every $a\in I$.

Example 5.3.3.1. Recall from Definition D.2.1.1 that a Hausdorff locally compact abelian group $G$ is modulated if it is equipped with a continuous proper homomorphism $\lvert\cdot\rvert_G:G\to\mathbf R_{>0}$ whose kernel $G^1$ is (therefore) a compact Hausdorff abelian subgroup. $G$ is $\mathbf R_{>0}$-modulated if $\lvert\cdot\rvert_G$ is surjective.

To fix ideas, the reader may consider the case $G=\mathbf R_{>0}$, with $\lvert\cdot\rvert_G$ the identity homomorphism, in which case $f:G\to\mathbf C$ has $I$-exponential decay if and only if $t^a f(t)\in\mathcal S(\mathbf R_{>0})$. Upon performing the change of variables $t=e^x$, i.e. upon defining the module homomorphism $\lvert x\rvert_{\mathbf R}:=e^x$, then $\mathcal S_I(\mathbf R)$ is the $\mathbf C$-linear space of smooth functions $f:\mathbf R\to\mathbf C$ such that $e^{ax}f(x)$ decays faster than any positive power of $\lvert x\rvert^{-1}$ as $\lvert x\rvert\to+\infty$ for every $a\in I$, hence the lexicon “$I$-exponential decay”. $\mathcal S_{\log(I)}(\mathbf R)$ is linearly and topologically isomorphic to $\mathcal S_I(\mathbf R_{>0})$ with the above module homomorphisms.

We refer the reader to Theorem D.3.3.7 for the properties of the Hausdorff locally convex topology on $\mathcal S_I(G)$.

We will now use only the special cases $G=\mathbf R^\times,\mathbf C^\times$, and $I=(0,+\infty)$, respectively $I=[-m,+\infty)$ for each integer $m\ge 0$.

We note that we have injective continuous linear inclusions $\mathcal S(\mathbf R)\to\mathcal S_{(0,+\infty)}(\mathbf R^\times)$ and $\mathcal S(\mathbf C)\to\mathcal S_{(0,+\infty)}(\mathbf C^\times)$.

Proposition 5.3.3.2. Let $m\ge 0$ be an integer. Then:

(1) *pointwise multiplication by $x$, respectively $z,\bar z$, denoted $M_x$, respectively $M_z,M_{\bar z}$, is a bounded linear operator on $\mathcal D(\mathbf R^\times)$, $\mathcal S_{[a,+\infty)}(\mathbf R^\times)$ for any $a\in\mathbf R\cup\{-\infty\}$, respectively $\mathcal D(\mathbf C^\times)$, $\mathcal S_{[a,+\infty)}(\mathbf C^\times)$ for any $a\in\mathbf R\cup\{-\infty\}$, and it is boundedly invertible on $\mathcal D(\mathbf R^\times)$, $\mathcal S_{(-\infty,+\infty)}(\mathbf R^\times)$, respectively $\mathcal D(\mathbf C^\times)$, $\mathcal S_{(-\infty,+\infty)}(\mathbf C^\times)$.*

(2) Let $m\ge 0$ be an integer.

(1) *$\partial_x^m:=(M_x^{-1}\circ(x\partial_x))^m$ is a continuous linear endomorphism on $\mathcal D(\mathbf R^\times)$ with closed range. It extends to a continuous operator on $\mathcal S_{(a,+\infty)}(\mathbf R^\times)$ valued in $\mathcal S_{(a+m,+\infty)}(\mathbf R^\times)$ for every real number $a$, and induces a continuous linear endomorphism of $\mathcal S_{(-\infty,+\infty)}(\mathbf R^\times)$.*

## PDF page 250

**250** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

*For each $\phi\in\mathcal S_{(0,+\infty)}(\mathbf R^\times)$, $\phi$ is a smooth function on $\mathbf R^\times$ (i.e. on $\mathbf R^\times$ as an open subset of $\mathbf R$), and $\partial_x\phi$ is computed pointwise by the ordinary derivative of $\phi$ as a smooth function on $\mathbf R^\times\subset\mathbf R$.*

(2) *$\partial_z:=M_z^{-1}\circ(z\partial_z)$, $\partial_{\bar z}:=M_{\bar z}^{-1}\circ(\bar z\partial_{\bar z})$ are continuous linear endomorphisms on $\mathcal D(\mathbf C^\times)$ with closed range.*

*$\partial_z$ and $\partial_{\bar z}^m$ extend to continuous operators on $\mathcal S_{(a,+\infty)}(\mathbf C^\times)$ valued $\mathcal S_{(a+m,+\infty)}(\mathbf C^\times)$ for every real number $a<0$, and induce continuous linear endomorphisms on $\mathcal S_{(-\infty,+\infty)}(\mathbf C^\times)$.*

*For each $\phi\in\mathcal S_{(0,+\infty)}(\mathbf C^\times)$, $\phi$ is a smooth function over $\mathbf C^\times$ (i.e. on $\mathbf C^\times$ as an open domain of the complex plane), and $\partial_z\phi$ and $\partial_{\bar z}\phi$ are computed pointwise by the ordinary holomorphic, respectively anti-holomorphic, derivatives of $\phi$ as a smooth function on $\mathbf C^\times\subset\mathbf C$.*

Proof. (1) : Multiplication by $x$ is bounded and boundedly invertible on $\mathcal D(\mathbf R^\times)$.

Indeed, since $\mathbf R^\times$ and $\mathbf C^\times$ are abelian Lie groups, we topologize $\mathcal D(\mathbf R^\times)$ and $\mathcal D(\mathbf C^\times)$ with the strict locally convex inductive limit topology of the Fréchet space topologies on $\mathcal D_K(\mathbf R^\times)$, respectively $\mathcal D_K(\mathbf C^\times)$ (see also [Sch-a, Ch.III,§1,Thm.II,p.66], for a direct definition using a separating family of seminorms, for then identifying the resulting locally convex topology with the strict locally convex inductive limit).

We further refer the reader to [Fol, Ch.9,§9.1,p.282].

All the results on the Hausdorff locally convex topological vector space $\mathcal D(\mathbf R^m)$ from [Sch-a, Ch.III,§1] apply to $\mathcal D(\mathbf R^\times)$ and $\mathcal D(\mathbf C^\times)$.

By [Sch-a, Ch.III,§1,Thm.IV,p.69], for $B\subset\mathcal D(\mathbf R^\times)$ a bounded subset, there exists a compact subset $K\subset\mathbf R^\times$ and a bounded subset $B_0\subset\mathcal D_K(\mathbf R^\times)$ such that $B$ is the image of $B_0$ under the linear topological embedding $\mathcal D_K(\mathbf R^\times)\to\mathcal D(\mathbf R^\times)$.

If $\varphi\in\mathcal D_K(\mathbf R^\times)$, then $M_x(\varphi)$ is the function $x\varphi(x)$ on $\mathbf R^\times$, and it is still compactly supported with support contained in $K$, i.e. $M_x$ preserves the subspaces $\mathcal D_K(\mathbf R^\times)$. It is therefore enough to show that $M_x$ is bounded and boundedly invertible on $\mathcal D_K(\mathbf R^\times)$, for $K\subset\mathbf R^\times$ an arbitrary compact subset with non-empty interior.

A similar reduction is valid for $M_z$ and $M_{\bar z}$ on $\mathcal D(\mathbf C^\times)$, being the Hausdorff locally convex topology on $\mathcal D(G)$ for $G$ an abelian Lie group, the strict inductive limit of the topologies on each $\mathcal D_K(G)$, for $K\subset G$ a compact subset with non-empty interior.

For any $\varphi\in B_0$, we have

$$
\sup_{x\in K}\lvert\partial_x^m(x\varphi(x))\rvert\le\sup_{x\in K}\lvert x\partial_x^m\varphi(x)\rvert+\sup_{x\in K}\lvert\partial_x^{m-1}\varphi(x)\rvert\le\sup_{x\in K}\lvert x\rvert\cdot\lVert\varphi^{(m)}\rVert_u+\lVert\varphi^{(m-1)}\rVert_u
$$

and hence $M_x$ is bounded on $\mathcal D_K(\mathbf R^\times)$. Similarly, $M_z$ and $M_{\bar z}$ are both bounded on $\mathcal D_K(\mathbf C^\times)$ for any compact subset $K\subset\mathbf C^\times$ with non-empty interior. By [NB, Thm.6.5.2] (see also [Scha, Ch.II,§8.3,p.62]), $M_x$, $M_z$ and $M_{\bar z}$ are continuous.

They are therefore all bounded and continuous (by [NB, Thm.13.2.7]) linear endomorphisms on $\mathcal D(\mathbf R^\times)$, respectively $\mathcal D(\mathbf C^\times)$.

Since they are surjective, then by Köthe’s Open Mapping Theorem (see [Gro-f, Ch.4,§5,Thm.2(1),p.148], and [SN, §2,Cor.3,p.8]) they are linear topological automorphisms, being their source and target (strict) LF-spaces.

(2) : Let $\{f_i\}_{i\in I}\subset\mathcal D(\mathbf R^\times)$ be a net in $\mathcal D(\mathbf R^\times)$ converging to $f$. By [Sch-a, Ch.III,§2,Thm.IV,p.69] we may and do assume that there exists a compact subset $K\subset\mathbf R^\times$ such that $\{f_i\}_{i\in I}\cup\{f\}\subset\mathcal D_K(\mathbf R^\times)$, since, up to replacing the directed set $I$ with a subset of the form $I_0:=\{i\in I:i\ge i_0\}$ for some $i_0\in I$, and renaming $I_0$ as $I$, we may assume that $\{f_i\}_{i\in I}$ is a bounded subset in $\mathcal D(\mathbf R^\times)$, being a Cauchy net (see [NB, Thm.3.4.2]. Cauchy nets are not necessarily eventually bounded,$^8$ since for any $0$-neighborhood $V$ there exists $i_0\in I$ such that $f_i-f_j\in V$ for all $i,j\ge i_0$, and hence upon choosing $i_1\ge i_0$, we have, for all $i,j\ge i_1$ that $f_i\in f_{i_1}+V$ holds, and $\{f_i\}_{i\in I,i\ge i_1}$ is bounded.

---

$^8$Return here.

## PDF page 251

**5.3. WEIL’S PRINCIPAL VALUE OPERATORS** · **251**

Since $\mathcal D_K(\mathbf R^\times)$ is a Fréchet space, there exists a cofinal sequence of elements of $I$ such that the resulting sequence $\{F_n:=f_{i_n}\}_{n\ge 0}$ converges to $f$ in $\mathcal D_K(\mathbf R^\times)$. If each $f_i$ is of the form $x\partial_x u_i$ for some $u_i\in\mathcal D(\mathbf R^\times)$, then since each $u_i$ is compactly supported, we must have $u_i\in\mathcal D_K(\mathbf R^\times)$, since $f\in\mathcal D_K(\mathbf R^\times)$ (and hence $u_i$ is constant away from the support of $f$, which forces the support of $u_i$ to be contained in $K$).

We have

$$
\partial_x^N\int_0^x F_n(y)\,\frac{\mathrm{d}y}{y}\to\partial_x^N\int_0^x f(y)\,\frac{\mathrm{d}y}{y}
$$

by Dominated Convergence, since $F_n\to f$ in $\mathcal D_K(\mathbf R^\times)$, the mode of convergence being uniform over $K$ for each integer $N\ge 0$, and hence $u_{i_n}$ converges to some $u\in\mathcal D_K(\mathbf R^\times)$ (see [Sch-a, Ch.III,§1,p.64]), and $\partial_x u=f/x$.

It follows that $f=x\partial_x u$, i.e. $f$ is in the range of $x\partial_x$. A similar argument shows that $z\partial_z$ and $\bar z\partial_{\bar z}$ both have closed range in $\mathcal D(\mathbf C^\times)$.

Since $M_x$, $M_z$ and $M_{\bar z}$ are linear topological automorphisms, they have closed range, and hence the continuous linear operators $\partial_x$, $\partial_z$ and $\partial_{\bar z}$ also have closed range.

Continuity of the operators $M_{x^{-1}}:\mathcal S_{(a,+\infty)}(\mathbf R^\times)\to\mathcal S_{(a+1,+\infty)}(\mathbf R^\times)$ and $M_{z^{-1}},M_{\bar z^{-1}}:\mathcal S_{(a,+\infty)}(\mathbf C^\times)\to\mathcal S_{(a+1,+\infty)}(\mathbf C^\times)$ follows from the design of the Hausdorff locally convex topology on sources and targets (see Definition D.3.3.1), which, recall, is the projective topology on $\mathcal S_I(G)$, $G$ a Hausdorff locally compact abelian group, $I\subset\mathbf R$ a non-empty connected interval, induced by the family of operators $T_a:\mathcal S_I(G)\to\mathcal S(G)$ sending $\phi\in\mathcal S_I(G)$ to $\lvert\cdot\rvert_G^a\cdot\phi$, with $\lvert\cdot\rvert_G$ the module of the modulated group $G$.

For $G=\mathbf R^\times$, then if $f_i\to f$ is a convergent $J$-indexed net in $\mathcal S_{(a,+\infty)}(\mathbf R^\times)$, $\{M_{x^{-1}}(f_i)\}_{i\in J}$ is contained in $\mathcal S_{(a+1,+\infty)}(\mathbf R^\times)$, and $T_b(M_{x^{-1}}(f_i))$ is, for each $i\in J$ and as a function of $x\in\mathbf R^\times$, $x\mapsto\lvert x\rvert^b\cdot x^{-1}f_i(x)$, which is Schwartz-Bruhat on $\mathbf R^\times$ since $x=\mathrm{sgn}(x)\lvert x\rvert$, and multiplication by unitary characters is continuous on $\mathcal S(\mathbf R^\times)$.

It follows that $T_b(M_{x^{-1}}(f_i))\to T_b(M_{x^{-1}}(f))$ for every $b>a+1$, i.e. $M_{x^{-1}}$ is continuous on $\mathcal S_{(a,+\infty)}$ and valued in $\mathcal S_{(a+1,+\infty)}$. A similar argument shows the same property holds for $M_{z^{-1}}$ and $M_{\bar z^{-1}}$ on $\mathcal S_{(a,+\infty)}(\mathbf C^\times)$.

Since $x\partial_x$, $z\partial_z$ and $\bar z\partial_{\bar z}$ are all continuous endomorphisms of $\mathcal S_{(a,+\infty)}(\mathbf R^\times)$, respectively $\mathcal S_{(a,+\infty)}(\mathbf C^\times)$ for any $a\in\mathbf R$, since they are continuous differential operators on $\mathcal S(\mathbf R^\times)$ respectively $\mathcal S(\mathbf C^\times)$, and by design of the Hausdorff locally convex topology on $\mathcal S_{(a,+\infty)}(\mathbf R^\times)$, respectively $\mathcal S_{(a,+\infty)}(\mathbf C^\times)$, the remaining assertions on $\partial_x^m$, $\partial_z^m$ and $\partial_{\bar z}^m$ follow by composition.

For each $y\in\mathbf R^\times$, and $\phi\in\mathcal S_{(a,+\infty)}(\mathbf R^\times)$, for $a\in\mathbf R$ a real number, we note that the limit:

$$
\lim_{x\to 1}\frac{\phi(x^{-1}y)-\phi(y)}{x^{-1}-1} \tag{5.3.3.1}
$$

exists and is finite, and its formation is continuous as a function of $y\in\mathbf R^\times$ because $\lvert\cdot\rvert_{\mathbf R}^a\phi\in\mathcal S(\mathbf R^\times)$.

Indeed, the limit:

$$
\lim_{x\to 1}\frac{\lvert x^{-1}y\rvert_{\mathbf R}^b\phi(x^{-1}y)-\lvert y\rvert_{\mathbf R}^a\phi(y)}{x^{-1}-1} \tag{5.3.3.2}
$$

exists since it is performed along a continuous multiplicative $1$-parameter subgroup of $\mathbf R^\times$, and $\lvert\cdot\rvert_{\mathbf R}^b\phi\in\mathcal S(\mathbf R^\times)$ for any $b>a$. It equals:

$$
\lvert y\rvert_{\mathbf R}^b\lim_{x\to 1}\frac{\lvert x^{-1}\rvert_{\mathbf R}^b\cdot\phi(x^{-1}y)-\phi(y)}{x^{-1}-1} \tag{5.3.3.3}
$$

which in turn equal the sum of $\lvert y\rvert_{\mathbf R}^b\lim_{x\to 1}\frac{\lvert x^{-1}\rvert_{\mathbf R}^a-1}{x^{-1}-1}\phi(x^{-1}y)$, and the limit in (5.3.3.1) (multiplied by $\lvert y\rvert_{\mathbf R}^b$) which therefore also exists, since the former does upon choosing $b>1$ (which we can do since $\phi\in\mathcal S_{(a,+\infty)}$. The limit in (5.3.3.1) therefore exists, it is finite, and it equals:

$$
y\lim_{x\to 1}\frac{\phi(x^{-1}y)-\phi(y)}{x^{-1}y-y} \tag{5.3.3.4}
$$

## PDF page 252

**252** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

and hence at each $y\in\mathbf R^\times$ the limit $\lim_{x\to 1}\frac{\phi(x^{-1}y)-\phi(y)}{x^{-1}y-y}$, equivalently (since $\phi$ is continuous on $\mathbf R^\times$) $\lim_{y'\to y}\frac{\phi(y')-\phi(y)}{y'-y}$, exists and is finite, and its formation is continuous as a function of $y\in\mathbf R^\times$, since $y$ is nowhere vanishing and continuous away from $0\in\mathbf R$.

We deduce that any $\phi\in\mathcal S_{(a,+\infty)}(\mathbf R^\times)$ is smooth on $\mathbf R^\times$ as a function on a non-empty open subset of the real line. A similar argument applies to $\mathcal S_{(a,+\infty)}(\mathbf C^\times)$, and we deduce that the operators $\partial_x$, $\partial_z$ and $\partial_{\bar z}$ are computed pointwise on functions by the ordinary smooth, holomorphic and anti-holomorphic derivatives, respectively.

(Note that continuity of $z\partial_z$ and $\bar z\partial_{\bar z}$, using which the same argument in the foregoing to establish continuity of $\partial_x$ and compute it pointwise, carries over to $\partial_z$ and $\partial_{\bar z}$, can also be seen on $\mathcal S(\mathbf C^\times)$ as follows: upon writing $z=re^{i\theta}$ in polar coordinates, from which we have $\partial_z=\frac{e^{-i\theta}}{2}(\partial_r-iM_{r^{-1}}\partial_\theta)$, and by Theorem D.3.3.7(3), it is enough to show continuity of $\partial_\theta$ on $\mathcal S(\mathrm U(1))$, which holds since $\partial_\theta$ is the directional derivatives along the $1$-parameter subgroup $\exp(i\theta):\mathbf R\to\mathrm U(1)$, and use continuity of $\partial_x$, which we established in the foregoing). $\square$

Lemma 5.3.3.3. *Let $p,q\ge 0$ be integers, and $I\subset\mathbf R$ an open connected non-empty interval. We call $(x_k)_{1\le k\le p}$ a choice of global smooth coordinates on $\mathbf R^p$, and $\{(z_m,\bar z_m)\}_{1\le m\le q}$ a choice of global holomorphic and anti-holomorphic coordinates on $\mathbf C^q$.*

*We denote by $\lvert\cdot\rvert_{r,k}$ the real absolute value on the $k$th factor in $\mathbf R^p$, and $\lvert\cdot\rvert_{c,m}$ the square of the Euclidean norm on the $m$th factor in $\mathbf C^q$.*

*We denote, for $\underline k\subset\{1,\dots,p\}$ and $\underline m\subset\{1,\dots,q\}$ totally ordered subsets, and for $(\underline a,\underline b)\in I^{\lvert\underline k\rvert}\times I^{\lvert\underline m\rvert}$:*

$$
\lvert\cdot\rvert_{\underline k,\underline m}^{\underline a,\underline b}:=\prod_{1\le k\le p}\lvert\cdot\rvert_{r,k}^{a_k}\cdot\prod_{1\le m\le q}\lvert\cdot\rvert_{c,m}^{b_m}:(\mathbf R^\times)^p\times(\mathbf C^\times)^q\to\mathbf R_{>0}. \tag{5.3.3.5}
$$

We define

$$
\mathcal S_{I^{p+q}}((\mathbf R^\times)^p\times(\mathbf C^\times)^q) \tag{5.3.3.6}
$$

*to be the linear subspace of $\mathcal S((\mathbf R^\times)^p\times(\mathbf C^\times)^q)$ of those Schwartz-Bruhat functions $\phi$ on $(\mathbf R^\times)^p\times(\mathbf C^\times)^q$ such that*

$$
\lvert\cdot\rvert_{\underline k,\underline m}^{\underline a,\underline b}\cdot\phi\in\mathcal S((\mathbf R^\times)^p\times(\mathbf C^\times)^q) \tag{5.3.3.7}
$$

*endowing $\mathcal S_{I^{p+q}}((\mathbf R^\times)^p\times(\mathbf C^\times)^q)$ with the projective topology induced by the linear operators*

$$
T_{(\underline k,\underline m),(\underline a,\underline b)}:\mathcal S_{I^{p+q}}((\mathbf R^\times)^p\times(\mathbf C^\times)^q)\to\mathcal S((\mathbf R^\times)^p\times(\mathbf C^\times)^q) \tag{5.3.3.8}
$$

defined by $T_{(\underline k,\underline m),(\underline a,\underline b)}(\phi):=\lvert\cdot\rvert_{\underline k,\underline m}^{\underline a,\underline b}\cdot\phi$.

Then:

(1) $\mathcal S_{I^{p+q}}((\mathbf R^\times)^p\times(\mathbf C^\times)^q)$ is a separable nuclear Fréchet space.

(2) the canonical linear map:

$$
\mathcal S_I(\mathbf R^\times)^{\otimes_\pi^p}\otimes_\pi\mathcal S_I(\mathbf C^\times)^{\otimes_\pi^q}\to\mathcal S_{I^{p+q}}((\mathbf R^\times)^p\times(\mathbf C^\times)^q) \tag{5.3.3.9}
$$

*is a linear topological embedding, inducing a linear topological isomorphism from the completion of the source.*

(3) We define:

$$
\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)\subset\mathcal S(\mathbf R^p\times\mathbf C^q) \tag{5.3.3.10}
$$

*the closed linear subspace of those Schwartz functions $f\in\mathcal S(\mathbf R^p\times\mathbf C^p)$ such that all partial derivatives with respect to the $p$ smooth coordinates, and all holomorphic and anti-holomorphic derivatives with respect to the $q$ complex coordinates, of any order, vanish on each of the hyperplanes $x_k=0$, $z_m=0$, for each $1\le k\le p$, $1\le m\le q$.*

## PDF page 253

**5.3. WEIL’S PRINCIPAL VALUE OPERATORS** · **253**

*If $I = (-\infty, +\infty)$, then the canonical linear restriction operator $\mathcal{S}_{00}(\mathbf{R}^{p} \times \mathbf{C}^{q}) \to \mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})$ is continuous and a linear topological isomorphism. In particular, multiplication by any continuous quasi-character of $(\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q}$ extends uniquely to a bounded and boundedly invertible automorphism of $\mathcal{S}_{00}(\mathbf{R}^{p} \times \mathbf{C}^{q})$, which, on functions and pointwise over the open subset $(\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q} \subset \mathbf{R}^{p} \times \mathbf{C}^{q}$, is computed by pointwise multiplication of smooth functions.*

PROOF. (1) : We begin by observing that, as in the proof of Lemma D.3.2.3(1), the Hausdorff locally convex topology on $\mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})$ is equivalent to the projective topology induced by a subfamily of the operators $T_{(\underline{k},\underline{m}),(\underline{a},\underline{b})}$: it is enough to assume $(\underline{a},\underline{b})$ vary over $\mathbf{Z}^{\lvert\underline{k}\rvert} \times \mathbf{Z}^{\lvert\underline{m}\rvert}$.

In particular, the operator:

$$
T : \mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q}) \to \prod_{(\underline{a},\underline{b}) \in \mathbf{Z}^{\lvert\underline{k}\rvert} \times \mathbf{Z}^{\lvert\underline{m}\rvert}} \prod_{(\underline{k},\underline{m})} \mathcal{S}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q}) \tag{5.3.3.11}
$$

induced by the $T_{(\underline{k},\underline{m}),(\underline{a},\underline{b})}$ from (5.3.3.8), is a linear topological embedding with closed range (see the proof of Lemma D.3.2.3(2)).

Since countable products of complete metrizable Hausdorff locally convex spaces are complete metrizable and Hausdorff by [Scha, Ch.I,§6,p.30] and [Scha, Ch.II,§5,5.3,p.52], the target Hausdorff locally convex topological $\mathbf{C}$-vector space in (5.3.3.11) is a Fréchet space (separable, since the product is countable and each factor is $\mathcal{S}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})$, which is a separable Fréchet space), so is the source, i.e. $\mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})$, since it is a closed subspace of a separable Fréchet space.

Nuclearity is inherited by subspaces and arbitrary products of nuclear Hausdorff locally convex topological $\mathbf{C}$-vector spaces are nuclear (see [Scha, Ch.III,§7,Thm.7.4,p.103]), proving nuclearity of $\mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})$.

(2) : We prove that the canonical linear map:

$$
\mathcal{S}_{I}(\mathbf{R}^{\times})^{\otimes_{\pi}^{p}} \otimes_{\pi} \mathcal{S}_{I}(\mathbf{C}^{\times})^{\otimes_{\pi}^{q}} \to \mathcal{S}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q}) \tag{5.3.3.12}
$$

is continuous with respect to the projective tensor product topology on the source, and induces a linear topological isomorphism from the completion, where each $\mathbf{R}^{\times}$ is modulated by $\lvert\cdot\rvert_{r,k}$, and each $\mathbf{C}^{\times}$ is modulated by $\lvert\cdot\rvert_{c,k}$, onto the linear subspace

$$
\mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})
$$

of those Schwartz-Bruhat functions $\phi((x_{k}), (z_{m}))$ such that $\prod_{1 \le k \le p}\lvert\cdot\rvert_{r,k}^{a_{k}} \cdot \prod_{1 \le m \le q}\lvert\cdot\rvert_{c,m}^{b_{m}} \cdot \phi \in \mathcal{S}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})$ for all $a_{k}, b_{m} \in I$ and all $1 \le k \le p$ and $1 \le m \le q$.

By [Jar, Part III,Ch.15,§15.1,Rem.6(b),p.326] and [Jar, Part III,Ch.15,§15.2,Cor.4,p.328], formation of the projective tensor product topology is associative on finitely many tensor factors, and stable under arbitrary permutations of finitely many tensor factors.

By Theorem D.3.3.7(3), upon choosing a continuous homomorphic section $\tau_{r}$ and $\tau_{r}$ to the real Euclidean, respectively to the complex, absolute values, we have linear topological isomorphisms:

$$
\mathcal{S}_{I}(\mathbf{R}^{\times}) \simeq \mathcal{S}(\{\pm 1\}) \,\widehat{\otimes}_{\pi}\, \mathcal{S}_{I}(\mathbf{R}_{>0}), \quad \mathcal{S}_{I}(\mathbf{C}^{\times}) \simeq \mathcal{S}(\mathrm{U}(1)) \,\widehat{\otimes}_{\pi}\, \mathcal{S}_{I}(\mathbf{R}_{>0}). \tag{5.3.3.13}
$$

The same argument as for the proof of Lemma D.2.2.2(1), shows that the canonical linear map:

$$
\mathcal{S}(\{\pm 1\}^{p} \times \mathrm{U}(1)^{q}) \otimes_{\pi} \mathcal{S}_{I^{p+q}}(\mathbf{R}_{>0}) \to \mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q}) \tag{5.3.3.14}
$$

is continuous and induces a linear topological isomorphism from the completion of the source. We note that indeed the argument from the proof of Lemma D.2.2.2(1) carries over, because the Hausdorff locally convex spaces $\mathcal{S}(\{\pm 1\}^{p}) \simeq \mathbf{C}^{2p}$, $\mathcal{S}(\mathrm{U}(1)^{q})$, and $\mathcal{S}_{I^{p+q}}(\mathbf{R}_{>0})$, are nuclear Fréchet, and Proposition C.2.3.11 can be accessed as in the proof of Lemma D.2.2.2(1), to show continuity of the linear operator from (5.3.3.14).

However, since $\mathcal{S}(\{\pm 1\})$ and $\mathcal{S}(\mathrm{U}(1)^{q})$ are also Fréchet spaces, the argument from [Tre, Part III,Ch.51,Thm.51.6,p.531] also carries over (the key difference is that since all tensor factors and the target are sequential, separate continuity of bi-linear forms from the product of two Fréchet spaces into an arbitrary Hausdorff locally convex

## PDF page 254

**254** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

topological $\mathbf{C}$-vector space, is sufficient for continuity to hold; see [Bou-TVS, Ch.III,§5,Cor.1,TVS III.30]. Lemma D.2.2.2 allows $\mathcal{S}(G^{1})$ to be only an LF-space, hence not necessarily metrizable).

We further refer the reader to the argument for Theorem D.3.3.7(3).

The following diagram of continuous linear operators:

(5.3.3.15)

```latex
\begin{tikzcd}
\mathcal{S}(\{\pm 1\})^{\widehat{\otimes}_{\pi}^{p}} \widehat{\otimes}_{\pi} \mathcal{S}(\mathrm{U}(1))^{\widehat{\otimes}_{\pi}^{q}} \widehat{\otimes}_{\pi} \mathcal{S}_{I}(\mathbf{R}_{>0})^{\widehat{\otimes}_{\pi}^{p+q}} \arrow[r] \arrow[d] & \mathcal{S}_{I}(\mathbf{R}^{\times})^{\widehat{\otimes}_{\pi}^{p}} \widehat{\otimes}_{\pi} \mathcal{S}_{I}(\mathbf{C}^{\times})^{\widehat{\otimes}_{\pi}^{q}} \arrow[d] \\
\mathcal{S}(\{\pm 1\}^{p} \times \mathrm{U}(1)^{q}) \,\widehat{\otimes}_{\pi}\, \mathcal{S}_{I^{p+q}}(\mathbf{R}_{>0}^{p+q}) \arrow[r] & \mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})
\end{tikzcd}
```

commutes, and we have shown that the bottom horizontal arrow is a linear topological isomorphism.

By Lemma D.1.8.1, combined with [Jar, Part III,Ch.16,§16.2,Cor.3,p.348], which applies since the tensor factors are nuclear by Theorem D.1.5.7 and, for $\mathcal{S}_{I^{p+q}}(\mathbf{R}_{>0}^{p+q})$, by the same argument as in part (1), using nuclearity of $\mathcal{S}(\mathbf{R}_{>0}^{p+q})$ which is shown in Proposition 2.1.1.6 (see also [Tre, Part III,Ch.51,p.530,Corollary]), the leftmost vertical arrow is a linear topological isomorphism, so long as the canonical linear map:

$$
\mathcal{S}_{I}(\mathbf{R}_{>0})^{\otimes_{\pi}^{p+q}} \to \mathcal{S}_{I^{p+q}}(\mathbf{R}_{>0}^{p+q}) \tag{5.3.3.16}
$$

is continuous and induces a linear topological isomorphism from the completion of the source.

If so, then upon combining the linear topological isomorphisms from (5.3.3.13) with [Jar, Part III,Ch.16,§16.2,Cor.3,p.348], which applies by nuclearity of the tensor factors, the top horizontal arrow is also a linear topological isomorphism, which proves that so is the rightmost vertical arrow. This proves (2).

We are therefore reduced to showing that the canonical linear operator from (5.3.3.16) is continuous with respect to the projective tensor product topology on the source, and a linear topological embedding with dense range.

We rename $p+q$ as $p$, and treat the case $p=2$ for simplicity, being the general case established in a similar manner.

It is therefore enough to prove that the canonical linear map:

$$
\mathcal{S}_{I}(\mathbf{R}_{>0}) \otimes \mathcal{S}_{I}(\mathbf{R}_{>0}) \to \mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0}) \tag{5.3.3.17}
$$

with $\mathbf{R}_{>0}$ modulated by the standard Euclidean absolute value $\lvert\cdot\rvert_{r}$, is continuous with respect to the projective tensor product topology on the source, and it extends to a linear topological isomorphism from the completion.

The Hausdorff locally convex topology on $\mathcal{S}_{I}(\mathbf{R}_{>0})$ is the projective topology induced by the linear operators $T_{a} : \mathcal{S}_{I}(\mathbf{R}_{>0}) \to \mathcal{S}(\mathbf{R}_{>0})$ defined, for each $a \in I$, by $T_{a}(\phi) := \lvert\cdot\rvert_{r}^{a} \phi$ (see Definition D.3.3.1).

Equivalently, it is the topology induced by the unique linear map:

$$
T := \prod_{a \in I} T_{a} : \mathcal{S}_{I}(\mathbf{R}_{>0}) \to \prod_{a \in I} \mathcal{S}(\mathbf{R}_{>0}).
$$

By the description of the $0$-neighborhoods of the projective tensor product topology from [Jar, Part III,Ch.15,§15.1,p.324] (see also the discussion preceding (C.2.3.14)), and by [Jar, Part III,Ch.15,§15.4,Thm.1,p.332], the canonical linear map:

$$
(\prod_{a \in I} \mathcal{S}(\mathbf{R}_{>0})) \otimes_{\pi} (\prod_{a \in I} \mathcal{S}(\mathbf{R}_{>0})) \to \prod_{(a,b) \in I \times I} (\mathcal{S}(\mathbf{R}_{>0}) \otimes \mathcal{S}(\mathbf{R}_{>0}))
$$

is a linear topological embedding, and by [Tre, Part III,Ch.51,Thm.51.6(51.3),p.530] the canonical linear operator $\mathcal{S}(\mathbf{R}_{>0}) \otimes \mathcal{S}(\mathbf{R}_{>0}) \to \mathcal{S}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$ is a linear topological embedding of the projective tensor product topology on the source, extending to a linear topological isomorphism $\mathcal{S}(\mathbf{R}_{>0}) \,\widehat{\otimes}_{\pi}\, \mathcal{S}(\mathbf{R}_{>0}) \to \mathcal{S}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$.

In particular and by design of the Hausdorff locally convex topologies on $\mathcal{S}_{I}(\mathbf{R}_{>0})$ and $\mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$, we deduce that the canonical linear operator from (5.3.3.13) is a linear topological embedding with respect to

## PDF page 255

**5.3. WEIL’S PRINCIPAL VALUE OPERATORS** · **255**

the projective tensor product topology on the source, and hence extends to a linear topological embedding from the completion of the source, into $\mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$.

$\mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$ is a nuclear Fréchet space. Indeed, we may select a $\mathbf{Z} \times \mathbf{Z}$-indexed countable subfamily of the $T_{a,b} : \phi \mapsto \lvert\cdot\rvert_{r,1}^{a} \lvert\cdot\rvert_{r,2}^{b} \phi \in \mathcal{S}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$ with $a,b$ ranging over countable sequences $\{a_{k}\}_{k \ge 0}$ and $\{b_{k}\}_{k \ge 0}$ such that $\bigcup_{k \in \mathbf{Z}}(a_{k}, a_{k+1}) = \mathbf{R}$ and $\bigcup_{k \in \mathbf{Z}}(b_{k}, b_{k+1}) = \mathbf{R}$ without changing the Hausdorff locally convex topology on $\mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$, which proves metrizability, and completeness and nuclearity are inherited by [Scha, Ch.III,§7,Thm.7.4,p.103], since $\prod_{a,b} T_{a,b}$ realizes $\mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$ as a closed subspace of the nuclear Fréchet space $\prod_{\{(a_{k},b_{k}), k \ge 0\}} (\mathcal{S}(\mathbf{R}_{>0}) \times \mathcal{S}(\mathbf{R}_{>0}))$.

It is therefore enough to show that $\mathcal{S}_{I}(\mathbf{R}_{>0}) \,\widehat{\otimes}_{\pi}\, \mathcal{S}_{I}(\mathbf{R}_{>0}) \to \mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$ has dense range: being the source complete, the range is closed, and hence agrees with $\mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$, which, by [NB, Thm.14.4.5], implies that the linear topological embedding $\mathcal{S}_{I}(\mathbf{R}_{>0}) \,\widehat{\otimes}_{\pi}\, \mathcal{S}_{I}(\mathbf{R}_{>0}) \to \mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$ is indeed a linear topological isomorphism.

Smooth compactly supported functions of the form $\phi \otimes \psi$ with $\phi \in \mathcal{D}(\mathbf{R}_{>0})$ and $\psi \in \mathcal{D}(\mathbf{R}_{>0})$ linearly generate a dense subspace of the source by [Jar, Part III,Ch.15,§15.2,Prop.3(a),p.327] and Lemma D.3.6.1.

By [Tre, Part III,Ch.39,Thm.39.2,p.409], $\mathcal{D}(\mathbf{R}_{>0}) \otimes \mathcal{D}(\mathbf{R}_{>0}) \subset \mathcal{D}(\mathbf{R}_{>0} \times \mathcal{D}(\mathbf{R}_{>0})$ is sequentially dense, and so it is enough to show that $\mathcal{D}(\mathbf{R}_{>0} \times \mathbf{R}_{>0}) \subset \mathcal{S}_{I \times I}(\mathbf{R}_{>0} \times \mathbf{R}_{>0})$ is dense. This is seen by means of the same argument as in the proof of Lemma D.3.6.1.

(3) : The following diagram of linear operators is commutative:

(5.3.3.18)

```latex
\begin{tikzcd}
\mathcal{S}_{00}(\mathbf{R})^{\otimes_{\pi}^{p}} \otimes_{\pi} \mathcal{S}_{00}(\mathbf{C})^{\otimes_{\pi}^{q}} \arrow[r] \arrow[d] & \mathcal{S}_{00}(\mathbf{R}^{p} \times \mathbf{C}^{q}) \arrow[d] \\
\mathcal{S}_{I}(\mathbf{R}^{\times})^{\widehat{\otimes}_{\pi}^{p}} \widehat{\otimes}_{\pi} \mathcal{S}_{I}(\mathbf{C}^{\times})^{\widehat{\otimes}_{\pi}^{q}} \arrow[r] & \mathcal{S}_{I^{p+q}}((\mathbf{R}^{\times})^{p} \times (\mathbf{C}^{\times})^{q})
\end{tikzcd}
```

and all the tensor factors are nuclear Fréchet spaces.

The linear operator

$$
\mathcal{S}_{00}(\mathbf{R})^{\otimes_{\pi}^{p}} \otimes_{\pi} \mathcal{S}_{00}(\mathbf{C})^{\otimes_{\pi}^{q}} \to \mathcal{S}_{00}(\mathbf{R}^{p} \times \mathbf{C}^{q})
$$

is a linear topological embedding (to see this, we observe that $\mathcal{S}_{00}(\mathbf{R})$ and $\mathcal{S}_{00}(\mathbf{C})$ are closed subspaces of $\mathcal{S}(\mathbf{R})$, respectively $\mathcal{S}(\mathbf{C})$, and so is $\mathcal{S}_{00}(\mathbf{R}^{p} \times \mathbf{C}^{q})$ as a subspace of $\mathcal{S}(\mathbf{R}^{p} \times \mathbf{C}^{q})$. Since $\mathcal{S}(\mathbf{R})$, $\mathcal{S}(\mathbf{C})$ and $\mathcal{S}(\mathbf{R}^{p} \times \mathbf{C}^{q})$ and all their closed subspaces are nuclear, and $\mathcal{S}(\mathbf{R})^{\otimes_{\pi}^{p}} \otimes_{\pi} \mathcal{S}(\mathbf{C})^{\otimes_{\pi}^{q}} \to \mathcal{S}(\mathbf{R}^{p} \times \mathbf{C}^{q})$ is continuous and a linear topological embedding with dense range by [Tre, Part III,Ch.51,Thm.51.6(51.3),p.530], then [Jar, Part III,Ch.16,§16.2,Cor.3,p.348] applies).

By (2), the bottom horizontal arrow in (5.3.3.18) is a linear topological isomorphism.

Since the topmost horizontal arrow is continuous and injective (because each of the Hausdorff locally convex topological $\mathbf{C}$-vector spaces $\mathcal{S}_{00}(\mathbf{R})$ and $\mathcal{S}_{00}(\mathbf{C})$ are closed in $\mathcal{S}(\mathbf{R})$ and $\mathcal{S}(\mathbf{C})$, respectively, and hence nuclear by [Scha, Ch.III,§7,Thm.7.4,p.103], which implies by [Jar, Part III,Ch.16,§16.2,Cor.3,p.348] that $\mathcal{S}_{00}(\mathbf{R})^{\otimes_{\pi}^{p}} \otimes_{\pi} \mathcal{S}_{00}(\mathbf{C})^{\otimes_{\pi}^{q}} \to \mathcal{S}(\mathbf{R})^{\otimes_{\pi}^{p}} \otimes_{\pi} \mathcal{S}(\mathbf{C})^{\otimes_{\pi}^{q}}$ is a linear topological embedding, which, followed by the linear topological embedding $\mathcal{S}(\mathbf{R})^{\otimes_{\pi}^{p}} \otimes_{\pi} \mathcal{S}(\mathbf{C})^{\otimes_{\pi}^{q}} \to \mathcal{S}(\mathbf{R}^{p} \times \mathbf{C}^{q})$ from [Tre, Part III,Ch.51,Thm.51.6(51.3),p.530], agrees with the composition of the top horizontal in (5.3.3.18) followed by the linear topological embedding $\mathcal{S}_{00}(\mathbf{R}^{p} \times \mathbf{C}^{q}) \to \mathcal{S}(\mathbf{R}^{p} \times \mathbf{C}^{q})$), then the rightmost vertical arrow is a linear topological isomorphism so long as we prove the following two assertions:

(1) the rightmost vertical arrow is continuous.
(2) the two linear operators

$$
\mathcal{S}_{00}(\mathbf{R}) \to \mathcal{S}_{I}(\mathbf{R}^{\times}), \quad \mathcal{S}_{00}(\mathbf{C}) \to \mathcal{S}_{I}(\mathbf{C}^{\times}) \tag{5.3.3.19}
$$

are continuous and surjective.

## PDF page 256

**256** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

Indeed, being source and target of the top horizontal and rightmost vertical arrows in (5.3.3.18) Fréchet spaces, surjectivity implies that they are both linear topological isomorphisms by [NB, Thm.14.4.5].

Since all the tensor factors in source and target of the leftmost vertical arrow in (5.3.3.18) are nuclear, by [Jar, Part III,Ch.16,§16.2,Cor.3,p.348] indeed the second of the two assertions above implies that it is a linear topological embedding with dense range.

We are therefore reduced to showing the two assertions in (1) and (2) above.

We first observe that (1) follows from (2). Indeed, we know that the topmost horizontal arrow in (5.3.3.18) is a linear topological embedding, hence inducing a linear topological embedding:

$$
\mathcal S_{00}(\mathbf R)^{\widehat\otimes^p_\pi}\widehat\otimes_\pi\mathcal S_{00}(\mathbf C)^{\widehat\otimes^q_\pi}\to\mathcal S_{00}(\mathbf R^p\times\mathbf C^q) \tag{5.3.3.20}
$$

and upon showing (2), then the continuous linear map:

$$
\mathcal S_{00}(\mathbf R)^{\widehat\otimes^p_\pi}\widehat\otimes_\pi\mathcal S_{00}(\mathbf C)^{\widehat\otimes^q_\pi}\to\mathcal S_I(\mathbf R^\times)^{\widehat\otimes^p_\pi}\widehat\otimes_\pi\mathcal S_I(\mathbf C^\times)^{\widehat\otimes^q_\pi}
$$

is also a linear topological isomorphism, and hence the composition of the leftmost vertical arrow followed by the bottom horizontal arrow in (5.3.3.18), is a linear topological isomorphism, hence surjective.

This implies that the linear topological embedding from (5.3.3.20) is surjective, and hence a linear topological isomorphism, which implies both continuity and surjectivity of the rightmost vertical arrow, hence proving (1).

Continuity of $\mathcal S_{00}(\mathbf R)\to\mathcal S_I(\mathbf R^\times)$, $\mathcal S_{00}(\mathbf C)\to\mathcal S_I(\mathbf C^\times)$ and $\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)\to\mathcal S_{I^{p+q}}((\mathbf R^\times)^p\times(\mathbf C^\times)^q)$ is seen as follows.

We use Proposition D.3.2.5 and [CF, Ch.XV,Thm.2.4.1].

We observe that for any $f\in\mathcal S_{00}(\mathbf R)$, respectively $f\in\mathcal S_{00}(\mathbf C)$, we have, using the same continuous homomorphic sections $\tau_r$, $\tau_c$ to the modules $|\cdot|_r$ and $|\cdot|_c$:

$$
L_r(f,(s,\omega)):=\int_{\mathbf R_{>0}}t^s(f(\tau_r(t))+\omega(-1)f(-\tau_r(t))\,\frac{\mathrm{d}t}{t},\quad L_c(f,(s,\omega)):=\int_{\mathbf R_{>0}}t^s\int_{\mathrm U(1)}\omega(e^{i\theta})f(\tau_c(t)e^{i\theta})\,(2|\mathrm{d}\theta|)\,\frac{\mathrm{d}t}{t}
$$

are entire functions of $s$, as $\omega$ varies over all continuous characters of $\{\pm 1\}$, respectively $\mathrm U(1)$.

We have the inequalities, for any real number $a>0$, and for any $\alpha,\beta\in\mathbf N$:

$$
\sup_{x\in\mathbf R^\times}|(1+|\log|x|_r|^\alpha)(x\partial_x)^\beta|x|_r^af(x)|\le\sup_{x\in\mathbf R}|(1+|x|_r^\alpha)|x|_r^{a+\beta}\partial_x^\beta f(x)| \tag{5.3.3.21}
$$

and:

$$
\sup_{z\in\mathbf C^\times}|(1+|\log|z|_c|^\alpha)(z\partial_z)^\beta(\bar z\partial_{\bar z}^\gamma|z|_c^af(z)|\le\sup_{z\in\mathbf C}|(1+|z|_c^\alpha)|z|_c^{a+\beta+\gamma}\partial_z^\beta\partial_{\bar z}^\gamma f(z)|. \tag{5.3.3.22}
$$

By the functional equation from [CF, Ch.XV,Thm.2.4.1] and the polynomial growth of $\rho_v(c)$ for $v$ Archimedean (see the proof of Theorem 3.3.1.5), the inequalities in (5.3.3.21) and (5.3.3.22) combined with Asymptotic Residue Theorem (see Theorem B.3.2.1) implies the sequential continuity of $L_r(\cdot,(s,\omega))$, respectively $L_c(\cdot,(s,\omega))$, as linear operators on $\mathcal S_{00}(\mathbf R)$, respectively $\mathcal S_{00}(\mathbf C)$, valued in $A\mathcal{S}(\mathbf C)\widehat\otimes_\pi\mathcal S(\widehat{\{\pm 1\}})$, respectively $A\mathcal{S}(\mathbf C)\widehat\otimes_\pi\mathcal S(\widehat{\mathrm U(1)})$, and being these Fréchet spaces, both $L_r(\cdot,(s,\omega))$ and $L_c(\cdot,(s,\omega))$ are continuous (this is so because Fréchet spaces are sequential).

The linear operators $L_r(\cdot,(s,\omega))$ and $L_c(\cdot,(s,\omega))$ are the compositions of the linear inclusions $\mathcal S_{00}(\mathbf R)\to\mathcal S_I(\mathbf R^\times)$ and $\mathcal S_{00}(\mathbf C)\to\mathcal S_I(\mathbf C^\times)$, followed by the Mellin transform (see Proposition D.3.2.5), which is a linear topological isomorphism $\mathcal S_I(G)\to A\mathcal{S}(\mathbf C)\widehat\otimes_\pi\mathcal S(G^1)$ by Theorem D.3.3.7, for $I=(-\infty,+\infty)$ and $G$ an $\mathbf R_{>0}$-modulated Hausdorff locally compact abelian group, and hence both linear inclusions $\mathcal S_{00}(\mathbf R)\to\mathcal S_I(\mathbf R^\times)$ and $\mathcal S_{00}(\mathbf C)\to\mathcal S_I(\mathbf C^\times)$ are continuous.

To establish the surjectivity assertions in (2), we use Proposition 5.3.3.2, which gives that $\mathcal S_I(\mathbf R^\times)$ and $\mathcal S_I(\mathbf C^\times)$ are stable under ordinary smooth, respectively holomorphic and anti-holomorphic, derivation of any order, and that this operation is continuous in each case respectively.

## PDF page 257

**5.3. WEIL'S PRINCIPAL VALUE OPERATORS** · **257**

We let $\phi\in\mathcal S_I(\mathbf R^\times)$. We need to show that the extension by zero of $\phi$ to $\mathbf R$ is smooth at $0\in\mathbf R$. This will prove that such extension by zero is Schwartz over $\mathbf R$ (the reader may compare this step in the argument, with the proof of Lemma B.2.1.4, where boundedness and convergence to zero of $\partial_x^m\phi$ as $|x|\to 0^+$ is obtained by direct calculation).

We know that, for every integer $m\ge 0$, $\partial_x^m\phi$ is continuous on $\mathbf R^\times$ and tends to $0$ as $|x|\to 0$. We have yet to show that the derivative of $\phi$ exists at $0\in\mathbf R$ and agrees with the limit value of $\partial_x^m\phi$ (which is zero).

This is seen by observing that we have, over $(-A,A)$:

$$
\left|\frac{\phi(x)}{x}\right|\le\frac{1}{2A}\int_{-A}^{A}|(\partial_x\phi)(y)|\,\mathrm{d}y\le\frac{C}{2A}\int_{-A}^{A}|y|^M\,\mathrm{d}y \tag{5.3.3.23}
$$

for some integer $M>1$ and a real number $C>0$, which gives the desired result, as $A\to 0^+$. To argue that we have $|\partial_x\phi(y)|\le C|y|^M$ for $y\in(-A,A)$, we used boudedness of $M_x$ and continuity of $\partial_x$ on $\mathcal S_I(\mathbf R^\times)$, to deduce that $\partial_x\phi$ is of the form $x^Mu$ for some $u\in\mathcal S_I(\mathbf R^\times)$, and hence $x^Mu$ tends to $0$ as $|x|\to 0^+$, giving boundedness of $u$ over $(-A,A)$ by some $C>0$, and the bound $|\partial_x\phi(y)|\le C|y|^M$ over $(-A,-\varepsilon)\cup(\varepsilon,A)$, propagated to $(-A,A)$ by continuity.

The middle improper integral in (5.3.3.23) therefore converges and the inequalities in (5.3.3.23) hold.

Upon replacing $\phi$ with $\partial_x^m\phi$ for any $m\ge 0$, which is possible by Proposition 5.3.3.2, we deduce that the derivative of the extension by zero of $\phi$ to $\mathbf R$ exists at $0$ and vanishes, therefore showing that such extension by zero is smooth and Schwartz. This shows surjectivity of the restriction operator $\mathcal S_{00}(\mathbf R)\to\mathcal S_I(\mathbf R^\times)$.

A similar argument shows that the restriction operator $\mathcal S_{00}(\mathbf C)\to\mathcal S_I(\mathbf C^\times)$, where the middle integral in (5.3.3.23) is replaces with the line integral from the origin to an arbitrary point $z$ along an arbitrary smooth rectifiable curve $\gamma:[0,1]\to\mathbf C$. This proves that the directional derivative along $\gamma'$ of the extension by zero of $\phi$ exists at $z=0$ and vanishes there, proving smoothness at $z=0$.

To conclude the proof of (3), we observe that, since we have shown that the linear restriction operator $\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)\to\mathcal S_{I^{p+q}}((\mathbf R^\times)^p\times(\mathbf C^\times)^q)$ is a linear topological isomorphism, since continuous quasi-characters of $(\mathbf R^\times)^p\times(\mathbf C^\times)^q$ are of the form $\bigotimes_{1\le k\le p}c_k\otimes\bigotimes_{1\le m\le q}c'_m$, for $c_k$ a continuous quasi-character of $\mathbf R^\times$ for each $1\le k\le p$, and $c'_m$ a continuous quasi-character of $\mathbf C^\times$ for $1\le m\le q$, then, using the linear topological isomorphisms $\mathcal S_{00}(\mathbf R)^{\widehat\otimes^p_\pi}\widehat\otimes_\pi\mathcal S(\mathbf C)^{\widehat\otimes^q_\pi}\to\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)$ and $\mathcal S_I(\mathbf R^\times)^{\widehat\otimes^p_\pi}\widehat\otimes_\pi\mathcal S_I(\mathbf C^\times)^{\widehat\otimes^q_\pi}\to\mathcal S_{I^{p+q}}((\mathbf R^\times)^p\times(\mathbf C^\times)^q)$, it is enough to treat the cases $(p,q)=(1,0)$, $(0,1)$, in order to show that pointwise multiplication by continuous quasi-characters of $(\mathbf R^\times)^p\times(\mathbf C^\times)^q$ on $\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)$ is valued in $\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)$, continuous and (hence) continuously invertible.

Continuous unitary characters on $\mathbf R^\times$, respectively $\mathbf C^\times$, are smooth, bounded, with smooth and bounded $(x\partial_x)^m$-derivatives, respectively $(z\partial_z)^m$ and $(\bar z\partial_{\bar z})^m$-derivatives, for every integer $m\ge 0$. Continuity and continuous invertibility of $M_x$ on $\mathcal S_I(\mathbf R^\times)$ and of $M_z$, $M_{\bar z}$ on $\mathcal S_I(\mathbf C^\times)$, therefore show, by composition, that indeed multiplication on $\mathcal S_{00}(\mathbf R)$, respectively $\mathcal S_{00}(\mathbf C)$, by a continuous unitary character of $\mathbf R^\times$, respectively $\mathbf C^\times$, is a continuous linear operator. The case of arbitrary continuous quasi-characters then follows from Proposition 5.3.3.2(1).

$\square$

We conclude with the following observation:

PROPOSITION 5.3.3.4. *We parametrize $\Omega(\mathbf R^\times)$ and $\Omega(\mathbf C^\times)$ as per (3.1.2.3) from (3.1.2.5) upon choosing the canonical continuous homomorphic section to the real absolute value on $\mathbf R^\times$, and the continuous homomorphic section $t\mapsto t^{1/2}$ to the complex absolute value on $\mathbf C^\times$.*

*Recall that we set:*

$$
\rho_r(s,1):=\frac{\pi^{-\frac{s}{2}}\Gamma\left(\frac{s}{2}\right)}{\pi^{-\frac{1-s}{2}}\Gamma\left(\frac{1-s}{2}\right)},\quad \rho_r(s,\mathrm{sgn}):=i\frac{\pi^{-\frac{s+1}{2}}\Gamma\left(\frac{s+1}{2}\right)}{\pi^{-\frac{(1-s)+1}{2}}\Gamma\left(\frac{(1-s)+1}{2}\right)} \tag{5.3.3.24}
$$

## PDF page 258

**258** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

*and, for each integer $n\in\mathbf Z$:*

$$
\rho_c(s,c_n):=(-1)^{|n|}\frac{(2\pi)^{1-s}\Gamma\left(s+\frac{|n|}{2}\right)}{(2\pi)^s\Gamma\left((1-s)+\frac{|n|}{2}\right)} \tag{5.3.3.25}
$$

*where $c_n:\mathrm U(1)\to\mathrm U(1)$ is the continuous character $\theta\mapsto e^{in\theta}$, and the subscript $r$ reads “real” and the subscript $c$ reads “complex”.*

*We further define:*

$$
L_r(f,(s,\omega)):=\int_{\mathbf R_{>0}}t^s(f(\tau_r(t))+\omega(-1)f(-\tau_r(t))\,\frac{\mathrm{d}t}{t},\quad L_c(f,(s,\omega)):=\int_{\mathbf R_{>0}}t^s\int_{\mathrm U(1)}\omega(e^{i\theta})f(\tau_c(t)e^{i\theta})\,(2|\mathrm{d}\theta|)\,\frac{\mathrm{d}t}{t} \tag{5.3.3.26}
$$

*as meromorphic functions on $\Omega(\mathbf R^\times)$, respectively $\Omega(\mathbf C^\times)$.*

*Then, for $n,p,q\ge 0$ integers, the continuous operators:*

$$
M_{x^n}:\mathcal S(\mathbf R)\to\mathcal S(\mathbf R),\quad M_{z^p\bar z^q}:\mathcal S(\mathbf C)\to\mathcal S(\mathbf C) \tag{5.3.3.27}
$$

*satisfy the following properties:*

*(1) As meromorphic functions on $\Omega(\mathbf R^\times)$, the following identity holds:*

$$
L_r(f,(s,\omega))=L_r(f,(s+n,\mathrm{sgn}(x)^{\epsilon(n)}\omega)) \tag{5.3.3.28}
$$

*where $\epsilon(n)=0$ if $n$ is even, and $\epsilon(n)=1$ if $n$ is odd. We further have:*

$$
L_r(M_{x^n}f,(s,\omega))=\rho_r(s+n,\mathrm{sgn}^{\epsilon(n)}\omega)L_r(\widehat f,(1-s-n,\mathrm{sgn}(x)^{\epsilon(n)}\omega)). \tag{5.3.3.29}
$$

*(2) As meromorphic functions on $\Omega(\mathbf C^\times)$, the following identity holds for every integer $n\in\mathbf Z$:*

$$
L_c(M_{z^p\bar z^q}f,(s,c_n))=L_c(f,(s+p/2+q/2,c_{n+p-q})). \tag{5.3.3.30}
$$

*We further have:*

$$
L_c(M_{z^p\bar z^q}f,(s,c_n))=\rho_c(s+p/2+q/2,c_{n+p-q})L_c(\widehat f,(1-s-p/2-q/2,c_{-n-p+q})). \tag{5.3.3.31}
$$

*PROOF. (1) : We compute:*

$$
L_r(M_{x^n}f,(s,\omega))=\int_{\mathbf R^\times}(M_{x^n}f)(x)\omega(x)|x|_r^s\,\frac{|\mathrm{d}x|}{|x|_r} \tag{5.3.3.32}
$$

$$
=\int_{\mathbf R^\times}f(x)\mathrm{sgn}(x)^{\epsilon(n)}\omega(u)|u|_r^{s+n}\,\frac{|\mathrm{d}u|}{|u|_r} \tag{5.3.3.33}
$$

$$
=L_r(f,(s+n,\mathrm{sgn}(x)^{\epsilon(n)}\omega)). \tag{5.3.3.34}
$$

We also have, by the local functional equation from [CF, Ch.XV,Thm.2.4.1]:

$$
L_r(M_{x^n}f,(s,\omega))=\rho_r(s+n,\mathrm{sgn}^{\epsilon(n)}\omega)L_r(\widehat f,(1-s-n,\mathrm{sgn}(x)^{\epsilon(n)}\omega)) \tag{5.3.3.35}
$$

where $\epsilon(n)=0$ if $n$ is even, and, and $\epsilon(n)=1$ if $n$ is odd.

(2) : Recall that the complex absolute value $|\cdot|_c$ is the square of the complex Euclidean norm.

## PDF page 259

**5.3. WEIL'S PRINCIPAL VALUE OPERATORS** · **259**

We further recall the following calculation:

$$
L_c(M_{z^p\bar z^q}f,(s,c_n))=\int_{\mathbf C^\times}(M_{z^p\bar z^q}f(z))c_n(z)|z|_c^s\,\frac{|\mathrm{d}z\wedge \mathrm{d}\bar z|}{|z|_c} \tag{5.3.3.36}
$$

$$
=\int_{\mathbf C^\times}z^p\bar z^qf(z)c_n(z)|z|_c^s\,\frac{|\mathrm{d}z\wedge \mathrm{d}\bar z|}{|z|_c} \tag{5.3.3.37}
$$

$$
=\int_{\mathbf C^\times}f(z)c_{n+p-q}(z)|z|_c^{s+p/2+q/2}\,\frac{|\mathrm{d}z\wedge \mathrm{d}\bar z|}{|z|_c} \tag{5.3.3.38}
$$

$$
=L_c(f,(s+p/2+q/2,c_{n+p-q})). \tag{5.3.3.39}
$$

We also have:

$$
L_c(M_{z^p\bar z^q}f,(s,c_n))=\rho_c(s+p/2+q/2,c_{n+p-q})L_c(\widehat f,(1-s-p/2-q/2,c_{-n-p+q})). \tag{5.3.3.40}
$$

All identities hold for $s\in\mathbf C_{>0}$, and hold as meromorphic functions over the complex $s$-plane by analytic continuation.

$\square$

We will be viewing $M_{x^n}$ and $M_{z^p\bar z^q}$ as analogs for Archimedean local fields, of the operators $\mathrm{PV}_v$ for $v$ non-Archimedean. The reason is that their application resolves the singularities of the Archimedean local $L$-functions, while $\mathrm{PV}_v$ does so for the non-Archimedean local $L$-functions.

**5.3.4. Weil's Principal Value Operators and holomorphic $S$-idelic Zeta functions.** We now discuss how to produce examples of $S$-idelic Zeta functions from Schwartz-Bruhat functions on $\mathbf A_{F,S}$, with a prescribed divisor of poles. This theme will be reprised in the subsequent two Chapters, which will discuss poles and zeros in depth: Schauder bases arising from poles of $S$-idelic Zeta functions and zeros of global idelic Zeta functions are one of the principal instruments throughout the trace calculation which is the main subject of study of this work.

Specifically, before we learn how to construct Schwartz-Bruhat functions that satisfy prescribed divisorial conditions, we will now discuss how to resolve the singularities of their $L$-functions.

The Definition below exhibits a rich source of Schwartz-Bruhat functions on $\mathbf A_{F,S}$ whose Mellin transform $L_S$ is entire. We will then use Weil's Principal Value Operators to modify an arbitrary Schwartz-Bruhat function on $\mathbf A_{F,S}$ into one whose only poles arise from its Archimedean component, and these, we will classify completely at the end of this subsection.

This completes the preparations for the Second Structrue Theorem (see Theorem 5.4.1.1), which is in turn the stepping stone for the remaining Structure Theorems throughout this Chapter.

DEFINITION 5.3.4.1. For $F$ a number field and $S$ a finite set of places of $F$ containing all the Archimedean places.

We choose, for each real place $v$ of $F$, an isomorphism of topological fields $F_v\simeq\mathbf R$, and for each complex place $v$ of $F$, an isomorphism of topological fields $F_v\simeq\mathbf C$.

We define the closed linear subspace $\mathcal S_{00}(\mathbf A_{F,S_\infty})\subset\mathcal S_{00}(\mathbf A_{F,S_\infty})$ as the pre-image along the pullback by the induced isomorphism of Hausdorff locally compact abelian groups $\mathbf A_{F,S_\infty}\simeq\mathbf R^{r_1}\times\mathbf C^{r_2}$, of the closed subspace $\mathcal S_{00}(\mathbf R^{r_1}\times\mathbf C^{r_2})\subset\mathcal S(\mathbf R^{r_1}\times\mathbf C^{r_2})$.

We define the following linear subspace of $\mathcal S(\mathbf A_{F,S})$:

$$
\mathcal S_{00}(\mathbf A_{F,S}):=\mathcal S_{00}(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F_v^\times)\subset\mathcal S(\mathbf A_{F,S}). \tag{5.3.4.1}
$$

We refer to $\mathcal S_{00}(\mathbf A_{F,S})$ as the subspace of polar-free Schwartz-Bruhat functions on $\mathbf A_{F,S}$.

LEMMA 5.3.4.2. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

## PDF page 260

**260** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

*(1) The linear subspace $\mathcal S_{00}(\mathbf A_{F,S})\subset\mathcal S(\mathbf A_{F,S})$ is closed, stable under the continuous left-translation action of $\mathrm{GL}_1(\mathbf A_{F,S})$ on $\mathcal S(\mathbf A_{F,S})$, and, as a subspace of $\mathcal S(\mathbf A_{F,S})$, independent of the choice of isomorphisms of topological fields $F_v\simeq\mathbf R$, for $v$ real, and $F_v\simeq\mathbf C$, for $v$ complex.*

*(2) For every $f\in\mathcal S_{00}(\mathbf A_{F,S})$, $Z_S(f,c)$ is entire over $\Omega(J_{F,S})$.*

*(3) pointwise multiplication of each element of $\mathcal S_{00}(\mathbf A_{F,S})$ by any continuous quasi-character $c\in\Omega(\mathrm{GL}_1(\mathbf A_{F,S}))$ invariant under $\mathcal O_{F,S}^\times$, is valued in $\mathcal S_{00}(\mathbf A_{F,S})$ and defines a continuous, linear and continuously invertible endomorphism $M_c$ on $\mathcal S_{00}(\mathbf A_{F,S})$.*

PROOF. (1) : The linear subspace $\mathcal S_{00}(\mathbf A_{F,S_\infty})\subset\mathcal S(\mathbf A_{F,S_\infty})$ is closed by Lemma 5.3.3.3(3), and since $\mathcal S(F_v^\times)\subset\mathcal S(F_v)$ is closed for each $v\in S_f$ since $\mathcal S(F_v)$ carries the finest locally convex topology by Lemma 2.1.2.4(1), then by [Jar, Part III,Ch.16,§16.2,Cor.3,p.348], which applies since each tensor factor is nuclear, $\mathcal S_{00}(\mathbf A_{F,S})$ is closed, as a consequence of completeness of the projective tensor product in (5.3.4.1) which is seen as for the proof of Proposition 2.1.4.1, whose method applies since $\bigotimes_{v\in S_f}\mathcal S(F_v^\times)$ also carries the finest locally convex topology (see Lemma C.2.5.2).

Stability under the continuous left-translation action of $\mathrm{GL}_1(\mathbf A_{F,S})$ on $\mathcal S(\mathbf A_{F,S})$ is a consequence of the fact that both $\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)$ is stable under the continuous left-translation action of $(\mathbf R^\times)^p\times(\mathbf C^\times)^q$ on $\mathcal S(\mathbf R^p\times\mathbf C^q)$, and $\mathcal S(F_v^\times)$ is stable under the continuous left-translation action of $F_v^\times$ on $\mathcal S(F_v)$ for any finite place $v\in S$.

Any isomorphism of topological fields $F_v\simeq\mathbf R$, if $v$ is real, and $F_v\simeq\mathbf C$, if $v$ is complex, induces an isomorphism of Hausdorff locally compact abelian groups $i:\mathbf A_{F,S_\infty}\simeq\mathbf R^{r_1}\times\mathbf C^{r_2}$. We choose, for each Archimedean place $v$, two such isomorphisms $i_v$, $i'_v$.

We call $\iota:\mathbf R^{r_1}\times\mathbf C^{r_2}\to\mathbf R^{r_1}\times\mathbf C^{r_2}$ the isomorphism of Hausdorff locally compact abelian groups induced by $i_v\circ i_v^{-1}$ for each Archimedean place $v$ of $F$.

$i$ is therefore smooth, being source and target abelian Lie groups, and preserves the $\mathbf C$-algebras of differential operators on source and target.

Each is isomorphic to the tensor product of the algebras of differential operators on each of the factors $\mathbf R$ and $\mathbf C$, and since $\iota$ is diagonal, and it is the identity on each real component, and either the identity or complex conjugation on each complex component, it preserves the subspace $\mathcal S_{00}(\mathbf R^{r_1}\times\mathbf C^{r_2})$.

It follows that the vanishing conditions defining $\mathcal S_{00}(\mathbf R^{r_1}\times\mathbf C^{r_2})$ as a subspace of $\mathcal S(\mathbf R^{r_1}\times\mathbf C^{r_2})$, define on $\mathcal S(\mathbf A_{F,S_\infty})$ vanishing conditions defining $\mathcal S_{00}(\mathbf A_{F,S_\infty})$ that do not depend on the choice of isomorphisms $F_v\simeq\mathbf R$ and $F_v\simeq\mathbf C$.

(2) : Let $f=\bigotimes_{v\in S}f_v$ be a Schwartz-Bruhat function over $\mathbf A_{F,S}$, with $f_v\in\mathcal S(F_v)$ for each place $v\in S$. Assume $Z_S(f,c)$ is entire over $\Omega(J_{F,S})$. As meromorphic functions on $\Omega(J_{F,S})$, we have $Z_S(f,c)=\prod_{v\in S}Z_v(f_v,c_v)$ where $c_v:=\psi_v(c)$, with $\psi_v:\Omega(J_{F,S})\to\Omega(F_v^\times)$ the surjective local analytic isomorphism defined by restricting the continuous quasi-character $c$ of $J_{F,S}$ to the closed subgroup $F_v^\times\subset J_{F,S}$.

Lemma 3.3.2.1 and Lemma 3.3.2.2 provide us with formulas for the residues of $Z_v(f_v,c_v)$ for each place $v\in S$. Since $Z_S(f,c)$ is entire, then for every Archimedean place $v$ of $F$ contained in $S$ we have, if $v$ is real, $\delta_0^{(k)}(f_v)=0$ for every integer $k\ge 0$, from (3.3.2.6) and (3.3.2.7) of Lemma 3.3.2.1(1), and $\partial_z^k\partial_{\bar z}^{k'}\delta_0(f_v)=0$ for every pair of integers $(k,k')\in\mathbf N^2$ if $v$ is complex, in light of (3.3.2.8) and (3.3.2.9) of Lemma 3.3.2.1(2).

By Lemma 3.3.2.2, we further have $\delta_0(f_v)=0$ for every non-Archimedean place $v$ of $F$ contained in $S$. It follows that we have $f\in\mathcal S_{00}(\mathbf A_{F,S})$.

Since $L_S$ is continuous with respect to the Hausdorff locally convex topology on $\mathcal S(\mathbf A_{F,S})$ and its closed subspaces, on the source, and the Hausdorff locally convex topology on the linear space $\mathscr M(\Omega(J_{F,S}))$ of meromorphic functions on the Riemann surface $\Omega(J_{F,S})$ of uniform convergence on the compact subsets of $\Omega(J_{F,S})-\mathcal U_S$, where $\mathcal U_S$ is the subset of $\Omega(J_{F,S})$ of the poles of the meromorphic function $\rho_S(c)$ from (3.3.1.3) (see Lemma 5.1.3.1(2)), then the closure in $\mathcal S_{00}(\mathbf A_{F,S})$ of the linear subspace linearly generated by the $f\in\mathcal S_{00}(\mathbf A_{F,S})$ of the above form is comprised of elements $f\in\mathcal S_{00}(\mathbf A_{F,S})$ such as $Z_S(f,c)$ is also entire.

## PDF page 261

**5.3. WEIL'S PRINCIPAL VALUE OPERATORS** · **261**

By the design of $\mathcal S_{00}(\mathbf A_{F,S})$, we deduce from [Jar, Part III,Ch.15,§15.2,Prop.3(a),p.327] that such closure is $\mathcal S_{00}(\mathbf A_{F,S})$, which proves (2).

(3) : Let $c\in\Omega(\mathrm{GL}_1(\mathbf A_{F,S}))$ be an $\mathcal O_{F,S}^\times$-invariant continuous quasi-character. Equivalently, a continuous quasi-character in $\Omega(J_{F,S})$, composed with the continuous quotient homomorphism $\mathrm{GL}_1(\mathbf A_{F,S})\to J_{F,S}$. We extend $c$ by zero to a function on $\mathbf A_{F,S}$, which is nowhere vanishing on the open subset $\mathrm{GL}_1(\mathbf A_{F,S})\subset\mathbf A_{F,S}$.

We call $c_v$ the restriction of $c$ to $F_v^\times\subset\mathrm{GL}_1(\mathbf A_{F,S})$, embedded as a closed subgroup through the insertion homomorphism into the $v$-indexed coordinate, with $w$-indexed coordinates defined to be $1$ for every $w\in S-\{v\}$.

Let $f\in\mathcal S_{00}(\mathbf A_{F,S})$ be of the form $f_\infty\otimes\bigotimes_{v\in S_f}f_v$ for $f_\infty\in\mathcal S_{00}(\mathbf A_{F,S_\infty})$ and $f_v\in\mathcal S(F_v^\times)$. We note that $c_v\cdot f_v$ is also Schwartz-Bruhat over $F_v$, because $c_v$ is locally constant and $f_v$ is locally constant and compactly supported, and it is therefore an element of the closed subspace $\mathcal S(F_v^\times)$.

Multiplication by $c_v$ is continuous on $\mathcal S(F_v^\times)$ for each finite place $v\in S$, since $\mathcal S(F_v^\times)$ carries the finest locally convex topology. It is in fact bounded, since $c_v$ is bounded on every compact subset of $F_v^\times$.

We now call $c_\infty$ the restriction of $c$ to $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$. Any $f_\infty\in\mathcal S_{00}(\mathbf A_{F,S_\infty})$ vanishes at each of the hyperplanes $\{x_v=0\}$ for each Archimedean place $v$ of $F$, and hence $c_\infty\cdot f_\infty$ is a smooth function on $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ vanishing on each $\{x_v=0\}$.

pointwise multiplication by any quasi-character of $\mathrm{GL}_1(\mathbf R^p\times\mathbf C^q)$ of any element of $\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)$ is valued in $\mathcal S_{00}(\mathbf R^p\times\mathbf C^q)$, linear, continuous and continuously invertible by Lemma 5.3.3.3(3).

Since $\mathcal S_{00}(\mathbf A_{F,S})$ is an LF-space, by Köthe's Open Mapping Theorem (see [Gro-f, Ch.4,§5,Thm.2(1),p.148], and [SN, §2,Cor.3,p.8]) it suffices to show that $M_c$ is surjective, in order to show that it is a linear topological isomorphism, in which case its inverse is computed by pointwise multiplication by $c^{-1}$.

For each finite place $v\in S$, multiplication by $c_v$ is surjective on $\mathcal S(F_v^\times)$, since multiplication by $c_v^{-1}$ is also continuous (in fact, bounded) and hence multiplication by $c_v$ is boundedly invertible on $\mathcal S(F_v^\times)$.

This shows that every $f\in\mathcal S_{00}(\mathbf A_{F,S})$ of the form $f_\infty\otimes\bigotimes_{v\in S_f}f_v$ for $f_\infty\in\mathcal S_{00}(\mathbf A_{F,S_\infty})$ and $f_v\in\mathcal S(F_v^\times)$ for each finite place $v$ of $F$, is in the image of $M_c$ for every $\sigma(c)\ge0$, and since $M_c$ is linear and continuous and these Schwartz-Bruhat functions linearly generate a dense subspace of $\mathcal S_{00}(\mathbf A_{F,S})$, by [Jar, Part III,Ch.15,§15.2,Prop.3(a),p.327], then $M_c$ is surjective, hence a linear topological isomorphism on $\mathcal S_{00}(\mathbf A_{F,S})$.

$\square$

LEMMA 5.3.4.3. *Let $I:=(-\infty,+\infty)=\mathbf R$, and let $\phi\in\mathcal S_I(\mathbf R_{>0})$ be a Schwartz-Bruhat function with $I$-exponential decay.*

*Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

*There exists $f\in\mathcal S_{00}(\mathbf A_{F,S})$ such that:*

$$
\Phi_{F,S,1}(f)=\phi. \tag{5.3.4.2}
$$

PROOF. We choose a continuous homomorphic section $\tau$ to the $S$-idelic norm.

The canonical linear map:

$$
\mathcal S(\mathbf A_{F,S}):=\mathcal S_{00}(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F_v^\times)\to\mathcal S_I(\mathbf R^\times)^{\widehat\otimes^{r_1}_\pi}\widehat\otimes_\pi\mathcal S_I(\mathbf C^\times)^{\widehat\otimes^{r_2}_\pi}\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F_v^\times) \tag{5.3.4.3}
$$

defined as the unique extension by continuity of the tensor product of the linear topological isomorphism

$$
\mathcal S_{00}(\mathbf A_{F,S_\infty})\to\mathcal S_{00}(\mathbf R^{r_1}\times\mathbf C^{r_2})\to\mathcal S_I((\mathbf R^\times)^{r_1})\widehat\otimes_\pi\mathcal S_I((\mathbf C^\times)^{r_2}) \tag{5.3.4.4}
$$

provided by Lemma 5.3.3.3(3) and (2), with the identity operator on $\bigotimes_{v\in S_f}\mathcal S(F_v^\times)$, is itself a linear topological isomorphism, since the tensor factors are nuclear, and [Jar, Part III,Ch.16,§16.2,Cor.3,p.348] applies.

We note that the linear topological isomorphism from (5.3.4.3) is compatible with the continuous left-translation action of $\mathrm{GL}_1(\mathbf A_{F,S})$ on the source and of $\mathrm{GL}_1(\mathbf R^{r_1}\times\mathbf C^{r_2})\times\prod_{v\in S_f}F_v^\times$ on the target.

## PDF page 262

**262** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

By Lemma D.2.2.2(1), we further have a linear topological isomorphism:

$$
\mathcal S_I((\mathbf R^\times)^{r_1})\widehat\otimes_\pi\mathcal S_I((\mathbf C^\times)^{r_2})\to\mathcal S(\{\pm 1\})^{\widehat\otimes^{r_1}_\pi}\widehat\otimes_\pi\mathcal S(\mathrm U(1))^{\widehat\otimes^{r_2}_\pi}\widehat\otimes_\pi\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2}_\pi} \tag{5.3.4.5}
$$

and the tensor product with the identity operator on $\bigotimes_{v\in S_f}\mathcal S(F_v^\times)$ is a linear topological isomorphism:

$$
\mathcal S_{00}(\mathbf A_{F,S})\to\mathcal S(\{\pm 1\})^{\widehat\otimes^{r_1}_\pi}\widehat\otimes_\pi\mathcal S(\mathrm U(1))^{\widehat\otimes^{r_2}_\pi}\widehat\otimes_\pi\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2}_\pi}\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F_v^\times) \tag{5.3.4.6}
$$

by [Jar, Part III,Ch.16,§16.2,Cor.3,p.348], again using nuclearity of the tensor factors to apply the Corollary, which, followed by the tensor product of the identity operator on the first $2r_1+2r_2$ tensor factors, with the tensor product of the linear topological isomorphisms $\mathcal S(F_v^\times)\simeq\mathcal S(\mathcal O_{F_v}^\times)\widehat\otimes_\pi\mathcal S(\pi_v^{\mathbf Z})$ for a choice of uniformizer $\pi_v$ at $v$ and for each finite place $v\in S$, is the linear topological isomorphism (by another application of [Jar, Part III,Ch.16,§16.2,Cor.3,p.348]):

$$
\mathcal S_{00}(\mathbf A_{F,S})\to\mathcal S(\{\pm 1\})^{\widehat\otimes^{r_1}_\pi}\widehat\otimes_\pi\mathcal S(\mathrm U(1))^{\widehat\otimes^{r_2}_\pi}\widehat\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(\mathcal O_{F_v}^\times)\otimes_\pi\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2}_\pi}\widehat\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(\pi_v^{\mathbf Z}) \tag{5.3.4.7}
$$

also compatible with the continuous left-translation action of $\mathrm{GL}_1(\mathbf A_{F,S})$ on the source, and the continuous action of $\mathrm{GL}_1(\mathbf A_{F,S})$ on the target uniquely determined by the actions through its quotients, on each tensor factor, extended by continuity.

By Theorem D.1.2.1, the operator $\Phi_{F,S,1}$ agrees, up to linear topological automorphisms of the source, on $\mathcal S_{00}(\mathbf A_{F,S})$, with the unique extension by continuity of the tensor product:

$$
\Phi_{\{\pm 1\}}^{\otimes^{r_1}_\pi}\otimes_\pi\Phi_{\mathrm U(1)}^{\otimes^{r_2}_\pi}\otimes_\pi\bigotimes_{v\in S_f}\Phi_{\mathcal O_{F_v}^\times}\otimes_\pi\Phi_{\log}\otimes_\pi\bigotimes_{v\in S_f}\Phi_v \tag{5.3.4.8}
$$

*where:*

(1) $\Phi_{\log}$ is the operator sending $\psi\in\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2}_\pi}$ to $\sum_{\xi\in\mathcal O_F^\times/\mu_F}\phi((|\xi_\infty x_\infty|_v)_{v\in S_\infty})$ where $\mu_F$ is the cyclic subgroup of $\mathcal O_F^\times$ of the roots of unity contained in $F$. The subscript $y_\infty$ denotes the projection of $y\in\mathrm{GL}_1(\mathbf A_{F,S})$ onto $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$.

(2) All the the other operators $\Phi_G$ are $\widehat{\delta}_1$ (i.e. the Fourier transform, in the sense of the Fourier transform on the Schwartz-Bruhat space $\mathcal S(G)$ of a Hausdorff locally compact abelian group $G$, of the evaluation-at-the-neutral-element continuous functional $\delta_1\in\mathcal S(G)'_\beta$, a tempered distribution; see §D.1).

The identification of the operators $\Phi_{F,S,1}$ and of the operator from (5.3.4.8) is up to a linear topological automorphism of $\mathcal S_{00}(\mathbf A_{F,S})$ only, which is the following one: we choose $\{g_1,\dots,g_{N_S}\}$ are representatives in $\mathrm{GL}_1(\mathbf A_{F,S})^1$ of the $N_S$ ideal classes in $\mathrm{Pic}(\mathcal O_F)$ that are trivialized in $\mathrm{Pic}(\mathcal O_{F,S})$, and for $f\in\mathcal S_{00}(\mathbf A_{F,S})$ of the form $f_\infty\otimes\bigotimes_{v\in S_f}f_v$, with $f_v\in\mathcal S(F_v^\times)$ for each finite place $v\in S$, we have:

$$
\Phi_{F,S,1}(f)(x)=\sum_{1\le i\le N_S}\int_{g\in E_{S_\infty,0}}\sum_{\xi\in\mathcal O_F^\times}f_\infty(\xi(g_i)_\infty gx_\infty)\,\mathrm{d}\mu_{S_\infty,1}(g)\cdot\sum_{\xi'\in\mathcal O_{F,S}^\times/\mathcal O_F^\times}\prod_{v\in S_f}\int_{g_v\in\mathcal O_{F_v}^\times}\sum_{m_v\in\mathbf Z}f_v(\xi' g_v(g_i)_vx_v)\,\mathrm{d}\mu_v(g_v) \tag{5.3.4.9}
$$

writing $x\in\mathbf A_{F,S}$ as $(x_\infty,(x_v)_{v\in S_f})$, where $E_{S_\infty,0}$ is the fundamental domain from (A.2.4.5) for the continuous left translation action of $\mathcal O_F^\times$ on $\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1$.

Since $(\prod_{v\in S_f}\mathcal O_{F_v}^\times)\cdot(\mathcal O_{F,S}^\times/\mathcal O_F^\times)$ has finite index $h_F$ in $\prod_{v\in S_f}F_v^\times$, we may choose the $g_i$'s so as to be of the form $(1,(g_{i,v})_{v\in S_f})$, i.e. each of their projections to $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ is $1$.

Upon making this choice, the value, for each $x\in\mathrm{GL}_1(\mathbf A_{F,S})$, of the integral:

$$
\int_{g\in E_{S_\infty,0}}\sum_{\xi\in\mathcal O_F^\times}f_\infty(\xi(g_i)_\infty gx_\infty)\,\mathrm{d}\mu_{S_\infty,1}(g) \tag{5.3.4.10}
$$

## PDF page 263

**5.3. WEIL'S PRINCIPAL VALUE OPERATORS** · **263**

does not depend on $i$ and equals $\int_{g\in E_{S_\infty,0}}\sum_{\xi\in\mathcal O_F^\times}f_\infty(\xi gx_\infty)\,\mathrm{d}\mu_{S_\infty,1}(g)$. The innermost sub-sum over $\mathcal O_F^\times/\mu_F$ is, we now recognize, the value of $\Phi_{\log}$ on $f_\infty$. The integral over $\mu_F\cdot E_{S_\infty,0}$ can now be recognized as being, for each $x_\infty\in\mathbf A_{F,S_\infty}$, the operator $\Phi_{\{\pm 1\}}^{\otimes^{r_1}_\pi}\otimes_\pi\Phi_{\mathrm U(1)}^{\otimes^{r_2}_\pi}$ (see the construction of $P_S$ from (A.2.4.8)), and hence the integral in (5.3.4.10) (upon setting $(g_i)_\infty=1$) agrees with the continuous extension to $\mathcal S_{00}(\mathbf A_{F,S_\infty})$ of $\Phi_{\{\pm 1\}}^{\otimes^{r_1}_\pi}\otimes_\pi\Phi_{\mathrm U(1)}^{\otimes^{r_2}_\pi}\otimes_\pi\Phi_{\log}$ on $\mathcal S(\{\pm 1\})^{\widehat\otimes^{r_1}_\pi}\widehat\otimes_\pi\mathcal S(\mathrm U(1))^{\widehat\otimes^{r_2}_\pi}\widehat\otimes_\pi\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2}_\pi}$.

The second factor in (5.3.4.9) can now be recognized as being, by another application of Theorem D.1.2.1, $\bigotimes_{v\in S_f}(\Phi_{\mathcal O_{F_v}^\times}\otimes\Phi_v)$ on $\bigotimes_{v\in S_f}\mathcal S(F_v^\times)$.

Making the choice of integrating over $E_{S_\infty,0}$ and the choice of the $\{g_1,\dots,g_{N_S}\}$ amounts to pre-composing $\Phi_{F,S,1}$ by a linear topological automorphism on $\mathcal S_{00}(\mathbf A_{F,S})$ (which, in fact and upon inspection, can be seen to be the identity).

We may choose the continuous homomorphic section $\tau$ to the $S$-idelic norm to have image in the closed subgroup $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ (for example, by choosing it to be of the form $\tau=\tau_{v_0}$, for $v_0$ a fixed choice of Archimedean place of $F$; see Definition A.2.2.5, where $\tau_{v_0}$ is denoted $s_{F,v_0}$).

The linear space $\mathcal D(\mathbf R^{r_1+r_2}_{>0})$ is contained in $\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2}_\pi}$ (up to the linear topological isomorphism to the nuclear Fréchet space $\mathcal S_{I^{r_1+r_2}}(\mathbf R^{r_1+r_2}_{>0})$ defined similarly as in Lemma 5.3.3.3(2) (see also the proof of Lemma 5.3.3.3(3)), compatibly with the continuous left-translation action of $\mathbf R^{r_1+r_2}_{>0}$ on itself, and by [Tre, Part III,Ch.39,Thm.39.2], the choice of continuous homomorphic section $\tau$ to the $S$-idelic norm induces a continuous linear operator $\mathcal D(\mathbf R^{r_1+r_2-1})\otimes\mathcal D(\mathbf R_{>0})$ with sequentially dense range into $\mathcal D(\mathbf R^{r_1+r_2}_{>0})$, where

$$
(\mathbf R^{r_1+r_2}_{>0})^1:=\ker(\prod_{1\le k\le r_1}\prod_{1\le m\le r_2}|\cdot|_{r,k}|\cdot|_{c,m}:\mathbf R^{r_1+r_2}\to\mathbf R_{>0})
$$

acts by continuous left-translation on $\mathbf R^{r_1+r_2-1}_{>0}$ up to the isomorphism $(\mathbf R^{r_1+r_2}_{>0})^1\simeq\mathbf R^{r_1+r_2-1}_{>0}$, and $\mathbf R_{>0}$ acts on $\mathcal D(\mathbf R_{>0})$ by continuous left-translation.

We now observe that $\Phi_{\log}$ can therefore further be written on $\mathcal D(\mathbf R^{r_1+r_2-1})\otimes\mathcal S_I(\mathbf R_{>0})\subset\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2}_\pi}$ (the containment being intended up to linear topological automorphism on the source) as $\Phi_{r_1+r_2-1}\otimes\mathrm{Id}$.

We then choose $\varphi_0$ in $\mathcal D(\{\pm 1\})\simeq\mathbf C^2$ such that $\Phi_{\{\pm 1\}}(\varphi_0)=1$, $\varphi_1$ in $\mathcal D(\mathrm U(1))$ such that $\Phi_{\mathrm U(1)}(\varphi_1)=1$, $\varphi_v\in\mathcal D(\mathcal O_{F_v}^\times)$ such that $\Phi_{\mathcal O_{F_v}^\times}(\varphi_v)=1$, and $\varphi_{\log}\in\mathcal D(\mathbf R^{r_1+r_2-1})$ such that $\Phi_{r_1+r_2-1}(\varphi_{\log})=1$. We therefore have that $\varphi_{\log}\otimes\phi$ is mapped by an equivariant linear topological isomorphism to an element $\psi\in\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2}_\pi}$, such that $\Phi_{\log}(\psi)=\phi$, where $\phi\in\mathcal S_I(\mathbf R_{>0})$ is our original Schwartz-Bruhat function on $\mathbf R_{>0}$ with exponential decay.

In the former cases, $\varphi_0$, $\varphi_1$ and $\varphi_v$ for each $v\in S_f$ exist by compactness of each group, respectively, and in the latter case, $\varphi_{\log}$ exists because $\mathcal O_F^\times/\mu_F$ acts discretely, properly and freely, with co-compact quotient, on $\mathbf R^{r_1+r_2-1}\simeq\{x\in\mathbf R^{r_1+r_2}_{>0}:\prod_{1\le k\le r_1}|x|_{r,k}\cdot\prod_{1\le k\le r_2}|x|_{c,k}=1\}$.

Similarly, we choose $\psi_v\in\mathcal S(\pi_v^{\mathbf Z})$ such that $\Phi_v(\psi_v)=1$, which we can do because $\pi_v^{\mathbf Z}$ acts properly, freely and with co-compact quotient (a single point) on itself.

*We now define:*

$$
\varphi_0^{\otimes^{r_1}}\otimes\varphi_1^{\otimes^{r_2}}\otimes\bigotimes_{v\in S_f}\varphi_v\otimes\psi\otimes\bigotimes_{v\in S_f}\psi_v \tag{5.3.4.11}
$$

*and element of $\mathcal S(\{\pm 1\})^{\widehat\otimes^{r_1}_\pi}\widehat\otimes_\pi\mathcal S(\mathrm U(1))^{\widehat\otimes^{r_2}_\pi}\widehat\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(\mathcal O_{F_v}^\times)\widehat\otimes_\pi\mathcal S_I(\mathbf R_{>0})^{\widehat\otimes^{r_1+r_2-1}_\pi}\widehat\otimes\bigotimes_{v\in S_f}\mathcal S(\pi_v^{\mathbf Z})\widehat\otimes_\pi\mathcal S_I(\mathbf R_{>0})$.*

The element from (5.3.4.11) corresponds under the linear topological isomorphism from (5.3.4.6) to a unique Schwartz-Bruhat function $f\in\mathcal S_{00}(\mathbf A_{F,S})$ such that $\Phi_{F,S,1}(f)=\phi$.

$\square$

PROPOSITION 5.3.4.4. *Let $F$ be a number field. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Let $\chi\in\widehat{J_{F,S}}$ be a continuous character.*

*The following conditions on Schwartz-Bruhat functions $f\in\mathcal S(\mathbf A_{F,S})$ are equivalent:*

## PDF page 264

**264** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

*(1) $Z_S(f,c)$ is entire over $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$.*

*(2) There exists $f_0\in\mathcal S_{00}(\mathbf A_{F,S})\subset\mathcal S(\mathbf A_{F,S})$ such that $Z_S(f,c)=Z_S(f_0,c)$ over $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$.*

*(3) $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)\in\mathcal S_{(-\infty,\infty)}(J_{F,S})(\chi|_{J^1_{F,S}})$.*

PROOF. Assume that (1) holds. If $Z_S(f,c)$ is entire over $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$, then the $S$-local functional equation from (3.3.1.2) of Theorem 3.3.1.1, combined with the polynomial growth of $\rho_S(c)$ (see Theorem 3.3.1.5) over the open vertical strips of bounded width of connected component parametrized by $\chi|_{J^1_{F,S}}$ of the Riemann surface $\Omega(J_{F,S})-\mathcal U_S$, implies, by the Asymptotic Residue Theorem (see Theorem B.3.2.1), that $Z_S(f,c)$ is Schwartz uniformly over the relative vertical strips of Bounded width within $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$, and hence $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)\in\mathcal S_{(-\infty,\infty)}(J_{F,S})(\chi|_{J^1_{F,S}})$ by Proposition D.3.2.5 (applied to the pull-back of $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)$ along a choice of continuous homomorphic section $\tau$ to the $S$-idelic norm, for then using Theorem D.3.3.7(3)), showing that (3) holds.

If (3) holds, then by Lemma 5.3.4.3 combined with Lemma 5.3.3.3(3), which asserts that multiplication by continuous characters of $\mathrm{GL}_1(\mathbf A_{F,S})$ is a bounded and boundedly invertible operator on $\mathcal S_{00}(\mathbf A_{F,S})$, there exists $f_1\in\mathcal S_{00}(\mathbf A_{F,S})$ such that, for $\tau$ a fixed choice of continuous homomorphic section to the $S$-idelic norm, $\Phi_{F,S,1}(f_1)(\tau(t))=\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)(\tau(t))$, and hence $f_0:=\overline{\chi}|\cdot|^{it_0}_{F,S}\cdot f_1$, for $t_0\in\mathbf R$ the unique real number such that $\chi(\tau(t))=t^{it_0}$, satisfies $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f_0)=\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)$.

This shows that (2) holds.

If (2) holds, then by Lemma 5.3.4.2(2), $Z_S(f_0,c)$ is entire over $\Omega(J_{F,S})$, and over the connected component parametrized by $\chi|_{J^1_{F,S}}$, it agrees with $Z_S(f,c)$, which is therefore itself entire over $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$.

$\square$

We have the following result, explaining how to use Weil's Principal Value Operators $\mathrm{PV}_{S,S_0}$ to resolve some of the singularities of the $L$-functions of Schwartz-Bruhat functions on $\mathbf A_{F,S}$.

PROPOSITION 5.3.4.5. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

*Let $f\in\mathcal S(\mathbf A_{F,S})$. Then:*

*(1) We have, for any finite subset $S_0\subset S_f$:*

$$
Z_S(\mathrm{PV}_{S,S_0}(f),c)=\frac{Z_S(f,c)}{\prod_{v\in S_0}L_v(c_v)} \tag{5.3.4.12}
$$

*as meromorphic functions of $c\in\Omega(J_{F,S})$.*

*(2) The poles of $Z_S(\mathrm{PV}_{S_f}(f),c)$ are located at the points*

$$
\mathcal U_{S_\infty}=\bigcup_{v\in S_\infty}\psi_v^{-1}(\mathcal U_v) \tag{5.3.4.13}
$$

*where $\psi_v:\Omega(J_{F,S})\to\Omega(F_v^\times)$ is the surjective local analytic isomorphism restricting a continuous quasi-character of $J_{F,S}$ to $F_v^\times\subset J_{F,S}$, and $\mathcal U_v$ is the set of poles in $\Omega(F_v^\times)$ of the local Euler factor $L_v(c_v)$ of the Hecke $L$-function $L(c)$. $\mathcal U_{S_\infty}$ is equipped with the multiplicity function $N_{S_\infty}:\mathcal U_{S_\infty}\to\mathbf N$ defined as:*

$$
N_{S_\infty}(c):=\sum_{v\in S_\infty}\mathrm{ord}_{c'=c}L_v(c'_v). \tag{5.3.4.14}
$$

*(3) For any continuous character $\chi\in\widehat{J_{F,S}}$, ramified at the finite places in $S_\chi\subset S$ and unramified at each place in $S-S_\chi$, the linear images in $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ under the continuous operator $\Phi_{F,S,\chi|_{J^1_{F,S}}}$ of the closed subspaces:*

$$
\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F_v^\times),\quad \mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f-S_\chi}\mathcal S(F_v^\times)\otimes_\pi\bigotimes_{v\in S_\chi}\mathcal S(F_v) \tag{5.3.4.15}
$$

## PDF page 265

**5.4. STRUCTURE THEOREM II: S-LOCAL ČECH SEQUENCE** · **265**

agree with $\mathrm{PV}_{S,S_f} \mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$.

The meaning of Proposition 5.3.4.5 is that the effect of the operator $\mathrm{PV}_{S,S_f}$ on a Schwartz-Bruhat function $f \in \mathcal S(\mathbf A_{F,S})$ is to remove all the singularities of $Z_S(f, c)$ arising from the non-Archimedean local factors of the Hecke $L$-function $L(c)$, leaving only those arising from the Archimedean local factors, counted with their multiplicity, in place.

Proof. (1) : The identity in (5.3.4.12) holds by Theorem 3.4.3.3, where (3.4.3.13) provides the formula for the effect of $\mathrm{PV}_v$ if $c$ is ramified at $v$, and (3.4.1.6) from Theorem 3.4.1.1 provides it in the unramified case.

(2) : The assertion on the location and multiplicity of the poles of $Z_S(\mathrm{PV}_{S_f}(f), c)$ follows from (1) combined with (3.3.1.2) from Theorem 3.3.1.1.

(3) : By (1), it is enough to show that for any $f_v \in \mathcal S(F_v)$, with $v \in S_\chi$, and for any $f_\infty \in \mathcal S(\mathbf A_{F,S_\infty})$, $f_v \in \mathcal S(F^\times_v)$ for any $v \in S_f - S_\chi$, there exists a large enough integer $N_v \ge 0$ and a complex number $c_v$ for each $v \in S_\chi$, such that upon calling $f'_v := f_v - c_v1_{\pi^{N_v}_v\mathcal O_{F_v}}$, then $f'_v \in \mathcal S(F^\times_v)$, and we have, upon calling $f := f_\infty \otimes \bigotimes_{v\in S_\chi} f_v \otimes \bigotimes_{v\in S_f - S_\chi} f_v$ and $f := f_\infty \otimes \bigotimes_{v\in S_\chi} f'_v \otimes \bigotimes_{v\in S_f - S_\chi} f_v$, we have, as meromorphic functions over $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$:

$$
Z_S(f, c) = Z_S(f', c).
$$

It is enough to show that $Z_v(f_v, c_v) = Z_v(f'_v, c_v)$ for all $c_v \in \Omega(F^\times_v)(\chi_v|_{\mathcal O^\times_{F_v}})_{>0}$.

Since $f_v$ is Schwartz-Bruhat over $F_v$, there exists a large enough integer $N_v \ge 0$ such that $f_v$ is constant over the compact open subgroup $\pi^{N_v}_v\mathcal O_{F_v}$. We let $c_v$ its constant value there. We then define $f'_v := f_v - c_v1_{\pi^{N_v}_v\mathcal O_{F_v}}$.

We note that $1_{\pi^{N_v}_v\mathcal O_{F_v}}$ is an $\mathcal O^\times_{F_v}$-invariant function. As such, since $c_v$ is ramified, $Z_v(1_{\pi^{N_v}_v\mathcal O_{F_v}}, c_v) = 0$ for $\sigma(c_v) > 1$, and hence $Z_v(f_v, c_v) = Z_v(f'_v, c_v)$ for $\sigma(c_v) > 1$. $\square$

**5.4. Structure Theorem II: S-local Čech sequence**

We require a description of the Hausdorff locally convex quotient topology on $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ inherited from $\mathcal S(\mathbf A_{F,S})$, for each continuous character $\omega$ of $J^1_{F,S}$, in terms of an explicit family of seminorms on a certain subspace of the space of meromorphic functions $\mathscr M(\Omega(J_{F,S}))$.

This is the purpose of the Second Structure Theorem (see Theorem 5.4.1.1), proved in this section.

**5.4.1. Second Structure Theorem.** We recall from (5.1.1.1) of Definition 5.1.1.4 that the operator:

$$
Z_S : \mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S})) \to \mathscr M(\Omega(J_{F,S})) \tag{5.4.1.1}
$$

is injective and continuous with respect to the Hausdorff locally convex topology of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$ on the source, and the topology of uniform convergence on the compact subsets of $\Omega(J_{F,S}) - \mathcal U_S$ on the target, where $\mathcal U_S$ is the set of the poles of the meromorphic function $\rho_S$ from (3.3.1.3) of Theorem 3.3.1.1.

In this subsection, we study stronger topologies on $\mathscr M(\Omega(J_{F,S}))$ that induce under $L_S$ the Hausdorff locally convex topology on $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$, for each continuous unitary character $\omega$ of $J^1_{F,S}$.

We are now ready to state and prove the Second Structure Theorem, providing a description of the topology of the Hausdorff locally convex topological $\mathbf C$-vector spaces $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$.

Theorem 5.4.1.1 (Second Structure Theorem). *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places. Let $\tau$ be a choice of continuous homomorphic section to the $S$-idelic norm. We write each $g \in J_{F,S}$ uniquely as $\tau(t)g_0$ for $t \in \mathbf R_{>0}$ and $g_0 \in J^1_{F,S}$, under the resulting isomorphism of Hausdorff locally compact abelian groups $J_{F,S} \simeq \mathbf R_{>0} \times J^1_{F,S}$.*

*(1) For any $\omega \in \widehat{J^1_{F,S}}$, the continuous linear map:*

$$
U_{S,\tau,\omega} : \mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S})) \to A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1}) \tag{5.4.1.2}
$$

## PDF page 266

**266** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

*defined by $U_{S,\tau,\omega}(f) := (Z_S(f, c), Z_S(\widehat f, \widehat c))$ for $c$ corresponding to the pair $(|\cdot|^s_{\mathbf R}, \omega) \in \Omega(\mathbf R_{>0})_{>0} \times \{\omega\}$ under the bi-holomorphism from (3.1.2.5) induced by $\tau$, is a linear topological embedding, compatible with the continuous left-translation actions of $J_{F,S}$ on the source, and the continuous left-translation action of $J_{F,S}$ on the target defined as $(g, (\phi(s), \psi(s))) \mapsto (t^s\omega(g_0)\phi(s), t^{1-s}\bar\omega(g_0)\psi(s))$ as functions of $s \in \mathbf C_{>0}$.*

*Its range is closed, and it is the linear subspace:*

$$
W_{F,S,\omega} := \{(\phi, \psi) \in A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1}) : \phi(s)|_{\mathbf C_{(0,1)}} = \rho_{S,\tau}(s)\psi(s)|_{\mathbf C_{(0,1)}}\} \tag{5.4.1.3}
$$

*where $\rho_{S,\tau}(s)$ is the meromorphic function on the complex $s$-plane obtained from $\rho_S(c)$ of (3.3.1.3) by pre-composing $\rho_S$ with the bi-holomorphism $\Omega(\mathbf R_{>0}) \times \{\omega\} \to \Omega(J_{F,S})(\omega)$ provided by (3.1.2.5).*

*(2) Let $\omega$ be a continuous character of $J^1_{F,S}$. Then $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ is a separable nuclear Fréchet space.*

Remark 5.4.1.2. We note that, in describing the continuous left-translation action of $J_{F,S}$ on the target of $U_{S,\tau,\omega}$, it is understood that $J_{F,S}$ acts through the isomorphism $J_{F,S} \to \mathbf R_{>0} \times J^1_{F,S}$ induced by the choice of $\tau$.

We could choose a holomorphic parametrization

$$
\{\chi|\cdot|^s_{F,S}, (\chi, s) \in \widetilde{J^1_{F,S}} \times \mathbf C\}
$$

for the Riemann surface $\Omega(J_{F,S})$, where $\widetilde{J^1_{F,S}}$ is a choice of lift to $J_{F,S}$ for each continuous character $\omega$ of $J^1_{F,S}$, equivalently a choice of base point for each connected component of $\Omega(J_{F,S})$, and upon calling $x_0(\chi) \in \mathbf R$ the unique real number such that $\chi(\tau(t)) = t^{ix_0(\chi)}$ as smooth functions on $\mathbf R_{>0}$, for each $\chi \in \widetilde{J^1_{F,S}}$, then the composition of $U_{S,\tau,\omega}$ with the vertical translation on the complex half $s$-plane $\mathbf C_{>0}$ by $ix_0(\chi)$, and on the complex half $s$-plane $\mathbf C_{<1}$ by $-ix_0(\chi)$, is the operator sending $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)$ to $(Z_S(f, \chi|\cdot|^s_{F,S}), Z_S(\widehat f, \bar\chi|\cdot|^{1-s}_{F,S}))$.

The action of $g \in J_{F,S}$ described on $A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1})$ in the statement of the Proposition, then matches the multiplication action by the pair of entire functions $(\chi(g)|g|^s_{F,S}, \bar\chi(g)|g|^{1-s}_{F,S})$.

We further refer the reader on Discussion 4.4.1.1 from Chapter 5 of this work.

We begin by showing that $U_{S,\omega,\tau}$ from (5.4.1.2) is continuous.

Lemma 5.4.1.3. *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places, $\omega \in \widehat{J^1_{F,S}}$ a continuous character. Let $\tau$ be a choice of continuous homomorphic section to the $S$-idelic norm. The linear operator $U_{S,\tau,\omega}$ from (5.4.1.2) is continuous and injective.*

Proof. We rename $U_{S,\tau,\omega}$ as $U_S$ for simplicity.

Let $\{f_m\}_{m\ge 0}$ be a sequence of Schwartz-Bruhat functions in $\mathcal S(\mathbf A_{F,S})$ converging in $\mathcal S(\mathbf A_{F,S})$ to $f$. By Proposition 2.3.1.4, since $\{f_m\}_{m\ge 0} \cup \{f\}$ is contained in a bounded subset $B \subset \mathcal S(\mathbf A_{F,S})$, being a Cauchy sequence, there exist real numbers $T_N > 0$ and $C_N > 0$ such that:

$$
|\Phi_{F,S,\omega}(u)(g)| \le C_N|g|^{-N}_{F,S} \tag{5.4.1.4}
$$

for all $g \in J_{F,S}$ such that $|g|_{F,S} > T_N$, and for all $u \in B$.

For every real number $a > 0$, the singularity of the function $t \mapsto t^a$ is $(\frac{\mathrm{d}t}{t})$-integrable over $(0, T_N)$, and by (2.4.3.5) from Corollary 2.4.3.2 and the uniformity properties of the implied constant in (2.4.3.5) and of the constant $T_\varepsilon$, for $\varepsilon = a$, then by Dominated Convergence we deduce that we have:

$$
\lim_{m\to+\infty} \int_{(0,T_N)} t^a \int_{J^1_{F,S}} |\Phi_{F,S,\omega}(f_m)(\tau(t)g_0) - \Phi_{F,S,\omega}(\tau(t)g_0)|^p\, \mathrm{d}\overline{\mu}_{S,1}(g_0)\, \frac{\mathrm{d}t}{t} = 0 \tag{5.4.1.5}
$$

for each real number $p \ge 1$, being $J^1_{F,S}$ compact Hausdorff.

## PDF page 267

**5.4. STRUCTURE THEOREM II: S-LOCAL ČECH SEQUENCE** · **267**

By the estimate from (5.4.1.4) and the uniformity properties of the constants $C_N, T_N > 0$, by Dominated Convergence we also have:

$$
\lim_{m\to+\infty} \int_{(T_N,+\infty)} t^a \int_{J^1_{F,S}} |\Phi_{F,S,\omega}(f_m)(\tau(t)g_0) - \Phi_{F,S,\omega}(\tau(t)g_0)|^p\, \mathrm{d}\overline{\mu}_{S,1}(g_0)\, \frac{\mathrm{d}t}{t} = 0 \tag{5.4.1.6}
$$

for each real number $p \ge 1$.

Upon combining (5.4.1.5) and (5.4.1.6), we deduce that the linear operator $U_S$ is sequentially continuous. Since, by Proposition 2.1.4.1(2), $\mathcal S(\mathbf A_{F,S})$ is a strict LF-space, it is bornological by [Scha, Ch.II,§8,Cor.2,p.62], and by [NB, Thm.13.2.12] it is ultrabornological. $A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1})$ is Hausdorff locally convex nuclear and Fréchet by Lemma D.3.1.2. In particular, it is webbed by [NB, Thm.14.6.2]. By [NB, Thm.14.7.3], $U_S$ is continuous. Injectivity is a consequence of the Identity Theorem: indeed, if for some $f \in \mathcal S(\mathbf A_{F,S})$ we have $Z_S(f, c) = 0$ over $\Omega(J_{F,S})(\omega)_{>0}$, then $Z_S(f, c) = 0$ over $\Omega(J_{F,S})(\omega)$, which, by (5.1.2.4) from Lemma 5.1.2.2, implies that we have $\Phi_{F,S,\omega}(f) = 0$, and hence $U_S$ is injective. $\square$

Before we prove Theorem 5.4.1.1, we establish a special case, resting on a concrete construction:

Proposition 5.4.1.4 (Second Structure Theorem, polar-free case). *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places.*

*Let $\tau$ be a choice of continuous homomorphic section to the $S$-idelic norm. We write each $g \in J_{F,S}$ uniquely as $\tau(t)g_0$ for $t \in \mathbf R_{>0}$ and $g_0 \in J^1_{F,S}$, under the resulting isomorphism of Hausdorff locally compact abelian groups $J_{F,S} \simeq \mathbf R_{>0} \times J^1_{F,S}$.*

*For any $\omega \in \widehat{J^1_{F,S}}$, the continuous linear operator from (5.4.1.2):*

$$
U_{S,\tau,\omega} : \mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S})) \to A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1}) \tag{5.4.1.7}
$$

*defined by $U_{S,\tau,\omega}(f) := (Z_S(f, c), Z_S(\widehat f, \widehat c))$ for $c$ corresponding to the pair $(|\cdot|^s_{\mathbf R}, \omega) \in \Omega(\mathbf R_{>0})_{>0} \times \{\omega\}$ under the bi-holomorphism from (3.1.2.5) induced by $\tau$, is a linear topological embedding, compatible with the continuous left-translation actions of $J_{F,S}$ on the source, and the continuous left-translation action of $J_{F,S}$ on the target defined as $(g, (\phi(s), \psi(s))) \mapsto (t^s\omega(g_0)\phi(s), t^{1-s}\bar\omega(g_0)\psi(s))$ as functions of $s \in \mathbf C_{>0}$.*

*Its range is closed, and it is the linear subspace:*

$$
V_{F,S,\omega} \subset W_{F,S,\omega} := \{(\phi, \psi) \in A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1}) : \phi(s)|_{\mathbf C_{(0,1)}} = \rho_{S,\tau}(s)\psi(s)|_{\mathbf C_{(0,1)}}\} \tag{5.4.1.8}
$$

*where $\rho_{S,\tau}(s)$ is the meromorphic function on the complex $s$-plane obtained from $\rho_S(c)$ of (3.3.1.3) by pre-composing $\rho_S$ with the bi-holomorphism $\Omega(\mathbf R_{>0}) \times \{\omega\} \to \Omega(J_{F,S})(\omega)$ provided by (3.1.2.5), and such that the unique analytic continuation of $\phi$ to the complex $s$-plane is entire.*

Proof. By Proposition 5.3.4.4, indeed $U_{S,\tau,\omega}$ is valued in $V_{F,S,\omega}$, when restricted to $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$, and maps $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$ surjectively onto $V_{F,S,\omega}$.

We now prove this surjectivity assertion.

Let $(\phi, \psi) \in W_{F,S,\omega}$ be an arbitrary element, and denote by $\widetilde\phi(s)$ the unique analytic continuation of $\phi$ to a meromorphic function on the complex $s$-plane, whose existence is ensured by $\phi$ being holomorphic over $\mathbf C_{>0}$, $\psi$ being holomorphic over $\mathbf C_{<1}$, and the functional equation $\phi(s) = \rho_{S,\tau}(s)\psi(s)$ over $\mathbf C_{(0,1)}$, with $\rho_{S,\tau}$ meromorphic over $\mathbf C$ and satisfying $\rho_{S,\tau}(\sigma + it) = O(|t|^{\sigma-1/2})$ for $\sigma \in (0, 1)$ and as $|t| \to +\infty$ (see Theorem 3.3.1.5(3) applied to $k = 0$), uniformly for $\sigma \in [\varepsilon, A)$ for any $0 < \varepsilon < A$, from which it follows that $\rho_{S,\tau}(s)\psi(s) \in A\mathcal S(\mathbf C_{(0,1)})$.

The poles of $\widetilde\phi$ are therefore located at the poles of $\rho_{S,\tau}$ and their order of pole is bounded above by the order of pole of each of the corresponding poles of $\rho_{S,\tau}$, respectively.

The function $\widetilde\phi$ is entire if and only if $\psi$ has a zero at $s = s_0$ of multiplicity at least $\mathrm{ord}_{s=s_0}\rho_{S,\tau}(s)$, this latter being the order of pole of $\rho_{S,\tau}$ at $s = s_0$.

## PDF page 268

**268** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

The point-evaluation functionals $(\phi, \psi) \mapsto (\partial^k_s\psi)(s_0)$ are all continuous for each $s_0 \in \mathbf C_{<1}$ and each integer $k \ge 0$, since they are continuous with respect to the topology of uniform convergence on compact subsets on $\mathcal S(\mathbf C_{<1})$, which is coarser than the Schwartz-Bergman topology on $A\mathcal S(\mathbf C_{<1})$.

It follows that $V_{F,S,\omega}$ is the intersection of the kernel of a countable collection of continuous functionals on $W_{F,S,\omega}$, and it is therefore closed in $W_{F,S,\omega}$. As such, by [Scha, Ch.I,§6,6.3,p.31] it is a Fréchet space.

By the Asymptotic Cauchy Integral Formula (see Theorem B.2.2.4; see also the proof of Lemma D.3.1.2) applied, for each integer $N \ge 0$, to $s^N\phi(s)$ on any vertical line within $\mathbf C_{>0}$, and to $s^N\psi(s)$ on any vertical line contained in $\mathbf C_{<0}$, and the functional equation satisfied by all elements of $W_{F,S,\omega}$ as per (5.4.1.8), for any $(\phi, \psi) \in V_{F,S,\omega}$ we deduce that the unique analytic continuation $\widetilde\phi$ of $\phi$ to the complex $s$-plane, is entire and Schwartz uniformly over all vertical strips of bounded width of the complex $s$-plane.

It is therefore an element of $A\mathcal S(\mathbf C)$. Its inverse Fourier transform along the vertical line $i\mathbf R$, denoted $f_0(t) \in \mathcal S(\mathbf R_{>0})$, is therefore of exponential decay over $\mathbf R_{>0}$, by Proposition D.3.2.5.

By Lemma 5.3.4.3, there exists a Schwartz-Bruhat function $f_1 \in \mathcal S_{00}(\mathbf A_{F,S})$ such that $\Phi_{F,S,1}(f_1)(\tau(t)) = \varphi_0(t)$ as Schwartz-Bruhat functions on $\mathbf R_{>0}$ with exponential decay.

Since multiplication by unitary characters of $J_{F,S}$ is a continuous and continuously invertible operator on $\mathcal S_{00}(\mathbf A_{F,S})$, then upon choosing $\chi \in \widehat{J_{F,S}}$ such that $\chi|_{J^1_{F,S}} = \omega$, we let $x_0 \in \mathbf R$ be the unique real number such that $\chi(\tau(t)) = |t|^{ix_0}_{\mathbf R}$ as smooth functions of $t \in \mathbf R_{>0}$, (and hence the $S$-idelic quasi-character corresponding under (3.3.1.3) from (3.1.2.5) to the pair $(|\cdot|^s_{\mathbf R}, \omega)$ is also parametrized by $\chi|\cdot|^z_{F,S}$ for $z + ix_0 = s$) and $f_0 := \overline{\chi}|\cdot|^{ix_0}_{F,S} \cdot f_1$ is also an element of $\mathcal S_{00}(\mathbf A_{F,S})$ (see Lemma 5.3.4.2).

We therefore have:

$$
\Phi_{F,S,\omega}(f_0)(\tau(t)) = \varphi_0(t)
$$

as smooth functions of $t \in \mathbf R_{>0}$.

By design of $\varphi_0$ and $f$, we have $Z_S(f_0, c) = Z_S(f, \chi|\cdot|^{s-ix_0}_{F,S}) = \phi(s)$ where $c$ corresponds under (3.1.2.5) to the pair $(|\cdot|^s_{\mathbf R}, \omega)$.

(We note that, upon observing that the action of $J^1_{F,S}$ on $V_{F,S,\omega}$ is through multiplication by $\bar\omega$, then $\varphi_0 \in \mathcal S_{(-\infty,+\infty)}(\mathbf R_{>0})$ corresponds under pullback along $\tau$ to a unique element of $\mathcal S_{(-\infty,+\infty)}(J_{F,S})(\chi|_{J^1_{F,S}})$, and hence Proposition 5.3.4.4 applies).

By the functional equation from (3.3.1.2) of Lemma 3.3.1.1, it follows that we have:

$$
\phi(s) = \rho_{S,\tau}(s)Z_S(\widehat f, \widehat c) \tag{5.4.1.9}
$$

with $c$ corresponding to the pair $(|\cdot|^s_{\mathbf R}, \omega)$ under the bi-holomorphism from (3.1.2.5). By uniqueness of the analytic continuation of $\phi$, we deduce that we have $\psi(s) = Z_S(\widehat f, \widehat c)$.

We deduce that the arbitrary $(\phi, \psi) \in V_{F,S,\omega}$ is in the image of $U_{S,\tau,\omega}$, and hence $U_{S,\tau,\omega}$ is surjective onto $V_{F,S,\omega}$.

This proves the surjectivity assertion, i.e. we have shown that $U_{S,\tau,\omega}$ maps $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$ surjectively onto $V_{F,S,\omega}$, a closed subspace of $A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1})$.

We note that since $\mathcal S_{00}(\mathbf A_{F,S})$ is closed in $\mathcal S(\mathbf A_{F,S})$ and $\Phi_{F,S,\omega}$ has closed kernel by Theorem 5.1.1.3, then $\ker(\Phi_{F,S,\omega}) \cap \mathcal S_{00}(\mathbf A_{F,S})$ is also closed in $\mathcal S(\mathbf A_{F,S})$ and in $\mathcal S_{00}(\mathbf A_{F,S})$, and this intersection agrees with the linear subspace of $\mathcal S_{00}(\mathbf A_{F,S})$ given by $\ker(\Phi_{F,S,\omega}|_{\mathcal S_{00}(\mathbf A_{F,S})})$.

It follows that $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$ equipped with the quotient topology, is a complete, Hausdorff locally convex topological $\mathbf C$-vector space.

Since $\mathcal S_{00}(\mathbf A_{F,S})$ is a closed subspace of $\mathcal S(\mathbf A_{F,S})$, and $\mathcal S(\mathbf A_{F,S})$ is a strict LF-space by Proposition 2.1.4.1(2), $\mathcal S_{00}(\mathbf A_{F,S})$ and hence $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$ equipped with the quotient topology are also LF-spaces.

By Lemma 5.4.1.3, $U_{S,\tau,\omega}$ from (5.4.1.7) is continuous, upon endowing its source $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$ with the quotient topology, since it is obtained as the composition of $U_{S,\tau,\omega}$ from (5.4.1.2) with the continuous linear inclusion $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S})) \subset \mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$.

## PDF page 269

**5.4. STRUCTURE THEOREM II: S-LOCAL ČECH SEQUENCE** · **269**

By Lemma 5.4.1.3, $U_{S,\tau,\omega}$ is a continuous bijection from the LF-space $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$ to the Fréchet space $V_{F,S,\omega}$. It is therefore a linear topological isomorphism by Köthe's Open Mapping Theorem (see [Gro-f, Ch.4,§5,Thm.2(1),p.148], and [SN, §2,Cor.3,p.8]). $\square$

Proof of Theorem 5.4.1.1. We will be deducing the Theorem in its general case, from the special case discussed in Proposition 5.4.1.4.

We first note that by Lemma 5.4.1.3, $U_{S,\tau,\omega}$ is continuous.

(1) : We rename $U_{S,\tau,\omega}$ from (5.4.1.2) as $U_S$ for simplicity.

To show that $U_S$ is indeed a linear topological embedding, we will be using the Principal Value Operators of Weil, discussed in §5.3.3 and in Proposition 5.3.4.5, as well as the multiplication operators from Proposition 5.3.3.4, and Proposition 5.3.4.4, to reduce to replacing $\mathcal S(\mathbf A_{F,S})$ with the closed subspace $\mathcal S_{00}(\mathbf A_{F,S})$, and $W_{F,S,\omega}$ with the closed subspace $V_{F,S,\omega}$ of those $(\phi, \psi)$ such that the unique meromorphic function $\widetilde\phi$ on the complex $s$-plane obtained by analytic continuation of $\phi$ from $\mathbf C_{>0}$ to $\mathbf C$ by the functional equation $\phi(s) = \rho_{S,\tau}(s)\psi(s)$, valid over $\mathbf C_{(0,1)}$, is entire.

This case is already settled in Proposition 5.4.1.4, and will finish the proof of Theorem 5.4.1.1.

We first verify that indeed $U_S$ is valued in $A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1})$.

To see this, we observe that, for a choice of continuous homomorphic section $\tau$ to the $S$-idelic norm, the Fourier transform

$$
Z_S(f, c) = \int_{\mathbf R_{>0}} t^{a+ix} \left(\int_{J^1_{F,S}} \omega(g)\Phi_{F,S}(f)(g)\, \mathrm{d}\overline{\mu}_{S,1}(g)\right) \frac{\mathrm{d}t}{t}
$$

for $a \in \mathbf R_{>0}$, and $c|\cdot|^{-a}_{F,S}$ corresponding to the pair $(\omega, x)$ under the resulting isomorphism of Hausdorff locally compact abelian topological groups $\widehat{J_{F,S}} \simeq \widehat{J^1_{F,S}} \times \mathbf R_{>0}$, is valued in $\mathcal S(\widehat{J_{F,S}}) \simeq \mathcal S(\mathbf R) \overline{\otimes} \mathcal S(\widehat{J^1_{F,S}})$. This holds for any $a > 0$, and so $\Phi_{F,S}$ composed with the Fourier transform on $J^1_{F,S}$, is valued in the Hausdorff locally convex topological $\mathbf C$-vector space of $(0, +\infty)$-exponentially decaying Schwartz-Bruhat functions on $J_{F,S}$, i.e. $\mathcal S_{(0,+\infty)}(\mathbf R_{>0}) \overline{\otimes} \mathcal S(\widehat{J^1_{F,S}})$ (see Definition B.2.1.1(1), and Theorem D.3.3.7(3). This is the completed inductive tensor product, for which we refer the reader to (C.2.3.23) and the subsequent discussion. We further refer the reader to Lemma D.1.8.1(1)).

This is so by Proposition 2.3.1.2 and Corollary 2.4.3.2.

The Fourier transform on the elements $\mathcal S_{(0,+\infty)}(\mathbf R_{>0})$ extends uniquely to a holomorphic function on $\mathbf C_{>0}$ (i.e. the Mellin transform of the same element of $\mathcal S_{>0}(\mathbf R_{>0})$) which is Schwartz uniformly on vertical strips of bounded width by Lemma B.2.1.5. This shows that $L_S$, followed by the restriction operator to the connected component of the Riemann surface $\Omega(J_{F,S})$ parametrized by $\omega \in \widehat{J^1_{F,S}}$, takes values in $A\mathcal S(\mathbf C_{>0})$.

The same argument applies to $Z_S(\widehat f, \widehat c)$ for any $f \in \mathcal S(\mathbf A_{F,S})$, and hence $U_S$ is valued in $A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1})$.

We choose a holomorphic parametrization of the connected component $\Omega(J_{F,S})(\omega)$, i.e. we choose a continuous character $\chi \in \widehat{J_{F,S}}$ and parametrize the connected component as $\chi|\cdot|^s_{F,S}$ for $s$ a global holomorphic coordinate. Up to linear topological isomorphism, $U_S$ is therefore isomorphic to the operator $f \mapsto (Z_S(f, \chi|\cdot|^s_{F,S}), Z_S(\widehat f, \overline{\chi}|\cdot|^{1-s}_{F,S}))$.

We now observe that by Proposition 5.3.4.5(1), combined with the fact that reciprocal non-Archimedean Euler factors of the Hecke $L$-function $L(c)$ are entire, and, with respect to any holomorphic parametrization $\chi|\cdot|^s_{F,S}$ of $\Omega(J_{F,S})(\omega)$ (i.e. for any given choice of $\chi \in \widehat{J_{F,S}}$ such that $\chi|_{J^1_{F,S}} = \omega$), have holomorphic derivatives of any order that are bounded any vertical strip of bounded width of the complex $s$-plane, the Principal Value Operator $\mathrm{PV}_{S,S_f}$ of Weil defined in Definition 5.3.1.4 on $\mathcal S(\mathbf A_{F,S})$ and descended to $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$, extends to the ambient $W_{F,S,\omega}$ to give a linear topological embedding on $W_{F,S,\omega}$ with closed range in $W_{F,S,\omega}$.

## PDF page 270

**270** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

Indeed, let $(\phi, \psi)$ be the arbitrary element of $W_{F,S,\omega}$. We then define:

$$
\widetilde{\mathrm{PV}}_{S,S_f}(\phi(s), \psi(s)) := \left(\frac{\phi(s)}{\prod_{v\in S_f} L_v(\chi_v|\cdot|^{s}_v)}, \frac{\psi(s)}{\prod_{v\in S_f} L_v(\chi_v|\cdot|^{s}_v)}\right). \tag{5.4.1.10}
$$

We note that the Fourier transform of $\mathrm{PV}_{S,S_f}(f)$ indeed satisfies

$$
Z_S(\mathcal F_S(\mathrm{PV}_{S,S_f}(f)), \overline{\chi}|\cdot|^{1-s}_{F,S}) = \prod_{v\in S_f} L_v(\chi_v|\cdot|^s_v)^{-1}Z_S(\widehat f, \overline{\chi}|\cdot|^{1-s}_{F,S}).
$$

This follows from the calculation:

$$
\widehat{1_{\mathcal O^\times_{F_v}}} = \widehat{1_{\mathcal O_{F_v}}} - \widehat{1_{\pi_v\mathcal O_{F_v}}} = N(\mathfrak d_{F_v/\mathbf Q_p})^{-1/2}1_{\mathfrak d^{-1}_{F_v/\mathbf Q_p}} - |\pi_v|_vN(\mathfrak d_{F_v/\mathbf Q_p})^{-1/2} \cdot 1_{\pi^{-1}_v\mathfrak d_{F_v/\mathbf Q_p}} \tag{5.4.1.11}
$$

for any choice of uniformizing element $\pi_v$ at $v \in S_f$.

The operator $\widetilde{\mathrm{PV}}_{S,S_f}$ therefore promotes the following diagram of continuous linear operators:

(5.4.1.12)

```latex
\begin{tikzcd}
\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S})) \arrow[r, "U_S"] \arrow[d, "\mathrm{PV}_{S,S_f}"'] & W_{F,S,\omega} \arrow[d, "\widetilde{\mathrm{PV}}_{S,S_f}"] \\
\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S})) \arrow[r, "U_S"'] & W_{F,S,\omega}
\end{tikzcd}
```

to a commutative diagram whose vertical arrows are linear topological embeddings with closed range. Note that $\widetilde{\mathrm{PV}}_{S,S_f}$ acts by multiplication by an entire function with holomorphic derivatives that are bounded on vertical strips of bounded width, and hence the range of $\widetilde{\mathrm{PV}}_{S,S_f}$ is sequentially closed since functions in this class are bounded multipliers on $A\mathcal S(\mathbf C_I)$ for any connected open interval $I \subset \mathbf R$, by [Sch-a, Ch.VII,§5,p.243].

By Proposition 5.3.4.5(3), the closed subspace $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ agrees with the linear image of $\mathcal S(\mathbf A_{F,S_\infty}) \otimes_\pi \bigotimes_{v\in S_f} \mathcal S(F^\times_v)$ under $\Phi_{F,S,\omega}$.

It is therefore enough to show that $U_S$ is surjective from $\Phi_{F,S,\omega}(\mathcal S(\mathbf A_{F,S_\infty}) \otimes_\pi \bigotimes_{v\in S_f} \mathcal S(F^\times_v))$ onto $\widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega})$.

We already know from Proposition 5.4.1.4 that the restriction of $U_S$ to $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$, i.e. the linear image of $\mathcal S_{00}(\mathbf A_{F,S}) \otimes_\pi \bigotimes_{v\in S_f} \mathcal S(F^\times_v)$, is surjective onto the closed subspace $V_{F,S,\omega}$. We note that $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S}))$ is contained in $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ and $V_{F,S,\omega}$ is contained in $\widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega})$, both as closed subspaces, and both by Proposition 5.3.4.5(1) and (3).

It therefore suffices to show that the induced continuous linear map:

$$
\bar U_S : \mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))/\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S})) \to \widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega})/V_{F,S,\omega}. \tag{5.4.1.13}
$$

is surjective.

The idea is to now exhibit a separated filtration on source and target of $\bar U_S$ from (5.4.1.13), compatible with $\bar U_S$, by closed subspaces, with finite dimensional subquotients, such that the Hausdorff locally convex topology on the source of $\bar U_S$ is equivalent to the projective topology induced by the quotient maps to the finite dimensional subquotients, and such topology is complete, for then showing that $\bar U_S$ induces $\mathbf C$-linear surjections (in fact isomorphisms) on the subquotients.

We choose an enumeration of $\Sigma_{F,r} = \{v_1, \ldots, v_{r_1}\}$ and $\Sigma_{F,c} = \{w_1, \ldots, w_{r_2}\}$, respectively, and order the tuples $(\underline{n}, \underline{p})$ lexicographically according to the chosen enumerations, i.e. $(\underline{n}, \underline{p}) \le (\underline{n}', \underline{p}')$ if and only if for every $\underline{n} \le \underline{n}'$ under the lexicographical ordering on $\mathbf N^{r_1}$, and $\underline{p} \le \underline{p}'$ under the lexicographical ordering on $\mathbf N^{r_2}$.

We choose an integer tuple $(\underline{n}, \underline{p})$ and define:

$$
\mathcal{U}_{\le(\underline{n},\underline{p})} := \bigcup_{1\le k\le r_1} \psi^{-1}_{v_k}(\mathcal{U}^{\le n_{v_k}}_{v_k}) \cup \bigcup_{1\le k\le r_2} \psi^{-1}_{w_k}(\mathcal{U}^{\le p_{v_k}}_{w_k}) \tag{5.4.1.14}
$$

## PDF page 271

**5.4. STRUCTURE THEOREM II: S-LOCAL ČECH SEQUENCE** · **271**

where $\mathcal{U}^{\le n_{v_k}}_{v_k}$ denotes the set of poles of the Euler factor $L_v(c_v)$ of the Hecke $L$-function $L(c)$ in $\Omega(F^\times_v)(\omega_v)$ whose ordinate $\sigma(c_{v_k})$ satisfies $\sigma(c_{v_k}) \ge -2n_{v_k} - \epsilon(c_{v_k})$ for $\epsilon(c_{v_k}) = 0$ if $\omega_{v_k}$ is trivial, and $\epsilon(c_{v_k}) = 1$ if $\omega_{v_k}$ is the sign character, and where $\mathcal{U}^{\le p_{w_k}}_{w_k}$ denotes the set of poles of the Euler factor $L_v(c_v)$ of the Hecke $L$-function $L(c)$ in $\Omega(F^\times_v)(\omega_v)$ whose ordinate $\sigma(c_{w_k})$ satisfies $\sigma(c_{w_k}) \ge -p_{w_k} - \epsilon(c_{w_k})$ where $\epsilon(c_{w_k}) = |n|/2$ if $\omega_{w_k} = c_n \in \widehat{\mathrm{U}(1)}$.

We define the two filtrations:

$$
F^{(\underline{n},\underline{p})}_S \subset \mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S})), \widetilde F^{(\underline{n},\underline{p})}_S \subset \widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega}) \tag{5.4.1.15}
$$

of those elements $\Phi_{F,S,\omega}(f) \in \mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$ whose $S$-idelic Mellin transform $Z_S(f, c)$ (which, recall from Lemma 5.1.2.2(2), only depends on $f$ through $\Phi_{F,S,\omega}(f)$) has no poles over $\mathcal{U}_{\le(\underline{n},\underline{p})}$, respectively of those elements $(\phi, \psi)$ of $\widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega})$ such that the unique analytic continuation of $\phi$ to the complex $s$-plane has no poles over $\mathcal{U}_{\le(\underline{n},\underline{p})}$.

We begin by observing that both $F^{(\underline{n},\underline{p})}_S$ and $\widetilde F^{(\underline{n},\underline{p})}_S$ are the countable intersection of the kernels of continuous functionals on $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$, respectively $W_{F,S,\omega}$.

The functionals on $W_{F,S,\omega}$ are defined as follows: for $(\phi, \psi)$ the arbitrary element of $W_{F,S,\omega}$ and $\widetilde\phi(s)$ the unique analytic continuation of $\phi$ to the complex $s$-plane which parametrizes the connected component of $\Omega(J_{F,S})$ over $\omega$ under the chosen holomorphic parametrization $\chi|\cdot|^s_{F,S}$, for $c \in \mathcal{U}_{\le(\underline{n},\underline{p})}$ parametrized by $\chi|\cdot|^{s_c}_{F,S}$ a pole of order $N_c$ of $\rho_S(\chi|\cdot|^s_{F,S})$ we define:

$$
a_m(c)(\phi, \psi) := \lim_{s\to s_c}(s - s_c)^m\widetilde\phi(s)
$$

the $m$th coefficient of the Laurent series expansion of $\widetilde\phi$ at $s = s_c$, for each integer $1 \le m \le N_c$.

This induces a functional on $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$ by composition with the operator $U_S$. Since $U_S$ is continuous, it is enough to show that $a_m$ is continuous on $W_{F,S,\omega}$, and we will deduce from this that indeed both $F^{(\underline{n},\underline{p})}_S$ and $\widetilde F^{(\underline{n},\underline{p})}_S$ are the countable intersections $\bigcap_{(\underline{n}',\underline{p}')\le(\underline{n},\underline{p})} \bigcap_{c\in \mathcal{U}^{\le(\underline{n}',\underline{p}')}} a_m(c)$, respectively $\bigcap_{(\underline{n}',\underline{p}')\le(\underline{n},\underline{p})} \bigcap_{c\in \mathcal{U}^{\le(\underline{n}',\underline{p}')}} a_m(c) \circ U_S$.

Note that since for each $(\underline{n}', \underline{p}') \le (\underline{n}, \underline{p})$ we have $\mathcal{U}^{\le(\underline{n}',\underline{p}')} \subset \mathcal{U}^{\le(\underline{n},\underline{p})}$, we have:

$$
\widetilde F^{(\underline{n},\underline{p})}_S = \bigcap_{c\in \mathcal{U}_{\le(\underline{n},\underline{p})}} a_m(c), \quad F^{(\underline{n},\underline{p})}_S = \bigcap_{c\in \mathcal{U}_{\le(\underline{n},\underline{p})}} a_m(c).
$$

To conclude that $\widetilde F^{(\underline{n},\underline{p})}_S$ and $F^{(\underline{n},\underline{p})}_S$ are closed subspaces, it is enough to show that the functionals $a_m(c)$ are continuous on $W_{F,S,\omega}$. Since the topology on $W_{F,S,\omega}$ induced by the product topology on $A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{<1})$ induces, under the linear operator sending $(\phi, \psi)$ to $\widetilde\phi \in \mathscr{M}_{\mathcal{U}}(\mathbf C)$, the linear space of meromorphic functions on the complex $s$-plane whose poles are located at the points of $\bigcup_{(\underline{n},\underline{p})} \mathcal{U}^{\le(\underline{n},\underline{p})}$, a Hausdorff locally convex topology that is finer than the topology of uniform convergence on compact subsets away from the poles, it is enough to show that each of the functionals $a_m(\chi|\cdot|^s_{F,S})$ is continuous on $\mathscr{M}_{\mathcal{U}}(\mathbf C)$ with respect to the Hausdorff locally convex topology of uniform convergence on compact subsets away from $\mathcal{U} \subset \mathbf C$ (using the chosen holomorphic parametrization for $\Omega(J_{F,S})(\omega)$ to parametrize the points in $\mathcal{U}$).

Continuity of each $a_m(\chi|\cdot|^s_{F,S})$ indeed holds with respect to this topology by Cauchy's Residue Theorem (see [Ahl, Ch.4,§5,Thm.17,p.150]) applied to $(s-s_c)^{m-1}\widetilde\phi$ and combined with Dominated Convergence, applied to the integral of $(s - s_c)^{m-1}\widetilde\phi$ along a rectifiable simple closed curve enclosing $s_c$.

We deduce that each $F^{(\underline{n},\underline{p})}_S$ and $\widetilde F^{(\underline{n},\underline{p})}_S$ are closed and of finite codimension (since each $\mathcal{U}^{\le(\underline{n},\underline{p})} \subset \Omega(J_{F,S})(\omega)$ contains only finitely many points) in their respective ambients $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$ and $\widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega})$.

## PDF page 272

**272** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

We now show that we have:

$$
\bigcap_{(\underline{n},\underline{p})} F^{(\underline{n},\underline{p})}_S = \Phi_{F,S,\omega}(\mathcal S_{00}(\mathbf A_{F,S})). \tag{5.4.1.16}
$$

Let $(\underline{n}, \underline{p})$ be an arbitrary $(\Sigma_{F,r}, \Sigma_{F,c})$-indexed tuple of nonnegative integers.

Let $f \in \mathrm{PV}_{S,S_f}(\mathcal S(\mathbf A_{F,S}))$ be such that $\Phi_{F,S,\omega}(f) \in F^{(\underline{n},\underline{p})}_S$. Then $Z_S(f, c)$ has no poles over $\mathcal{U}^{\le(\underline{n},\underline{p})}$ within the connected component $\Omega(J_{F,S})(\omega)$.

Since all the poles that $Z_S(f, c)$ can have on the connected component $\Omega(J_{F,S})(\omega)$ are contained in the countable union:

$$
\bigcup_{(\underline n,\underline p)}\left\{\bigcup_{1\le k\le r_1} \psi^{-1}_{v_k}(\mathcal{U}^{\le n_{v_k}}_{v_k}) \cup \bigcup_{1\le k\le r_2} \psi^{-1}_{w_k}(\mathcal{U}^{\le p_{v_k}}_{w_k})\right\}
$$

we deduce that $Z_S(f, c)$ is entire over the connected component $\Omega(J_{F,S})(\omega)$.

By Proposition 5.3.4.4(3), there exists $f_1 \in \mathcal S_{00}(\mathbf A_{F,S})$ such that $\Phi_{F,S,\omega}(f_1) = \Phi_{F,S,\omega}(f)$, which shows that the closed subspace in the left side of (5.4.1.16) is contained in $\Phi_{F,S,\omega}(\mathcal S_{00}(\mathbf A_{F,S}))$.

Similarly, within $\widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega})$, the closed subspace:

$$
\bigcap_{(\underline{n},\underline{p})} \widetilde F^{(\underline{n},\underline{p})}_S \subset \widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega}) \tag{5.4.1.17}
$$

is the closed subspace of those elements $(\phi, \psi)$ such that the resulting unique analytic continuation $\widetilde\phi$ of $\phi$ to the complex $s$-plane has no poles in the subset $\mathcal{U}_{\le(\underline{n},\underline{p})}$ from (5.4.1.14) for any $(\underline{n}, \underline{p})$.

We therefore also have $\bigcap_{(\underline{n},\underline{p})} \widetilde F^{(\underline{n},\underline{p})}_S = V_{F,S,\omega}$.

By design of $F^{(\underline{n},\underline{p})}_S$, we have:

$$
F^{(\underline{n},\underline{p})}_S = U_S^{-1}(\widetilde F^{(\underline{n},\underline{p})}_S) \tag{5.4.1.18}
$$

for any $(\underline{n}, \underline{p})$.

We define:

$$
H := \mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))/\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S})) \tag{5.4.1.19}
$$

endowed with the quotient topology and the induced filtration $\bar F^{(\underline{n},\underline{p})}_S$, and similarly:

$$
\widetilde H := \widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega})/V_{F,S,\omega} \tag{5.4.1.20}
$$

endowed with the quotient topology and the filtration induced by $\widetilde F^{(\underline{n},\underline{p})}_S$, which we denote $\mathscr{F}^{(\underline{n},\underline{p})}_S$.

Each $\overline{F}^{(\underline{n},\underline{p})}_S$ carries the quotient topology, and it has finite codimension in $H$. Indeed, $\overline{F}^{(\underline{n},\underline{p})}_S = \overline{U}_S^{-1}(\mathscr{F}^{(\underline{n},\underline{p})}_S)$, since $U_S^{-1}(V_{F,S,\omega}) = \Phi_{F,S,\omega}(\mathcal S_{00}(\mathbf A_{F,S}))$ by Proposition 5.3.4.4(3), and $U_S(\Phi_{F,S,\omega}(\mathcal S_{00}(\mathbf A_{F,S}))) = V_{F,S,\omega}$ by Proposition 5.4.1.4, and so the linear map $\overline{F}^{(\underline{n},\underline{p})}_S \to \mathscr{F}^{(\underline{n},\underline{p})}_S$ induced by $\underline{U}_S$ (which, in turn, is the operator $H \to \widetilde H$ induced by $U_S$), is injective, showing that each $\overline{F}^{(\underline{n},\underline{p})}_S$ has finite codimension in $H$, and is therefore closed with respect to the subspace topology inherited from $H$, by [NB, Thm.7.3.5].

A similar argument implies that the quotient topology and the subspace topology on $\mathscr{F}^{(\underline{n},\underline{p})}_S$ inherited from $\widetilde H$ agree, and $\mathscr{F}^{(\underline{n},\underline{p})}_S$ is closed in $\widetilde H$.

The filtration $\{\overline{F}^{(\underline{n},\underline{p})}_S\}_{(\underline{n},\underline{p})}$ induces on $H$ a locally convex topology: the projective topology induced by the collection of all quotient maps $H \to H/\bar F^{(\underline{n},\underline{p})}_S$. This topology is Hausdorff, because $\bigcap_{(\underline{n},\underline{p})} \overline{F}^{(\underline{n},\underline{p})}_S = 0$, as a consequence of (5.4.1.16).

## PDF page 273

**5.4. STRUCTURE THEOREM II: S-LOCAL ČECH SEQUENCE** · **273**

It agrees with the projective limit topology induced by the $H \to H/\bar F^{(\underline{n},\underline{p})}_S$: indeed, the ordering on the integer tuples $(\underline{n}, \underline{p})$, promotes the collection of quotient maps $H \to H/\bar F^{(\underline{n},\underline{p})}_S$ to a cofiltered diagram, and the projective limit topology on $H$ is metrizable. Its completion $\widehat H$ is a Fréchet space, surjecting on the complete Hausdorff locally convex topological $\mathbf C$-vector space $H$ by [Jar, Part I,Ch.3,§3.4,Thm.2,p.61]. Since $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ is an LF-space, so are its closed subspaces and its quotient by closed subspaces, and hence so is $H$.

By Köthe's Open Mapping Theorem (see [Gro-f, Ch.4,§5,Thm.2(1),p.148], and [SN, §2,Cor.3,p.8]), the continuous surjective linear operator $\widehat H \to H$ is open, hence a linear topological isomorphism. The same argument applies to $\widetilde H$, which is therefore seen to carry the projective limit topology induced by the surjective quotient maps $\widetilde H \to \widetilde H/\mathscr{F}^{(\underline{n},\underline{p})}_S$ with finite dimensional range.

We have proved that $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ and $\widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega})$ fit into the following commutative diagram of continuous linear operators:

(5.4.1.21)

```latex
\begin{tikzcd}
\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S_{00}(\mathbf A_{F,S})) \arrow[r, "U_S"] \arrow[d] & V_{F,S,\omega} \arrow[d] \\
\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S})) \arrow[r, "U_S"] \arrow[d] & \widetilde{\mathrm{PV}}_{S,S_f}(W_{F,S,\omega}) \arrow[d] \\
H \arrow[r, "\bar U_S"'] & \widetilde H
\end{tikzcd}
```

The vertical columns in (5.4.1.21) are exact in the strict sense (i.e. the topmost Hausdorff locally convex topological $\mathbf C$-vector spaces are closed in the middle spaces, respectively, and the bottom vertical arrows are surjective quotient linear operators).

By Proposition 5.4.1.4, we have that the topmost horizontal arrow is a linear topological isomorphism. The middle horizontal arrow is continuous and injective, and so is the bottom horizontal arrow.

In order to show that the middle horizontal arrow is a linear topological isomorphism, it is enough to show that $\bar U_S$ is.

To see this, it is enough to show that the induced maps on the subquotients:

$$
H/\bar F^{(\underline{n},\underline{p})}_S \to \widetilde H/\mathscr{F}^{(\underline{n},\underline{p})}_S \tag{5.4.1.22}
$$

which we already know to be injective, are also surjective, being source and target finite dimesional.

To this end, it is enough to exhibit Schwartz-Bruhat functions in $\mathcal S(\mathbf A_{F,S})$ whose image under $\Phi_{F,S,\omega}$ has prescribed poles and orders of poles at the points of each $\mathcal{U}^{\le(\underline{n},\underline{p})}$.

Each local character $\omega_v = \chi_v|_{\{u\in F^\times_v : |u|_v=1\}}$ for each Archimedean place $v$, uniquely determines a Schwartz-Bruhat function $f_v$ on $F_v$ whose local $L$-function is the $\Gamma$-factor at $v$. We refer the reader to [CF, Ch.XV,§2.5,pp.316-319] and [RV, Ch.7,§7.1,pp.249-253] for the explicit definition of such functions, satisfying the self-duality properties in [CF, Ch.XV,§2.5,pp.316-319] with respect to the real and complex Fourier transforms.

Enough many Schwartz-Bruhat functions in $\mathcal S(\mathbf A_{F,S})$ such that their images under $\Phi_{F,S,\omega}$ and the quotient map to $H/\bar F^{(\underline{n},\underline{p})}_S$ composed with the injective linear map to $\widetilde H/\mathscr{F}^{(\underline{n},\underline{p})}_S$ linearly generate $\widetilde H/\mathscr{F}^{(\underline{n},\underline{p})}_S$, are obtained as follows.

## PDF page 274

**274** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

We consider a tuple of nonnegative integers $(\underline{n}, \underline{p}) = ((n_v)_{v\in\Sigma_{F,r}}, (p_v)_{v\in\Sigma_{F,c}})$ where $\Sigma_{F,r}$ denotes the real places of $F$, and $\Sigma_{F,c}$ denotes the complex places, and define the linear map:

$$
M_{(\underline{n},\underline{p})} := \bigotimes_{v\in\Sigma_{F,r}} M_{x^{2n_v}_v} \otimes \bigotimes_{v\in\Sigma_{F,c}} M_{z^{p_v}_v\bar z^{p_v}_v} : \mathcal S(\mathbf A_{F,S_\infty}) \to \mathcal S(\mathbf A_{F,S_\infty}). \tag{5.4.1.23}
$$

We further define

$$
M^S_{(\underline{n},\underline{p})} := M_{(\underline{n},\underline{p})} \otimes \bigotimes_{v\in S_f - S_\chi} 1_{\mathcal O^\times_{F_v}} \otimes \bigotimes_{v\in S_\chi} \omega^{-1}_v 1_{\mathcal O^\times_{F_v}} : \mathcal S(\mathbf A_{F,S_\infty}) \to \mathcal S(\mathbf A_{F,S_\infty}) \otimes \bigotimes_{v\in S_f} \mathcal S(F^\times_v)
$$

and, upon calling $f_\infty := \bigotimes_{v\in S_\infty}f_v$ for $f_v \in \mathcal S(F_v)$ the above choice of "self-dual" Schwartz-Bruhat function, the Schwartz-Bruhat functions on $\mathbf A_{F,S}$ obtained as $M^S_{(\underline{n}',\underline{p}')}(f_\infty)$ for each $(\underline{n}', \underline{p}') \le (\underline{n}, \underline{p})$, satisfy the desired spanning properties (see Proposition 5.3.3.4).

This proves that $\bar U_S$ is surjective, hence a linear topological isomorphism, which proves that the middle horizontal arrow in (5.4.1.21) is also a linear topological isomorphism. In turn, we proved that this suffices to show that $U_S$ from (5.4.1.2) is a linear topological isomorphism, finishing the proof of Theorem 5.4.1.1.

(2) : $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ is a nuclear Fréchet space since $U_S$ is a linear topological embedding of $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ into a Fréchet space, making $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ metrizable, hence Fréchet. It is nuclear by Theorem 5.2.3.1. It is separable by Lemma D.3.1.2. $\square$

Remark 5.4.1.5. We recall from the First Structure Theorem (see Theorem 5.2.1.1), that the Hausdorff locally convex topological $\mathbf C$-vector space $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$ is complete, nuclear, Montel, and its strong dual satisfies the same properties. It is an LF-space. From Theorem 5.4.1.1(4) we have that $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_{F,S}))$ is a Fréchet space,. In particular, $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_F))$ is itself realized as a strict LF-space, improving on Theorem 5.2.1.1. We shall see that the transition operators $\overline{\pi}_S$ are eventually surjective, and hence, since they are linear topological embeddings, $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_F))$ will be realized as itself a nuclear Fréchet space.

**5.4.2. S-local Čech sequences.** Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places of $F$. The Fourier transform $\mathcal F_S$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$ defined in (5.2.4.1) is continuous with respect to the normed topology on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$ induced by the continuous seminorm:

$$
\|\phi\|_{2,S} := \left(\int_{J_{F,S}} |\phi(g)|^2 |g|_{F,S}\, \mathrm{d}\overline{\mu}_S(g)\right)^{1/2}. \tag{5.4.2.1}
$$

This can be seen as a consequence of Theorem 3.3.1.5: indeed, for any $f \in \mathcal S(\mathbf A_{F,S})$, we have:

$$
Z_S(f, c) = \rho_S(c)Z_S(\widehat f, \widehat c)
$$

by (3.3.1.2) from Theorem 3.3.1.1, and since $\rho_S(c) \in \mathrm{U}(1)$ by Theorem 3.3.1.5(2) for any $c \in \Omega(J_{F,S})$ with $\sigma(c) = 1/2$, we deduce that $\mathcal F_S$ is in fact unitary with respect to $\|\cdot\|_{2,S}$.

The extension of $\mathcal F_S$ to the completion $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$ with respect to $\|\cdot\|_{2,S}$, which we denote by:

$$
L^2\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S})) \tag{5.4.2.2}
$$

is a linear topological automorphism and a unitary isometry, compatible with passage to $J^1_{F,S}$-isotypes.

We conclude this section by showing that the Fourier transform on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$ extends to other Hausdorff locally convex topological $\mathbf C$-vector spaces of smooth functions on $J_{F,S}$, other than the Hilbert space $L^2\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$.

Principal tool to conduct this analysis is the $S$-idelic Mellin transform $L_S$ (see (5.4.1.1)) and the $S$-local functional equation from (3.3.1.2) of Theorem 3.3.1.1.

## PDF page 275

**5.4. STRUCTURE THEOREM II: S-LOCAL ČECH SEQUENCE** · **275**

As an application, we will be reformulating, in the next subsection, the Second Structure Theorem (see Theorem 5.4.1.1) using spaces of Schwartz-Bruhat functions on $J_{F,S}$ with $I$-exponential decay (see Definition D.3.3.1 and Theorem D.3.3.7), by means of the $S$-local Mellin transform $L_S$.

Proposition 5.4.2.1 (S-local Fourier transform and $I$-exponential decay). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\chi \in \widehat{J_{F,S}}$ be a continuous character. Let $I \subset (0, 1)$ be an open connected interval.*

Then:

(1) *The Fourier transform $\mathcal F_S$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$ extends by continuity to a linear topological isomorphism:*

$$
\mathcal F_S : \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) \to \mathcal S_{1-I}(J_{F,S})(\bar\chi|_{J^1_{F,S}}). \tag{5.4.2.3}
$$

(2) *If $1/2 \in I$, then the Hausdorff locally convex topological $\mathbf C$-vector space $\mathcal S_I(J_{F,S})$ of Schwartz-Bruhat functions on $J_{F,S}$ with $I$-exponential decay, admits a continuous injective linear operator into $L^2\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$, and the Fourier transform $\mathcal F_S$ on*

$$
L^2\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))
$$

restricts to $\mathcal F_S$ from (5.4.2.3) on $\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$.

Proof. (1) : We choose a continuous homomorphic section $\tau : \mathbf R_{>0} \to J_{F,S}$ to the $S$-idelic norm, and we denote by $x_0$ the unique real number such that $\chi(\tau(t)) = t^{ix_0}$ as smooth functions of $t \in \mathbf R_{>0}$. For $\phi \in \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$, the Fourier transform

$$
\mathcal F(\phi)(x) = \int_{\mathbf R_{>0}} \phi(\tau(t))t^{ix}\,\frac{\mathrm{d}t}{t}
$$

extends to $M_I(\phi)(s) = \int_{\mathbf R_{>0}} \phi(\tau(t))t^s\,\frac{\mathrm{d}t}{t}$ by Theorem D.3.3.7 (see also Proposition D.3.2.5) for $\mathrm{Re}(s) \in I$, with $M(\phi)(s)$ holomorphic over $\mathbf C_I$ and Schwartz uniformly on every vertical strip of bounded width strictly contained within $\mathbf C_I$.

We let $\{\phi_m\}_{m\ge 0} \in \mathcal D(J_{F,S})(\chi|_{J^1_{F,S}})$ be such that $\phi_m \to \phi$ in $\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$, which is possible by Lemma D.3.6.1.

It follows that on every vertical line strictly contained within $\mathbf C_I$, parametrized as $\sigma + ix_0 + i\mathbf R$, $M_I(\phi_m) \to M_I(\phi)$ in the sense of Schwartz functions on the real line.

Since each $\phi_m$ is of the form $\Phi_{F,S}(\psi_m)$ for a smooth compactly supported test function on $\mathrm{GL}_1(\mathbf A_{F,S})$ extended by zero to a Schwartz-Bruhat function on $\mathbf A_{F,S}$, we have $M_I(\phi_m)(s + ix_0) = Z_S(\psi_m, \chi|\cdot|^s_{F,S})$ as entire functions on the complex $s$-plane, since $\phi_m \in \mathcal S_\mathrm{E}(J_{F,S})(\chi|_{J^1_{F,S}})$, and hence $M_I(\phi_m) = M_{\mathbf R}(\phi_m)$ is entire on the complex $s$-plane by Proposition D.3.2.5.

By the $S$-local functional equation from (3.3.1.2) of Theorem 3.3.1.1, we have, for each integer $m \ge 0$ and as meromorphic functions on the complex $s$-plane:

$$
Z_S(\psi_m, \chi|\cdot|^s_{F,S}) = \rho_S(\chi|\cdot|^s_{F,S}) Z_S(\widehat{\psi_m}, \overline{\chi}|\cdot|^{1-s}_{F,S}) \tag{5.4.2.4}
$$

For every real number $\sigma \in I$, we therefore have:

$$
Z_S(\widehat{\psi_m}, \overline{\chi}|\cdot|^{1-\sigma-ix}_{F,S}) = \frac{Z_S(\psi_m, \chi|\cdot|^{\sigma+ix}_{F,S})}{\rho_S(\chi|\cdot|^{\sigma+ix}_{F,S})} = \frac{M_I(\phi_m, \sigma + ix + ix_0)}{\rho_S(\chi|\cdot|^{\sigma+ix}_{F,S})} \tag{5.4.2.5}
$$

as meromorphic functions on the complex $(\sigma, x) = s$-plane. Indeed, $\rho_S(\chi|\cdot|^s_{F,S})$ is nowhere vanishing over $\mathbf C_{(0,1)}$ and grows at most polynomially over each vertical line of $\mathbf C_{(0,1)}$, as do all of its holomorphic derivatives (see Proposition 3.3.1.5).

## PDF page 276

**276** · **CHAPTER 5. SPACES OF ADELIC $\theta$-FUNCTIONS AND IDELIC Z-FUNCTIONS**

We define $\mathcal F_S(\phi)$ to be the limit in $\mathcal S_{1-I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ of the functions $\Phi_{F,S}(\widehat{\psi_m}) = \mathcal F_S(\Phi_{F,S}(\psi_m)) = \mathcal F_S(\phi_m)$. We have just shown that $\mathcal F_S$ is continuous with respect to the Hausdorff locally convex topology on $\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$ on the source, and the Hausdorff locally convex topology on $\mathcal S_{1-I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ on the target, and since it has a continuous inverse given by $\mathcal F_S$ itself, which is its own inverse on the dense linear subspace $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$, we deduce that $\mathcal F_S$ is a linear topological isomorphism as in (5.4.2.3).

(2) : Since $1/2 \in I$, for any $\phi \in \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$ we have $|\cdot|^{1/2}_{F,S}\phi \in \mathcal S(J_{F,S})(\chi|_{J^1_{F,S}})$. In particular, $\phi \in L^2(J_{F,S}, |\cdot|_{F,S}\overline{\mu}_S)(\chi|_{J^1_{F,S}})$.

Since $|\cdot|^{1/2}_{F,S}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S})) \subset L^2(J_{F,S}, \overline{\mu}_S)$ is dense, since it contains $C^\infty_c(J_{F,S})$, we deduce that the continuous linear inclusion $|\cdot|^{1/2}_{F,S}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S})) \subset L^2(J_{F,S}, |\cdot|_{F,S}\overline{\mu}_S)(\chi|_{J^1_{F,S}})$ extends by continuity to a linear topological embedding

$$
L^2\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S})) \to L^2(J_{F,S}, |\cdot|_{F,S}\overline{\mu}_S)(\chi|_{J^1_{F,S}})
$$

with dense range, hence a linear topological isomorphism between Hilbert spaces (in fact, up to pre-composing by $c_S\mathrm{Id}$, a surjective isometry).

We deduce that the injective continuous linear operator $\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) \to L^2(J_{F,S}, |\cdot|_{F,S}\overline{\mu}_S)(\chi|_{J^1_{F,S}})$ factors through $L^2\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$. By (1), the result follows upon observing that $\mathcal F_S$ on $L^2\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$ restricts to $\mathcal F_S$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S}, \mathcal S(\mathbf A_{F,S}))$. $\square$

Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

We can now rephrase the Second Structure Theorem (see Theorem 5.4.1.1) into the following form:

Theorem 5.4.2.2 (S-local Čech sequences). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places. Let $\chi \in \widehat{J_{F,S}}$ be a continuous character. Let $\tau$ be a choice of continuous homomorphic section to the $S$-idelic norm. We define $x_0 \in \mathbf R$ to be the unique real number such that $\chi(\tau(t)) = t^{ix_0}$ as smooth functions of $t \in \mathbf R_{>0}$.*

*We define the interval $I := (0, +\infty) \subset \mathbf R$, noting that we have $1 - I = (-\infty, 1)$, and $I \cap (1 - I) = (0, 1)$.*

*The following diagram of continuous linear operators:*

(5.4.2.6)

```latex
\begin{tikzcd}
\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S})) \arrow[r, "{(\mathrm{Id},\mathcal F_S)}"] \arrow[d, equal] & \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) \times \mathcal S_I(J_{F,S})(\bar\chi|_{J^1_{F,S}}) \arrow[r, "\mathrm{pr}_1-\widetilde{\mathrm{pr}}_2"] \arrow[d, "{(M_{I,\tau},M_{I,\tau})}"] & \mathcal S_{I\cap(1-I)}(\mathbf R_{>0}) \arrow[d, "T_{ix_0}\circ M_{I\cap(1-I)}"] \\
\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S})) \arrow[r, "{(L_S,L_S\circ\mathcal F_S)}"'] & A\mathcal S(\mathbf C_{>0}) \times A\mathcal S(\mathbf C_{>0}) \arrow[r, "\mathrm{pr}_1-\widetilde{J}\circ\mathrm{pr}_2"'] & A\mathcal S(\mathbf C_{I\cap(1-I)})
\end{tikzcd}
```

*for:*

*(1) $M_{I,\tau} : \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) \to A\mathcal S(\mathbf C_I)$ is the Mellin transform operator from Theorem D.3.3.7 (see also Proposition D.3.2.5), defined as $M_{I,\tau}(\phi) := \int_{\mathbf R_{>0}} \phi(\tau(t))t^{s+ix_0}\,\frac{\mathrm{d}t}{t}$ for $\mathrm{Re}(s) \in I$, and similarly for $M_{I,\tau}$ on $\mathcal S_I(J_{F,S})(\bar\chi|_{J^1_{F,S}})$.*

*(2) $J_\tau : \mathcal S_I(J_{F,S})(\bar\chi|_{J^1_{F,S}}) \to \mathcal S_I(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ the linear topological isomorphism uniquely determined by sending $\phi \in \mathcal S_{1-I}(J_{F,S})(\bar\chi|_{J^1_{F,S}})$ as a function of $\tau(t)g_0$ for unique $t \in \mathbf R_{>0}$ and $g_0 \in J^1_{F,S}$, to the function $t^{-1}\phi(\tau(t)^{-1}g_0)$, which is an element of $\mathcal S_{1-I}(J_{F,S})(\bar\chi|_{J^1_{F,S}})$.*

*(3) $\widetilde{J} : A\mathcal S(\mathbf C_I) \to A\mathcal S(\mathbf C_{1-I})$ the linear topological isomorphism sending an element $\phi \in A\mathcal S(\mathbf C_I)$ to the holomorphic function $\widetilde{J}(\phi)(s) := \rho_S(\chi|\cdot|^s_{F,S})\phi(1 - s)$ on $\mathbf C_{1-I}$.*

*(4) $\widetilde{\mathrm{pr}}_2$ is the projection onto $\mathcal S_I(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, followed by the operator $M_{I,\tau}^{-1} \circ M_{\rho_S} \circ M_{I,\tau}$, where $M_{\rho_S}$ is the multiplication operator by $\rho_S(\chi|\cdot|^s_{F,S})$ on $A\mathcal S(\mathbf C_I)$.*

## PDF page 277

**5.5. STRUCTURE THEOREM III: STRONG DUALS AND EIGENDISTRIBUTIONS** · **277**

(5) *The operator $\mathrm{pr}_1-\widetilde{\mathrm{pr}}_2$ is the operator sending $(\phi,\psi)\in\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})\times\mathcal S_I(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, to the pair $(\phi,\widetilde\psi:=\widetilde{\mathrm{pr}}_2(\phi,\psi))$, further sent to the pair of elements of $\mathcal S_{I\cap(1-I)}(\mathbf R_{>0})$ defined by $(\phi(\tau(t)),\widetilde\psi(\tau(t)))$, further sent to their difference.*

(6) *$T_{ix_0}$ is the vertical translation by $ix_0$ linear topological automorphism on $A\mathcal{S}(\mathbf C_{I\cap(1-I)})$.*

*is commutative, the vertical arrows are linear topological isomorphisms, the leftmost horizontal arrows are linear topological embeddings with closed range, and both rows are exact on the left and in the middle.*

We refer to the short-exact sequences of (5.4.2.6) as the $S$-local Čech sequences. Indeed, it exhibits the isotype $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ as a space of meromorphic functions on the connected component of $\Omega(J_{F,S})$ parametrized by $\chi|_{J^1_{F,S}}$, upon choosing the holomorphic parametrization $\chi|\cdot|^s_{F,S}$ for such connected component.

Remark 5.4.2.3. Let $F$ be a number field, $S$ a finite set of finite places of $F$ containing all the Archimedean places. Let $\chi\in\widehat{J_{F,S}}$ be a continuous character.

Theorem 5.4.2.2 is a way of rephrasing Theorem 5.4.1.1, the dictionary being the Mellin transform $M_I:\mathcal S_I(\mathbf R_{>0})\to A\mathcal{S}(\mathbf C_I)$ for any non-empty connected open interval $I\subset\mathbf R$ (up to a vertical translation by $ix_0$ for a unique $x_0\in\mathbf R$, through the global holomorphic coordinate $\mathbf C_I$ prescribed by the equation $\chi(\tau(t))=t^{ix_0}$ for all $t\in\mathbf R_{>0}$.

We define $I:=(0,+\infty)\subset\mathbf R$.

We will, however, highlight here how it implies that the continuous linear map:

$$
(\mathrm{Id},\mathcal F_S):\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))\to\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})\times\mathcal S_I(J_{F,S})(\overline{\chi}|_{J^1_{F,S}}) \tag{5.4.2.7}
$$

sending $\phi$ to $(\phi,\mathcal F_S(\phi))$, is a linear topological embedding with closed range.

Proof. By Proposition 5.4.2.1 and Theorem D.3.3.13, the Theorem follows from the Second Structure Theorem (see Theorem 5.4.1.1). $\square$

**5.5. Structure Theorem III: strong duals and Eigendistributions**

Let $F$ be a number field, $S$ a finite set of places containing all Archimedean places of $F$.

In this section we prove a Structure Theorem describing the strong duals of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ in terms of Weil’s eigendistributions, providing the tools to prove the remaining of the Structure Theorems, resting on group homology calculations.

**5.5.1. Eigendistributions and the strong duals of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$.**

Building on work of Weil on eigendistributions (see [Weil-a]), we assign the following:

Definition 5.5.1.1. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places.

(1) We say a tempered distribution $T\in\mathcal S(\mathbf A_{F,S})'_\beta$ is an $S$-local eigendistribution of weight $c\in\Omega(J_{F,S})$ if and only if

$$
\langle T,\rho_{F,S}(g,f)\rangle_{\mathcal S(\mathbf A_{F,S})'_\beta,\mathcal S(\mathbf A_{F,S})}=c(g)\langle T,f\rangle_{\mathcal S(\mathbf A_{F,S})'_\beta,\mathcal S(\mathbf A_{F,S})} \tag{5.5.1.1}
$$

for every $f\in\mathcal S(\mathbf A_{F,S})$ and $g\in\mathrm{GL}_1(\mathbf A_{F,S})$. Equivalently, if and only if:

$$
\rho'_{F,S}(g,T)=c(g)T \tag{5.5.1.2}
$$

for every $g\in\mathrm{GL}_1(\mathbf A_{F,S})$, where $\rho'_{F,S}$ is the adjoint action of $\mathrm{GL}_1(\mathbf A_{F,S})$ on $\mathcal S(\mathbf A_{F,S})'_\beta$.

We define $\mathcal S(\mathbf A_{F,S})'_\beta(c)$ to be the closed subspace of eigendistributions of weight $c$, endowed with the subspace topology.

## PDF page 278

**278** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

(2) We say a tempered distribution $T\in\mathcal S(\mathbf A_F)'_\beta$ is a global eigendistribution of weight $c\in\Omega(C_F)$ if and only if

$$
\langle T,\rho_F(g,f)\rangle_{\mathcal S(\mathbf A_F)'_\beta,\mathcal S(\mathbf A_F)}=c(g)\langle T,f\rangle_{\mathcal S(\mathbf A_F)'_\beta,\mathcal S(\mathbf A_F)} \tag{5.5.1.3}
$$

for every $f\in\mathcal S(\mathbf A_F)$ and $g\in\mathrm{GL}_1(\mathbf A_F)$. Equivalently, if and only if:

$$
\rho'_F(g,T)=c(g)T \tag{5.5.1.4}
$$

for every $g\in\mathrm{GL}_1(\mathbf A_F)$, where $\rho'_F$ is the adjoint action of $\mathrm{GL}_1(\mathbf A_F)$ on $\mathcal S(\mathbf A_F)'_\beta$. We define $\mathcal S(\mathbf A_F)'_\beta(c)$ to be the closed subspace of eigendistributions of weight $c$, endowed with the subspace topology.

In a similar vein as in [Weil-a], we now classify $S$-local eigendistributions of weight $c\in\Omega(J_{F,S})$. We will later classify the global eigendistributions of weight $c\in\Omega(C_F)$.

Theorem 5.5.1.2. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places.*

*(1) For $\Delta'(c)$ the eigendistribution of weight $c$ defined as:*

$$
\Delta'(c):=\bigotimes_{v\in S}\Delta'_v(c) \tag{5.5.1.5}
$$

*for $\Delta'_v$ the local eigendistribution constructed in [Weil-a, §1], we have:*

$$
\mathcal S(\mathbf A_{F,S})'_\beta(c)=\mathbf C\cdot\Delta'(c). \tag{5.5.1.6}
$$

*Moreover, formation of $\Delta'(c)$ is holomorphic as a function of $c\in\Omega(J_{F,S})$.*

*(2) Let $T$ be a fixed element of $\mathcal S(\mathbf A_{F,S})'_\beta$. Let $T$ be an $S$-local eigendistribution of weight $c\in\Omega(J_{F,S})$. There exists a unique $T_0\in\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta$, such that the adjoint action $\rho'_{F,S}$ of $J_{F,S}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta$ satisfies:*

$$
\rho'_{F,S}(g,T_0)=c(g)T_0 \tag{5.5.1.7}
$$

*for all $g\in\mathrm{GL}_1(\mathbf A_{F,S})$, and such that:*

$$
\langle T_0,\Phi_{F,S}(f)\rangle_{\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))}=\langle T,f\rangle_{\mathcal S(\mathbf A_{F,S})'_\beta,\mathcal S(\mathbf A_{F,S})}. \tag{5.5.1.8}
$$

*Moreover, upon denoting by $\Delta_{F,S}(c)$ resulting unique element of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta(c)$ such that $\Phi'_{F,S}(\Delta_{F,S}(c))=\Delta'(c)$, we have:*

$$
\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta(c)=\mathbf C\cdot\Delta_{F,S}(c) \tag{5.5.1.9}
$$

*and formation of $\Delta_{F,S}(c)$ is holomorphic as a function of $c\in\Omega(J_{F,S})$.*

Proof. (1) : One-dimensionality of $\mathcal S(\mathbf A_{F,S})'_\beta(c)$ for every $c\in\Omega(J_{F,S})$ follows from Theorem 3.4.3.3, which also provides the canonical generators $\Delta'(c)$ and $\Delta_{F,S}(c)$.

Since, for every $f\in\mathcal S(\mathbf A_{F,S})$, $\langle\Delta'(c),f\rangle_{\mathcal S(\mathbf A_{F,S})'_\beta,\mathcal S(\mathbf A_{F,S})}$ is a holomorphic function of $c\in\Omega(J_{F,S})$ by Theorem 3.4.3.3, then by Theorem C.5.2.6 and Theorem C.5.2.4 formation of $\Delta'$ is holomorphic over $\Omega(J_{F,S})$.

(2) : The adjoint operator $\Phi'_{F,S}$ of $\Phi_{F,S}:\mathcal S(\mathbf A_{F,S})\to\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ is continuous by [NB, Thm.8.11.3] and injective by [NB, Thm.8.13.2]. Every element of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta$ is therefore in a unique manner an $\mathcal O^\times_{F,S}$-invariant tempered distribution on $\mathcal S(\mathbf A_{F,S})$.

Let $T$ be an $S$-local eigendistribution of weight $c\in\Omega(J_{F,S})$. Then $T=A\cdot\Delta'(c)$, with $\Delta'$ defined in (5.5.1.5). Since, by (1), $\Delta':\Omega(J_{F,S})\to\mathcal S(\mathbf A_{F,S})'_\beta$ is a holomorphic function, its value at $c$ is controlled by its values over non-empty open subsets of $\Omega(J_{F,S})$ by the Identity Theorem.

We then have, for every $f\in\ker(\Phi_{F,S})$:

$$
L_S(c')\langle\Delta'(c'),f\rangle_{\mathcal S(\mathbf A_{F,S})'_\beta,\mathcal S(\mathbf A_{F,S})}=0 \tag{5.5.1.10}
$$

for $L_S(c')$ the $S$-local Hecke $L$-function, and for $c'$ away from the polar set $\mathcal U_S\subset\Omega(J_{F,S})$ of the meromorphic function $\rho_S(c')$ (see (3.3.1.3)) serving as correcting factor in the $S$-local functional equation (see (3.3.1.2)),

## PDF page 279

**5.5. STRUCTURE THEOREM III: STRONG DUALS AND EIGENDISTRIBUTIONS** · **279**

because $L_S(c')\Delta'(c')=Z_S(f,c')$ by (3.4.3.13), and Lemma 5.1.2.2 applies. Since, over $\Omega(J_{F,S})-\mathcal U_S$, $L_S(c')$ is holomorphic, and as such its set of zeros is discrete, we deduce that we have:

$$
\langle\Delta'(c'),f\rangle_{\mathcal S(\mathbf A_{F,S})'_\beta,\mathcal S(\mathbf A_{F,S})}=0 \tag{5.5.1.11}
$$

as holomorphic scalar valued functions on the entire $\Omega(J_{F,S})$, and hence

$$
\langle\Delta'(c),f\rangle_{\mathcal S(\mathbf A_{F,S})'_\beta,\mathcal S(\mathbf A_{F,S})}=0. \tag{5.5.1.12}
$$

This means that $\Delta'(c)$ factors through the quotient of $\mathcal S(\mathbf A_{F,S})$ by $\ker(\Phi_{F,S})$, i.e. $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$. Being the topology on the latter space the quotient topology inherited from $\mathcal S(\mathbf A_{F,S})$ under $\Phi_{F,S}$, we deduce that $\Delta'(c)$ is in the image of $\Phi'_{F,S}$, and hence so is $T$.

The continuous operator $\Phi'_{F,S}$ restricts to a linear bijection:

$$
\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta(c)\to\mathcal S(\mathbf A_{F,S})'_\beta(c) \tag{5.5.1.13}
$$

for every $c\in\Omega(J_{F,S})$. To see this, we observe that $\Phi'_{F,S}$ is a linear topological embedding: indeed, by [NB, Thm.8.13.2] it is injective and weakly relatively open, and by [NB, Thm.8.12.4(b)] applied to the quotient map $\Phi_{F,S}$, the assumptions of [NB, Thm.8.13.4] are satisfied, and $\Phi'_{F,S}$ is a linear topological embedding. By the foregoing its range contains the linear subspace of $\mathcal S(\mathbf A_{F,S})'_\beta$ linearly generated by the $S$-local eigendistributions.

By Theorem 3.4.3.3, the target in (5.5.1.13) is 1-dimensional and contained in the range of $\Phi'_{F,S}$, and hence the continuous injective linear operator from (5.5.1.13) is a linear topological isomorphism, which proves (5.5.1.9).

By the foregoing, $c\mapsto\Delta'(c)$, a holomorphic function $\Omega(J_{F,S})\to\mathcal S(\mathbf A_{F,S})'_\beta$, factors through $\Phi'_{F,S}$. By Lemma C.4.3.8 and injectivity of $\Phi'_{F,S}$ (which is a consequence of [NB, Thm.8.13.1]), we deduce from Theorem C.5.2.6 and Theorem C.5.2.4 that formation of $\Delta_{F,S}$ is holomorphic over $\Omega(J_{F,S})$. $\square$

The same argument for Theorem 5.5.1.2, establishes the following global analog:

Theorem 5.5.1.3. *Let $F$ be a number field.*

*(1) For $\Delta'(c)$ the eigendistribution of weight $c$ defined as:*

$$
\Delta'(c):=\bigotimes_{v\in\Sigma_F}\Delta'_v(c) \tag{5.5.1.14}
$$

*for $\Delta'_v$ the local eigendistribution constructed in [Weil-a, §1], we have:*

$$
\mathcal S(\mathbf A_F)'_\beta(c)=\mathbf C\cdot\Delta'(c), \tag{5.5.1.15}
$$

*Moreover, formation of $\Delta'(c)$ is holomorphic as a function of $c\in\Omega(C_F)$.*

*(2) Let $T$ be a fixed element of $\mathcal S(\mathbf A_F)'_\beta$. Assume $T$ is a global eigendistribution of weight $c\in\Omega(C_F)$. There exists a unique $T_0\in\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta$, such that the adjoint action $\rho'_F$ of $C_F$ on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta$ satisfies:*

$$
\rho'_F(g,T_0)=c(g)T_0 \tag{5.5.1.16}
$$

*for all $g\in\mathrm{GL}_1(\mathbf A_F)$, and such that:*

$$
\langle T_0,\Phi_F(f)\rangle_{\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta,\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))}=\langle T,f\rangle_{\mathcal S(\mathbf A_F)'_\beta,\mathcal S(\mathbf A_F)}. \tag{5.5.1.17}
$$

*Moreover, upon denoting $\Delta_F(c)$ the resulting unique element of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta(c)$ such that $\Phi'_F(\Delta_F(c))=\Delta'(c)$, we have:*

$$
\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta(c)=\mathbf C\cdot\Delta_F(c) \tag{5.5.1.18}
$$

*and formation of $\Delta_F(c)$ is holomorphic as a function of $c\in\Omega(C_F)$.*

## PDF page 280

**280** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

Proof. By [NB, Thm.8.13.2], $\Phi'_F$ is injective and weakly relatively open, and by [NB, Thm.8.12.4(b)] applied to the quotient map $\Phi_F$, the assumptions of [NB, Thm.8.13.4] are satisfied, and $\Phi'_F$ is a linear topological embedding. The same argument shows that $\Phi'_{F,\omega}$ is a linear topological embedding, for every $\omega\in\widehat{C^1_F}$.

Since, by Theorem 5.2.1.1 and Theorem 2.1.4.1, respectively, Lemma C.1.6.1 applies to both $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta$ and $\mathcal S(\mathbf A_F)'_\beta$, as these are strict countable locally convex inductive limits (directed, up to choosing a co-final sequence of finite subsets of $\Sigma_F$ containing all the Archimedean places of $F$) of the $S$-local spaces $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $\mathcal S(\mathbf A_{F,S})$, all reflexive, being Montel, both (1) and (2) reduce to Theorem 5.5.1.2. $\square$

Remark 5.5.1.4. We note that Theorem 5.5.1.2(1) partially informs us about the structure of the linear image of $\Phi'_{F,S}$ within $\mathcal S(\mathbf A_{F,S})'_\beta$. It contains the $S$-local eigendistributions, and hence the linear subspace they topologically (being $\Phi'_{F,S}$ a linear topological embedding) generate. In fact, a converse is also true: it turns out that the $S$-local eigendistributions are linear topological generators of the range of $\Phi'_{F,S}$, and hence of the strong dual of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta$. This is the content of the Third Structure Theorem (see Theorem 5.5.3.2) and it rests on the Second Structure Theorem, describing the topology on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ (see Theorem 5.4.1.1), and on the Spectral Theorem for unbounded densely defined normal operators on Hilbert spaces (see [Cnw-a, Thm.4.11]). Similar considerations hold for Theorem 5.5.1.3(1), which says that the range of $\Phi'_F$ within $\mathcal S(\mathbf A_F)'_\beta$ contains the global eigendistributions, and hence the linear subspace they topologically (being $\Phi'_F$ a linear topological embedding) generate.

**5.5.2. An example: global eigendistributions of weight $c=1,|\cdot|_F$.** We illustrate Theorems on an example.

Recall from (2.2.4.23) that we have defined:

$$
\mathcal S_0(\mathbf A_F):=\ker(\delta_0)\cap\ker(\widehat\delta_0) \tag{5.5.2.1}
$$

where $\delta_0:\mathcal S(\mathbf A_F)\to\mathbf C$ is the strongly continuous functional $\delta_0(f):=f(0)$, and $\widehat\delta_0$ is its adelic Fourier transform, i.e. $\widehat\delta_0(f):=\widehat f(0)$.

We endow $\mathcal S_0(\mathbf A_F)$ with the subspace topology, promoting it to a closed subspace of $\mathcal S(\mathbf A_F)$, being $\delta_0$ and $\widehat\delta_0$ continuous functionals on $\mathcal S(\mathbf A_F)$.

Lemma 5.5.2.1. *Let $F$ be a number field. The continuous functionals $\delta_0,\widehat\delta_0\in\mathcal S(\mathbf A_F)'_\beta$ descend uniquely to continuous functionals on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$. They are homogeneous with respect to the adjoint of the continuous left-translation action of $C_F$ on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ and satisfy:*

$$
\rho'_F(g,\delta_0)=\delta_0,\quad\rho'_F(g,\widehat\delta_0)=|g|_F\widehat\delta_0 \tag{5.5.2.2}
$$

*for all $g\in C_F$, i.e. $\delta_0$ is a global eigendistribution of weight $c=1$, and $\widehat\delta_0$ is a global eigendistribution of weight $c=|\cdot|_F$. Moreover, for every $\omega\in\widehat{C^1_F}$, both $\delta$ and $\widehat\delta_0$ vanish on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ if and only if $\omega\neq 1$.*

In the notation of Theorem 5.5.1.3, we have

$$
\delta_0=\Delta_F(1),\quad\widehat\delta_0=\Delta_F(|\cdot|_F). \tag{5.5.2.3}
$$

Proof. The value of the functionals $\delta_0,\widehat\delta_0$ on $f\in\mathcal S(\mathbf A_F)$ depend, respectively, only on $\Phi_F(f)$. Indeed, $\delta_0(f)$ is the residue of $Z(f,c)$ at $c=1$ up to a nonzero constant. Similarly, $\widehat\delta_0(f)=\widehat f(0)$ is the residue of $Z(f,c)$ at $c=|\cdot|_F$, up to a nonzero constant (see Theorem 3.2.2.1). Assume $f_1,f_2\in\mathcal S(\mathbf A_F)$ are such that $\Phi_F(f_1)=\Phi_F(f_2)$. Then by Lemma 5.1.2.1 we have $Z(f_1,c)=Z(f_2,c)$ as meromorphic functions on $\Omega(C_F)$, and their poles and residues are also equal.

Both functionals $\delta_0$ and $\widehat\delta_0$ induce unique linear functionals on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, continuous with respect to the quotient topology. Such residues vanish over all the connected components of $\Omega(C_F)$ parametrized by non-trivial continuous characters of $C^1_F$. $\square$

## PDF page 281

**5.5. STRUCTURE THEOREM III: STRONG DUALS AND EIGENDISTRIBUTIONS** · **281**

Remark 5.5.2.2. We observe that while $\delta_0$ and $\widehat\delta_0$ induce continuous functionals on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, which, throughout this remark, we shall denote the same way, this is not saying that $\delta_0(\Phi_F(f))=\sum_{\xi\in F^\times}\delta_0(f(\xi^{-1}x))$: indeed, this series diverges.

The value of $\delta_0$ at $\Phi_F(f)$, for some $f\in\mathcal S(\mathbf A_F)$, is $f(0)$: Lemma 5.5.2.1 informs us that this is well-defined modulo $\ker(\Phi_F)$, i.e. modulo $\ker(Z)$ (see Lemma 5.1.2.1). The same holds for $\widehat\delta_0$.

This can also be seen directly from Theorem 2.2.3.4(2): let $f\in\mathcal S(\mathbf A_F)$ be such that $\Phi_F(f)=0$. Then by (2.2.3.5) from Theorem 2.2.3.4(2), we have, for every integer $N\geq 0$, that there exists a real number $C_N>0$ such that:

$$
|-|g|^{-1}_F\widehat f(0)+f(0)|\leq C_N|g|^N_F
$$

for all $g\in C_F$ as $|g|_F\to 0^+$. This forces $\widehat f(0)=0$, and hence also $f(0)=0$. Therefore, if $f\in\mathcal S(\mathbf A_F)$ is arbitrary and $f_0\in\ker(\Phi_F)$, $\delta_0$ and $\widehat\delta_0$ satisfy $\delta_0(f)=\delta_0(f+f_0)$ and $\widehat\delta_0(f)=\widehat\delta_0(f+f_0)$.

**5.5.3. Third Structure Theorem.** The Third Structure Theorem (Theorem 5.5.3.2) places Weil’s eigendistributions into their natural place to work organically, obtaining a precise result on the structure of the locally convex spaces of co-invariants of $\mathcal S(\mathbf A_F)$ and $\mathcal S(\mathbf A_{F,S})$ under the action of $\mathrm{GL}_1(\mathbf A_F)$ and its subgroups, respectively $\mathrm{GL}_1(\mathbf A_{F,S})$ and its subgroups.

The following Proposition provides a local converse to Theorem 5.5.1.2(1) (i.e. local at a single place $v$ of the number field $F$), and builds towards Theorem 5.5.3.2.

Proposition 5.5.3.1. *Let $F$ be a number field, $v$ a place of $F$, $\omega\in\Omega(F^\times_v)$ a unitary character. Then $\mathcal S(F_v)'_\beta$ is linearly and topologically generated by the functionals $\{\Delta'_v(c),c\in\Omega(F^\times_v)\}$, and the closed subspace of $\mathcal S(F_v)'_\beta$ of the $\omega$-homogeneous tempered distributions is linearly and topologically generated by the functionals $\{\Delta'_v(c),c\in\Omega(F^\times_v)(\omega)\}$.*

Proof. We show that $\{\Delta'_v(c),c\in\Omega(F^\times_v)\}$ separates the points of $\mathcal S(F_v)$. Indeed, let $f\in\mathcal S(F_v)$ and assume $\Delta'_v(c)(f)$ for every $c\in\Omega(F^\times_v)$. Then $Z_v(f,c)=\Delta'_v(c)(f)L_v(c)=0$ as a meromorphic function over $\Omega(F^\times_v)$. In particular, $f$ vanishes identically over $F^\times_v$, and hence over $F_v$ by continuity. We now call $E$ the linear subspace of $\mathcal S(F_v)'_\beta$ generated by $\{\Delta'_v(c),c\in\Omega(F^\times_v)\}$. Since $\{\Delta'_v(c),c\in\Omega(F^\times_v)\}$ separates the points of $\mathcal S(F_v)$, then by [NB, Thm.7.7.3] $E$ is dense with respect to the $\sigma(\mathcal S(F_v)'_\beta,\mathcal S(F_v))$-topology on $\mathcal S(F_v)'$, which is the strong topology by [NB, Thm.11.3.6] since $\mathcal S(F_v)'_\beta$ is barrelled, as $\mathcal S(F_v)$ is Montel, and hence $\sigma(\mathcal S(F_v)'_\beta,\mathcal S(F_v))=\sigma(\mathcal S(F_v)'_\beta,(\mathcal S(F_v)'_\beta)')$ since $\mathcal S(F_v)$ is reflexive (recall that the bi-dual of a Hausdorff locally convex space is defined to be the dual of the strong dual; see [Jar, Part II,Ch.11,§11.2]).

Assume now that $v$ is non-Archimedean.

Since the closed subspace of $\omega$-homogeneous tempered distributions on $\mathcal S(F_v)$ is closed in $\mathcal S(F_v)'_\beta$, which is complemented. Indeed, integration over the compact Hausdorff abelian group $\mathcal O^\times_{F_v}$ with respect to the local multiplicative Tamagawa measure produces a linear form, for each $f\in\mathcal S(F_v)$:

$$
P_v(f)(\varphi):=\int_{\mathcal O^\times_{F_v}}\langle\rho_v(g,f),\varphi\rangle_{\mathcal S(F_v),\mathcal S(F_v)'_\beta}\overline{\omega}(g)\,\mathrm{d}\mu_v(g)
$$

for $\varphi\in\mathcal S(F_v)'$, and for each $f$, $P_v(f)$ is valued in $(\mathcal S(F_v)')^*$. Since $\mathcal S(F_v)$ is complete, hence quasi-complete, then by Theorem C.4.3.5 we see that $P_v(f)$ is contained in $\mathcal S(F_v)$, and since its formation is linear, it is a linear operator $P_v:\mathcal S(F_v)\to\mathcal S(F_v)$.

By Lemma C.4.3.12, $P_v$ is continuous. Its range is the closed subspace of $\omega$-homogeneous elements of $\mathcal S(F_v)$, and hence $\ker(P_v)^\perp$, which already contains all $\omega$-homogeneous tempered distributions in $\mathcal S(F_v)'_\beta$, coincides with their closed subspace in $\mathcal S(F_v)'_\beta$. $\square$

For $F$ a number field and $S$ a finite set of places of $F$ containing all the Archimedean places, the $S$-local and global analogs of Proposition 5.5.3.1 rest upon the description of the topology of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ provided by the Second Structure Theorem (see Theorem 5.4.1.1), on the First Structure Theorem (see Theorem

## PDF page 282

**282** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

5.2.1.1) to reduce the global assertion to the $S$-local case, and on the Spectral Theorem for unbounded densely defined normal operators on Hilbert spaces.

Theorem 5.5.3.2 (S-local Third Structure Theorem). *Let $F$ be a number field, $S$ a finite set of places containing all Archimedean places.*

*(1) For any $\omega\in\widehat{J^1_{F,S}}$, the continuous linear operator $\Phi'_{F,S,\omega}$ is injective and maps $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))'_\beta$ into $\mathcal S(\mathbf A_{F,S})'_\beta$ within the closed subspace of $\mathcal S(\mathbf A_{F,S})'_\beta$ of the $\omega$-homogeneous tempered distributions. The strong closure of its range is linearly and topologically generated by the image under $\Phi'_{F,S,\omega}$ of the functionals $\{\Delta_{F,S}(c),c\in\Omega(J_{F,S})(\omega)\}$.*

*(2) The continuous linear operator $\Phi'_{F,S}$ is injective and maps $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\beta$ into $\mathcal S(\mathbf A_{F,S})'_\beta$ within the closed subspace of $\mathcal S(\mathbf A_{F,S})'_\beta$ of the $\mathcal O^\times_{F,S}$-invariant tempered distributions, and the strong closure of its range is linearly and topologically generated by the image under $\Phi'_{F,S}$ of the functionals $\{\Delta_{F,S}(c),c\in\Omega(J_{F,S})\}$.*

Proof. We start by recalling the following general argument: let $A:X\to Y$ be a continuous linear operator between Hausdorff locally convex topological $\mathbf C$-vector spaces. Assume $Y=\prod_{i\in I}H_i$ is a locally convex product of Hilbert spaces, and $A$ is a linear topological embedding. Then the canonical linear bijection $P:\bigoplus_{i\in I}H'_i\to Y'$ provided by [Jar, Part II,Ch.8,§8.8,Prop.1] is continuous with respect to the locally convex direct sum topology on the source, and the strong topology on the target, and the composition

$$
A'\circ P:\bigoplus_{i\in I}H'_i\to Y'\xrightarrow{A'}X' \tag{5.5.3.1}
$$

is continuous, linear and surjective. To see this, we proceed as follows. From [Jar, Part II,Ch.8,§8.8,Prop.1], we know that $P$ is a continuous linear bijection with respect to the stated topologies on source and target. It is therefore enough to show that $A':Y'\to X'$ is continuous and surjective. Since $A$ is injective and relatively open, being a linear topological embedding, this follows from [NB, Thm.8.13.1(c)].

(1) : We now call $X:=\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$, for an arbitrary choice $\omega\in\widehat{J^1_{F,S}}$. The Second Structure Theorem (Theorem 5.4.1.1) applied with $p=2$, provides us with a linear topological embedding:

$$
U_S:\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))\to\prod_{m\geq 0}\prod_{N\geq 0}(L^2(\mathbf R,\mathrm{d}x)\times L^2(\mathbf R,\mathrm{d}x))
$$

defined as, upon choosing $\chi\in\widehat{J_{F,S}}$ such that $\chi|_{J^1_{F,S}}=\omega$:

$$
U_S(f):=(s^NZ_S(f,\chi|\cdot|^s_{F,S}),s^NZ_S(\widehat f,\chi|\cdot|^s_{F,S}))_{s\in\mathbf C_{>0},\mathrm{Re}(s)=a_m}
$$

for $\{a_m\}_{m\geq 0}\subset\mathbf Q_{>0}$ a sequence of positive rational numbers such that $0$ is an accumulation point, and $\limsup_{m\geq 0}a_m=+\infty$.

The linear topological embedding $U_S$ induces a family $\mathcal P$ of seminorms on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$ that generate the Hausdorff locally convex topology on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$. We define, for each $\phi\in\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$:

$$
p_{m,N}(\phi):=\|(a_m+ix)^NM(\phi)(a_m+ix)\|_{L^2(\mathbf R,\mathrm{d}x)},\quad\widehat p_{m,N}(\phi):=\|(a_m+ix)^NM(\mathcal F_S(\phi))(a_m+ix)\|_{L^2(\mathbf R,\mathrm{d}x)},\ m,N\geq 0
$$

where $M(\phi)(s):=\int_{\mathbf R_{>0}}\phi(s)t^s\frac{\mathrm{d}t}{t}$ is the Mellin transform.

By Theorem 5.2.1.1(2), the family $\mathcal P=\{p_{m,N},\widehat p_{m,N},m,N\in\mathbf N\}$ is a separating countable family of seminorms on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$ generating the Hausdorff locally convex topology on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$.

The completion of $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$ with respect to any $p\in\mathcal P$ is a Hilbert space, which we denote $H_p$.

The linear map:

$$
A:\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))\to\prod_{p\in\mathcal P}H_p \tag{5.5.3.2}
$$

obtained from the completion operators $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))\to H_p$, is a linear topological embedding, since $\mathcal P$ generates the Hausdorff locally convex topology on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$.

## PDF page 283

**5.5. STRUCTURE THEOREM III: STRONG DUALS AND EIGENDISTRIBUTIONS** · **283**

In particular, the canonical linear operator

$$
A'\circ P:\bigoplus_{p\in\mathcal P}H'_p\to(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})))' \tag{5.5.3.3}
$$

from the foregoing (where $P$ is the linear bijection $P:\bigoplus_{p\in\mathcal P}H'_p\to(\prod_{p\in\mathcal P}H_p)'$ provided by [Jar, Part II,Ch.8,§8.8,Cor.1]) is a surjective linear operator from the direct sum $\bigoplus_{p\in\mathcal P}H'_p$ onto $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))'$.

Upon endowing each $H'_p$ with the strong topology (promoting them to Hilbert spaces, anti-isomorphic to $H_p$ itself by [Cnw-a, Ch.I,§3,Thm.3.4]), their direct sum with the resulting Hausdorff locally convex topology, and $(\prod_{p\in\mathcal P}H_p)'$ with its strong topology, then $P$ is continuous, and $A'\circ P$ is continuous with respect to the locally convex direct sum topology of the $(H_p)'_\beta$ on the source, and the strong topology of $(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})))'_\beta$ on the target.

We choose a continuous homomorphic section $\tau$ to the $S$-idelic norm, and observe that each Hilbert space $H_p$ is equipped with a strongly continuous one-parameter group of operators as follows induced by the $\mathbf R_{>0}$-action on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$ through $\tau$. Indeed, we define:

$$
\Psi:\mathbf R\times H_p\to H_p \tag{5.5.3.4}
$$

by, for $f\in\mathcal S(\mathbf A_{F,S})$ and $p=p_{m,N}$ with $m,N\geq 0$ integers:

$$
\Psi(t',\Phi_{F,S,\omega}(f))(g):=\Phi_{F,S,\omega}(f)(\tau(t')^{-1}g) \tag{5.5.3.5}
$$

the right side being a continuous function of $g\in J_{F,S}$, $\overline{\omega}$-homogeneous under the left-translation action of $J^1_{F,S}$.

To see this, we proceed as follows. We have, for the above choice of $p\in\mathcal P$:

$$
p(\Psi(t',\Phi_{F,S,\omega}(f))(g))=\left\|(a_m+ix)^N\int_{\mathbf R_{>0}}t^{a_m+ix}\left(\int_{J^1_{F,S}}\omega(g_0)\Phi_{F,S}(f)(\tau(t')^{-1}g_0\tau(t))\,\mathrm{d}\overline{\mu}_{S,1}(g_0)\right)\frac{\mathrm{d}t}{t}\right\|_{L^2(\mathbf R,\mathrm{d}x)}
$$

for unique integers $m,N\geq 0$.

We compute:

$$
p(\Psi(t',\Phi_{F,S,\omega}(f))(g))=\|(a_m+ix)^N(t')^{a_m+ix}M(\Phi_{F,S,\omega}(f)(\tau(t))(a_m+ix)\|_{L^2(\mathbf R,\mathrm{d}x)}=(t')^{a_m}p(\Phi_{F,S,\omega}(f)).
$$

We deduce that the new strongly continuous 1-parameter group of operator given by

$$
t\mapsto t^{-a_m}\Psi(t,\cdot)
$$

is unitary.

The infinitesimal generator $\Theta$, which exists and is unbounded and densely defined on $H_p$ by [Cnw-a, Thm.5.6], has real spectrum $\sigma(\Theta)\subset\mathbf R$, and by [Cnw-a, Thm.4.11], there exists a unique spectral measure $E:\mathcal B(\sigma(\mathbf R))\to\mathscr{B}_{\mathrm{SOT}}(H_p)$ valued in orthogonal projectors, such that the action $\rho_{F,S}$ of $J_{F,S}$ on $H_p$ defined as the unique continuous extension of the action of $J_{F,S}$ on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$, can be written as, for each $\phi\in H_p$:

$$
\rho_{F,S}(g,\phi)=t^{a_m}\omega(g_0)\int_{\sigma(\mathbf R)}t^{ix}\,\mathrm{d}E(x)\phi
$$

upon writing $g\in J_{F,S}$ uniquely as $\tau(t)g_0$ for $(t,g_0)\in\mathbf R_{>0}\times J^1_{F,S}$.

From the construction of $E$ from the proof of [Cnw-a, Thm.4.11], we may choose, for every real number $X\geq 0$, increasingly fine partitions $\{\Delta_{k,X}\}_{k\in\mathbf N,X}$ of $[-X,X]\subset\mathbf R$ by Borel sets, and points $x_k\in\Delta_k$, ordering the intervals $[-X,X]$ by inclusion and the partitions by refinement, obtaining a net of continuous linear operators $\sum_{k\in\mathbf N}t^{ix_k}E(\Delta_{k,X})$ on $H_p$ such that

$$
\sum_{k\in\mathbf N}t^{ix_k}E(\Delta_{k,X})\to\int_{\sigma(\mathbf R)}t^{ix}\mathrm{d}E(x) \tag{5.5.3.6}
$$

## PDF page 284

**284** · **CHAPTER 5. SPACES OF ADELIC θ-FUNCTIONS AND IDELIC Z-FUNCTIONS**

as $X\to+\infty$, and the partitions of $[-X,X]$ are increasingly finer, with respect to the strong operator topology on $\mathscr{B}(H_p)$ (the $\mathbf C$-algebra of bounded operators on $H_p$).

The range of $E(\Delta_{k,X})$ splits off as a linear topological direct summand of $H_p$, being $E(\Delta_{k,X})$ an orthogonal projector.

Since the convergence in (5.5.3.6) is with respect to the strong operator topology on $\mathscr{B}(H_p)$, then we deduce that any $\phi\in H_p$, can be approximated to an arbitrary degree of precision in the norm-topology on $H_p$, by a finite linear combination of elements $\phi_k$ of the form $\phi_k=E(\Delta_{X,k})\phi$, on which the continuous action of $J_{F,S}$ has the diagonal form:

$$
\rho_{F,S}(\tau(t)g_0,\phi_k)=t^{a_m+ix_k}\omega(g_0)\phi_k.
$$

Since $(H_p)'_\beta$ is anti-isometric to $H_p$ compatibly with the strongly continuous action $t\mapsto t^{-a_m}\Psi(t,\cdot)$, which the anti-isometry carries over to the dual action, the same conclusion holds for the elements $T$ of $(H_p)'_\beta$: they can be approximated to an arbitrary degree of precision with respect to the norm-topology (which is the strong topology on $H'_p$) by finite $\mathbf C$-linear combinations of norm-continuous functionals $T_k$ on $H_p$ on which the action $\rho'_{F,S}$ of $\mathbf R_{>0}\times J^1_{F,S}$ is of the diagonal form:

$$
\rho'_{F,S}(\tau(t)g_0,T_k)=t^{-a_m-ix_k}\overline{\omega}(g_0)T_k.
$$

Each $T_k$ is in particular continuous as a functional on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$, with respect to the finer topology of $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$, and therefore induces an element of $(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})))'_\beta$ (which is none other than the image of $T_k\in(H_p)'_\beta\subset\bigoplus_{p\in\mathcal P}(H_p)'_\beta$ under the continuous linear operator $A'\circ P$ of (5.5.3.3)).

We have just shown that the functionals of the form $T_k$, on which the (dual) continuous $J_{F,S}$-action is diagonal, of weight $c$ given by the quasi-character corresponding to $(t^{a_m+ix_k},\omega)$ under the bi-holomorphism from (3.1.2.5) induced by the continuous homomorphic section $\tau$ to the $S$-idelic norm, are norm-dense in $(H_p)'_\beta$. They therefore span a dense linear subspace and the direct sum within $\bigoplus_{p\in\mathcal P}(H_p)'_\beta$ is sent onto a dense linear subspace of $(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})))'_\beta$ by the continuous linear surjective operator $A'\circ P$ from (5.5.3.3).

Recall now the purpose of this argument. We want to show that the closed $\mathbf C$-linear subspace of $\mathcal S(\mathbf A_{F,S})'_\beta$ of those tempered distributions $T$ in the closure of the range of $\Phi'_{F,S,\omega}$, is comprised of tempered distributions that are $\overline{\omega}$-homogeneous, i.e. such that $\rho'_{F,S}(g,T)=\overline{\omega}(g)T$ for all $g\in J^1_{F,S}$, and it is linearly and topologically generated by the eigendistributions $\{\Delta_{F,S}(c),c\in\Omega(J_{F,S})(\omega)\}$ from (5.5.1.6) of Theorem 5.5.1.2.

The desired homogeneity condition is a consequence of the design of the operator $\Phi_{F,S,\omega}$, which factors through the projector $P_{F,S,\omega}$ from (5.2.3.9). We have just shown that $c$-homogeneous continuous functionals in $(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})))'_\beta$, as $c$ varies over all $S$-idelic quasi-characters such that $c|_{J^1_{F,S}}=\omega$, linearly topologically generate $(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})))'_\beta$. Their image in $\mathcal S(\mathbf A_{F,S})'_\beta$ is itself a homogeneous tempered distribution with weight given by an $S$-idelic quasi-character in $\Omega(J_{F,S})(\omega)$, which is what we wanted to show.

(2) : We define the linear subspace $H$ of $\mathcal S(\mathbf A_{F,S})'_\beta$ generated by the functionals $\{\Delta_{F,S}(c),c\in\Omega(J_{F,S})\}$.

We compute $H^\perp$ with respect to the duality $\langle(\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))\rangle$.

Let $\phi\in\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$ be viewed as an element of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ under the linear topological identification of $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$ with $\mathrm H^0(\omega,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))$, the closed subspace of $\omega$-homogeneous elements in $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$.

The condition

$$
\langle T,\phi\rangle_{(\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))}=0
$$

is valid, in particular, for $T$ in the subspace of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta$ generated by the functionals $\{\Delta_{F,S}(c),c\in\Omega(J_{F,S})(\omega)\}$. By (1), this is the closure of the range under $\Phi'_{F,S,\omega}$ of $(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})))'_\beta$. Which forces $\phi=0$.

Since the algebraic direct sum $\bigoplus_{\omega\in\widehat{J^1_{F,S}}}\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$ is dense in $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$, we deduce that we have $H^\perp=0$, and hence $H$ is weakly dense in $(\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta$ by [NB, Thm.8.9.2(e)], noting

## PDF page 285

**5.5. STRUCTURE THEOREM III: STRONG DUALS AND EIGENDISTRIBUTIONS** · **285**

that $\sigma((\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))=\sigma((\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta,((\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta)')$ since $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ is reflexive by Theorem 5.2.1.1(1), being Montel. The weak closure of $H$ in $(\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta$ agrees with its strong closure by the Hahn-Banach Theorem, and so $H$ is dense in $(\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))'_\beta$ (see also [Jar, Part II,Ch.11,§11.5,Prop.1,p.230]). $\square$

Remark 5.5.3.3. An alternative argument for Theorem 5.5.3.2 uses the Mellin transform $L_S$. Indeed, the eigendistributions $\{\Delta_{F,S}(c)\}$ are multiples of point-evaluation functionals on the meromorphic functions on $\Omega(J_{F,S})$ given by the linear image in $\mathscr M(\Omega(J_{F,S}))$ under $L_S$ from (5.1.1.2).

The joint kernel of the $\Delta_{F,S}(c)$ for $c$ varying over $\Omega(J_{F,S})$, or simply over a connected subset containing an interval with non-empty 1-dimensional interior, is therefore trivial in $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ by the Identity Theorem.

It follows that the continuous functionals $\{\Delta_{F,S}(c)\}$ separate the points of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$, and they linearly generate a weakly dense subspace of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))'_\sigma$ by [NB, Thm.8.9.2(e)].

By [Jar, Part II,Ch.11,§11.5,Prop.1,p.230], since $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ is Montel by Theorem 5.2.1.1(1), such subspace is also strongly dense.

Theorem 5.5.3.2 enables us to establish the following global analog:

Theorem 5.5.3.4 (Global Third Structure Theorem). *Let $F$ be a number field.*

*(1) For any $\omega\in\widehat{C^1_F}$, the continuous linear operator $\Phi'_{F,\omega}$ is a linear topological embedding of $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))'_\beta$ into $\mathcal S(\mathbf A_F)'_\beta$, whose range is contained within the closed subspace of $\mathcal S(\mathbf A_F)'_\beta$ of the $\omega$-homogeneous tempered distributions, and it is linearly and topologically generated by the image under $\Phi'_{F,\omega}$ of the functionals $\{\Delta_F(c),c\in\Omega(C_F)(\omega)\}$.*

*(2) The continuous linear operator $\Phi'_F$ is a linear topological embedding of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta$ into $\mathcal S(\mathbf A_F)'_\beta$, whose range is contained within the closed subspace of $\mathcal S(\mathbf A_F)'_\beta$ of the $F^\times$-invariant tempered distributions, and it is linearly and topologically generated by the image under $\Phi'_F$ of the functionals $\{\Delta_F(c),c\in\Omega(C_F)\}$.*

Proof. (1) follows from (2), because Lemma 4.3.3.1 applies to the continuous adjoint action of $C^1_F$ on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta$, this space being complete by Theorem 5.2.3.1, hence quasi-complete by [Scha, Ch.III,§4,Corollary,p.85], and the action of $C^1_F$ being uniformly continuous as a consequence of Lemma 5.1.3.1.

Since, by Theorem 5.2.1.1 and Theorem 2.1.4.1, respectively, Lemma C.1.6.1 applies to both $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))'_\beta$ and $\mathcal S(\mathbf A_F)'_\beta$, as these are strict countable locally convex inductive limits (directed, up to choosing a co-final sequence of finite subsets of $\Sigma_F$ containing all the Archimedean places of $F$) of the $S$-local spaces $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $\mathcal S(\mathbf A_{F,S})$, all reflexive, being Montel, both (1) and (2) reduce to Theorem 5.5.1.2. $\square$

## PDF page 286
