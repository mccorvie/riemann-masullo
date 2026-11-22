## PDF page 287

**CHAPTER 6** · **Local-Global structures** · **287**

CHAPTER 6

Local-Global structures

6.1. Structure Theorem IV: local within global 287

6.1.1. Description of $\bar\pi_{S,S'}$ and $\bar\pi_S$ 287

6.1.2. Ranges of $\bar\pi_{S,S'}$ and $\bar\pi_S$, and subspaces of invariants 288

6.2. Structure Theorem V: isotypic exhaustiveness 295

6.2.1. Eventual surjectivity of $\bar\pi_{S,S'}$ and $\bar\pi_S$ 295

6.2.2. Computation of the isotypes of $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ 298

6.3. Local and Global Converse Theorems 302

6.3.1. Recollections on the Euler factors of Hecke $L$-functions 302

6.3.2. Converse Theorems 303

**6.1. Structure Theorem IV: local within global**

In this section we establish one more Structure Theorem on $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ and their isotypes, identifying the range of the transition operators $\bar\pi_{S,S'}$ and $\bar\pi_S$, and proving their eventual surjectivity on isotypes for all large enough $S$.

**6.1.1. Description of $\bar\pi_{S,S'}$ and $\bar\pi_S$.** Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

We provide a description of the transition operators $\bar\pi_{S,S'}$ and $\bar\pi_S$ from Theorem 5.2.3.1, which will elucidate their relation to Euler products, with a view towards the later constructions of Chapter 5.

PROPOSITION 6.1.1.1. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$.*

*Upon choosing a $\mathbf Z$-basis $\Xi_{S,S'}:=\{\xi_1,\dots,\xi_{\lvert S'\rvert-\lvert S\rvert}\}$ for $\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times$, and upon denoting by $\theta_\xi:\mathcal S(\mathbf A_{F,S'})\to\mathcal S(\mathbf A_{F,S'})$ the continuous linear operator $f\mapsto\rho_{F,S}(\xi,f)=f(\xi^{-1}\cdot)$, we have, as elements of*

$$
\mathscr L_\beta(\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})),\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'})))
$$

*that the following identity holds:*

$$
\bar\pi_{S,S'}=\prod_{\xi\in\Xi_{S,S'}}(1-\theta_\xi)^{-1}. \tag{6.1.1.1}
$$

*Upon choosing a $\mathbf Z$-basis $\Xi_S:=\{\xi_k,k\ge 1\}$ for $F^\times/\mathcal O_{F,S}^\times$, and upon denoting by $\theta_\xi:\mathcal S(\mathbf A_F)\to\mathcal S(\mathbf A_F)$ the continuous linear operator $f\mapsto\rho_F(\xi,f)=f(\xi^{-1}\cdot)$, we have, as elements of*

$$
\mathscr L_\beta(\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})),\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)))
$$

*that the following identity holds:*

$$
\bar\pi_S=\prod_{\xi\in\Xi_S}(1-\theta_\xi)^{-1} \tag{6.1.1.2}
$$

*the convergence of the product being uniform on the bounded subsets of $\mathcal S(\mathbf A_{F,S})$.*

**287**

## PDF page 288

**288** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

PROOF. This is a consequence of the fact that every element $\xi$ in $\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times$ acts non-trivially by left multiplication only through the submonoid $\mathcal O_{F,S'}\cap\xi^{\mathbf Z}$, since for any $f\in\mathcal S(\mathbf A_{F,S})$, we have $\pi_{S,S'}(f)=f\otimes 1_K$ with $K=\prod_{v\in S'-S}1_{\mathcal O_{F_v}}$ with $K=\prod_{v\in S'-S}\mathcal O_{F_v}\subset\widehat{\prod}_{v\in S'-S}(F_v,\mathcal O_{F_v})$. Injectivity of $\bar\pi_{S,S'}$ (see Theorem 5.2.3.1(1)) implies that $\bar\pi_{S,S'}=\sum_{m\ge 0}\theta_\xi^m$ and $(1-\theta_\xi)^{-1}$ are the same element in

$$
\mathscr L_\beta(\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S})),\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))).
$$

Similarly, every $\xi\in F^\times/\mathcal O_{F,S}^\times$ is such that acts on $\pi_S(\mathcal S(\mathbf A_{F,S}))$ by left multiplication through the submonoid $\mathcal O_F\cap\xi^{\mathbf Z}$. The convergence assertion is a consequence of Lemma 2.2.2.1. $\square$

**6.1.2. Ranges of $\bar\pi_{S,S'}$ and $\bar\pi_S$, and subspaces of invariants.** We recall that for $S,S'$ finite sets of places of the number field $F$ containing all Archimedean places, and such that $S\subset S'$, the Hausdorff locally compact abelian group $J_{F,S}=\mathrm{GL}_1(\mathbf A_{F,S})/\mathcal O_{F,S}^\times$ from (3.1.2.1) acts continuously on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$ by left translation, as does $J_{F,S'}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$, and the compact Hausdorff abelian group $\prod_{v\in S'-S}\mathcal O_{F_v}^\times$ acts on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$ through the insertion homomorphism:

$$
\widehat{\mathcal O}_{F,S'-S}^\times:=\prod_{v\in S'-S}\mathcal O_{F_v}^\times\to\{1\}\times\prod_{v\in S'-S}F_v^\times\subset\mathrm{GL}_1(\mathbf A_{F,S}) \tag{6.1.2.1}
$$

followed by the quotient homomorphism $\mathrm{GL}_1(\mathbf A_{F,S})\to J_{F,S}$.

We extend the notation $\widehat{\mathcal O}_{F,S'-S}^\times$ to the case $S'$ is not finite, but coincides with the set $\Sigma_F$ of all places of $F$.

We denote by $\widehat{\mathcal O}_{F,\Sigma_F-S}^\times$ the compact Hausdorff abelian group:

$$
\widehat{\mathcal O}_{F,\Sigma_F-S}^\times:=\prod_{v\notin S}\mathcal O_{F_v}^\times\to\{1\}\times\prod_{v\notin S}F_v^\times\subset\mathrm{GL}_1(\mathbf A_F). \tag{6.1.2.2}
$$

THEOREM 6.1.2.1 (Fourth Structure Theorem). *Let $F$ be a number field, $S,S'$ finite sets of places of $F$ containing all Archimedean places such that $S\subset S'$. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$.*

*(1) The range of the linear topological embedding $\bar\pi_{S,S'}$ from (5.2.1.1) is the closed subspace of elements of $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$ invariant under the action of the closed subgroup $\widehat{\mathcal O}_{F,S'-S}^\times$ of $\mathrm{GL}_1(\mathbf A_{F,S'})$.*

*(2) The range of the linear topological embedding $\bar\pi_S$ induced by the linear topological isomorphism $\bar\pi$ from (5.2.1.2) is the closed subspace of elements of $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ invariant under the action of the closed subgroup $\widehat{\mathcal O}_{F,\Sigma_F-S}^\times$ of $\mathrm{GL}_1(\mathbf A_F)$.*

We need the following:

LEMMA 6.1.2.2. *Let $F$ be a number field.*

*(1) Let $v$ be a finite place of $F$. The $\mathbf C$-linear space:*

$$
\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v)) \tag{6.1.2.3}
$$

*is a free $\mathbf C[z^{\pm 1}]$-module of rank 1.*

*(1) Upon defining the action of $z\in\mathbf C[z^{\pm 1}]$ by left-translation on functions by $\pi_v^{\mathbf Z}$, for $\pi_v$ any choice of uniformizer at $v$, then a $\mathbf C[z^{\pm 1}]$-module free generator is the function $1_{\mathcal O_{F_v}}$.*

*(2) Upon endowing the subspace $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))\subset\mathcal S(F_v)$ with the subspace topology, it is a closed subspace, and the $\mathbf C$-linear isomorphism with $\mathbf C[z^{\pm 1}]$ is a linear topological isomorphism upon endowing $\mathbf C[z^{\pm 1}]$ with the final locally convex topology.*

*(2) Let $S,S'$ be finite sets of places containing all Archimedean places, and such that $S\subset S'$. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$. The $\mathbf C$-linear space:*

$$
\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'})) \tag{6.1.2.4}
$$

*satisfies the following properties:*

## PDF page 289

**6.1. STRUCTURE THEOREM IV: LOCAL WITHIN GLOBAL** · **289**

*(1) Upon endowing the $\mathbf C$-linear space $\mathbf C[z_v^{\pm 1},v\in S'-S]$ with the final locally convex topology, then the linear topological isomorphism $\mathbf C[z^{\pm 1}]\to\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$ for every finite place $v\in S'$ induces a linear topological isomorphism:*

$$
\mathcal S(\mathbf A_{F,S})\otimes_\pi\mathbf C[z_v^{\pm 1},v\in S'-S]\to\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'})). \tag{6.1.2.5}
$$

*(2) The map from (6.1.2.5) is uniquely determined by the assignment explicitly obtained by sending, for any $f_S\in\mathcal S(\mathbf A_{F,S})$, the element $f_S\otimes(\prod_{v\in S'-S}z_v^{a_v})$, for $(a_v)_{v\in S'-S}\in\mathbf Z^{\lvert S'\rvert-\lvert S\rvert}$, to the Schwartz-Bruhat function:*

$$
f_S\otimes\prod_{v\in S'-S}1_{\pi_v^{a_v}\mathcal O_{F_v}}. \tag{6.1.2.6}
$$

REMARK 6.1.2.3. For the sake of clarity, we recall that by “left-translation action” of a Hausdorff locally compact abelian group $G$ on a function space $\mathscr F(X)$ on a Hausdorff topological space $X$ on which $G$ acts continuously, we mean the assignment $\rho_G:G\times\mathscr F(X)\to\mathscr F(X)$ defined by $\rho_G(g,f)(x):=f(g^{-1}x)$ as functions of $x\in X$. $\rho_G$ preserves continuity of functions.

In particular, for $f\in\mathcal S(F_v)$ as in Lemma 6.1.2.2(1), $z.f$ is the function of $x\in F_v$ given by $f(\pi_v^{-1}x)$.

PROOF. (1) : We define $u_m:=1_{\pi_v^m\mathcal O_{F_v}}$ for $m\in\mathbf Z$. The set $\{u_m\}_{m\in\mathbf Z}\subset\mathcal S(F_v)$ is $\mathbf C$-linearly independent. Indeed, let $\{c_m\}_{-N\le m\le N}\subset\mathbf C$ be such that $u:=\sum_{-N\le m\le N}c_mu_m=0$ in $\mathcal S(F_v)$.

Since $\pi_v^m\mathcal O_{F_v}\subset\pi_v^{m-1}\mathcal O_{F_v}$ for every $m\in\mathbf Z$, we let $x\in\pi_v^m\mathcal O_{F_v}-\pi_v^{m+1}\mathcal O_{F_v}$. Then $u(x)=c_m$, which forces $c_m=0$ for every $-N\le m\le N$.

We now let $f\in\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$. The function $f$ is locally constant and compactly supported over $F_v$. There exists a large enough integer $N\ge 0$ such that $f$ is $\pi_v^N\mathcal O_{F_v}$-invariant.

By compactness of the support of $f$, there exists an integer $N'$ such that $f$ vanishes over $F_v-\pi_v^{N'}\mathcal O_{F_v}$, and since $\pi_v^k\mathcal O_{F_v}\subset\pi_v^{N'}\mathcal O_{F_v}$ for every $k\ge N'$, the set of integers $k\in\mathbf Z$ such that $f$ is nonzero over $\pi_v^k\mathcal O_{F_v}$ is bounded below. There therefore exists a minimal such $k\ge N'$, and we rename it as $N'$.

Let $c_{N'}$ be the value of $f$ over the collar $\pi_v^{N'}\mathcal O_{F_v}-\pi_v^{N'+1}\mathcal O_{F_v}$. Then $f-c_mu_m$ vanishes over $\pi_v^{N'}\mathcal O_{F_v}-\pi_v^{N'+1}\mathcal O_{F_v}$, and hence its support, again compact, is contained in $\pi_v^{N'+1}\mathcal O_{F_v}$.

Upon iterating finitely many times, we obtain a subset $\{c_m,m\in\mathbf Z\}\subset\mathbf C$ such that $c_m$ is nonzero for at most finitely many integers $m$, and such that $f-\sum_{m\in\mathbf Z}c_mu_m$ vanishes over $\pi_v^k\mathcal O_{F_v}-\pi_v^{k+1}\mathcal O_{F_v}$ for every $k\in\mathbf Z$. This means that $f-\sum_{m\in\mathbf Z}c_mu_m$ vanishes over $F_v^\times$, and by continuity it vanishes over $F_v$, forcing $f=\sum_{m\in\mathbf Z}c_mu_m$.

The set $\{1_{\pi_v^m\mathcal O_{F_v}},m\in\mathbf Z\}$ is therefore an algebraic $\mathbf C$-linear basis for $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$.

Since $1_{\pi_v\mathcal O_{F_v}}=z\cdot 1_{\mathcal O_{F_v}}$, we see that we have $\mathbf C[z^{\pm 1}]\cdot 1_{\mathcal O_{F_v}}=\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$.

The Hausdorff locally convex topological vector space $\mathcal S(F_v)$ is itself endowed with the final locally convex topology, since it is the strict locally convex inductive limit of finite dimensional $\mathbf C$-linear subspaces, spanned by locally constant functions whose compact support is contained in $\pi_v^N\mathcal O_{F_v}$, as $N$ varies over $\mathbf Z$, and that are invariant under $\pi_v^{N'}\mathcal O_{F_v}$ for some $N'\le N$. We call such finite dimensional subspace $W_{N,N'}$.

Such functions that are contained in $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$ are spanned by $z^m\cdot 1_{\mathcal O_{F_v}}$ for $N'\le m\le N$, which implies that the linear left-inverse of the inclusion of $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$ is continuous when restricted to the intersection with $W_{N,N'}$, since such intersection is finite dimensional and hence linearly homeomorphic to its image in $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$ endowed with the subspace topology of the locally convex inductive limit topology induced by the Euclidean topologies on the finite dimensional subspaces $\bigoplus_{N'\le m\le N}\mathbf C z^m\cdot 1_{\mathcal O_{F_v}}$. Such inductive limit topology on $\mathbf C[z^{\pm 1}]\cdot 1_{\mathcal O_{F_v}}$ is the final locally convex topology by [Tre, Part I,Ch.13,Example 1] and [Scha, Ch.II,p.56,Example] (see also [Scha, Ch.II,p.69,Exercise 7]).

By [Tre, Part I,Ch.13,Thm.13.1], $\mathbf C[z^{\pm 1}]\cdot 1_{\mathcal O_{F_v}}$ is complete with respect to such inductive limit topology, and since such topology is the subspace topology inherited from $\mathcal S(F_v)$, $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$ is a complete, hence closed (by [Bou-GT, Ch.II,§3.4,Prop.8]), subspace.

## PDF page 290

**290** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

(2) : Since, by Corollary 2.1.4.2, the continuous linear operator

$$
\mathcal S(\mathbf A_{F,S})\otimes_\pi\mathcal S(\prod_{v\in S'-S}F_v)\to\mathcal S(\mathbf A_{F,S'})
$$

is a linear topological isomorphism, and $\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'}))$ is endowed with the subspace topology inherited from the Hausdorff locally convex topology on $\mathcal S(\mathbf A_{F,S'})$, in order to prove (2) it is enough to show that the following assertions hold:

(1) The linear operator

$$
\mathbf C[z_v^{\pm 1},v\in S'-S]\to\mathcal S(\prod_{v\in S'-S}F_v) \tag{6.1.2.7}
$$

defined in (b) and uniquely determined by the assignment from (6.1.2.6), is a linear topological embedding onto $\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))$.

(2) The linear map:

$$
\mathcal S(\mathbf A_{F,S})\otimes\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))\to\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'}))
$$

is a linear isomorphism.

Indeed, by Proposition 2.1.4.1(1), $\mathcal S(\mathbf A_{F,S})$ is nuclear, and hence the continuous linear operator $\mathcal S(\mathbf A_{F,S})\otimes_\pi E_1\to\mathcal S(\mathbf A_{F,S})\otimes_\pi E_2$ induced by a linear topological embedding $E_1\to E_2$ of Hausdorff locally convex topological $\mathbf C$-vector spaces is itself a linear topological embedding (see [Jar, Part III,Ch.16.2,Cor.3]).

Upon applying this to $E_1=\mathbf C[z_v^{\pm 1},v\in S'-S]$ and $E_2=\mathcal S(\prod_{v\in S'-S}F_v)$, we obtain from (1) that the continuous linear operator from (6.1.2.5) is a linear topological embedding. By (2), we obtain that it is surjective, and hence a linear topological isomorphism.

(1) follows from compatibility of the linear operator (6.1.2.7) with the linear topological isomorphism $\mathcal S(\prod_{v\in S'-S}F_v)\simeq\bigotimes_{v\in S'-S}\mathcal S(F_v)$, the tensor product being projective and already complete, since the factors are endowed with the final locally convex topology, being $S'-S$ comprised of non-Archimedean places only. The linear topological embeddings $\mathbf C[z_v^{\pm 1}]\to\mathcal S(F_v)$ combine into the continuous linear operator in (6.1.2.7), itself a linear topological embedding by [Jar, Part III,Ch.16.2,Cor.3].

Since $\mathrm{Pic}(\mathcal O_{F,S})=1$, the quotient homomorphism

$$
C_F/\widehat{\mathcal O}_{F,\Sigma_F-S}^\times\to J_{F,S} \tag{6.1.2.8}
$$

is an isomorphism of Hausdorff locally compact abelian groups. Since we have that the continuous homomorphism

$$
(\mathrm{GL}_1(\mathbf A_{F,S})\times\widehat{\mathcal O}_{F,\Sigma_F-S}^\times)/\mathcal O_{F,S}^\times\to\mathrm{GL}_1(\mathbf A_F)/F^\times=C_F \tag{6.1.2.9}
$$

is an isomorphism, being its cokernel $\mathrm{Pic}(\mathcal O_{F,S})$, the kernel of quotient homomorphism $C_F\to J_{F,S}$ is isomorphic to both $\widehat{\mathcal O}_{F,\Sigma_F-S}^\times/\mathcal O_{F,S}^\times$ and $\widehat{\prod}_{v\notin S}(F_v^\times,\mathcal O_{F_v}^\times)/F^\times$.

This in turn implies that the continuous homomorphism:

$$
F^\times/\mathcal O_{F,S}^\times\to\widehat{\prod}_{v\notin S}(F_v^\times,\mathcal O_{F_v}^\times)/\widehat{\mathcal O}_{F,\Sigma_F-S}^\times \tag{6.1.2.10}
$$

is also an isomorphism.

Since $S\subset S'$, then $\mathrm{Pic}(\mathcal O_{F,S'})=1$, and (6.1.2.10) being an isomorphism holds for $S'$ in place of $S$ too. By [DE, Lemma 13.3.1(b)] it follows that the continuous homomorphism:

$$
\prod_{v\in S'-S}(F_v^\times/\mathcal O_{F_v}^\times)\to\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times \tag{6.1.2.11}
$$

## PDF page 291

**6.1. STRUCTURE THEOREM IV: LOCAL WITHIN GLOBAL** · **291**

is an isomorphism.

To show that the linear topological embedding $\mathbf C[z_v^{\pm 1},v\in S'-S]\to\mathcal S(\prod_{v\in S'-S}F_v)$ is surjective onto $\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))$, it is enough to check that it is so upon further composing it with the injective $\mathbf C$-linear map $\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))\to\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,C_c^\infty(\prod_{v\in S'-S}F_v^\times))$, which, explicitly, is uniquely determined by sending the monomial $\prod_{v\in S'-S}z_v^{a_v}$, for $(a_v)_{v\in S'-S}\in\mathbf Z^{\lvert S'\rvert-\lvert S\rvert}$, to $\prod_{v\in S'-S}1_{\pi_v^{a_v}\mathcal O_{F_v}^\times}$.

Since $\widehat{\mathcal O}_{F,S'-S}^\times$ is a compact Hausdorff abelian group, integration of smooth compactly supported functions over $\widehat{\mathcal O}_{F,S'-S}^\times$ with respect to the Radon product measure $\bigotimes_{v\in S'-S}\mu_v$, $\mu_v$ being the local Tamagawa measure from Definition A.3.2.2, identifies $\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,C_c^\infty(\prod_{v\in S'-S}F_v^\times))$ with $C_c^\infty(\prod_{v\in S'-S}F_v^\times/\mathcal O_{F_v}^\times)=\mathbf C[\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times]$, using the isomorphism from (6.1.2.11), and the surjectivity assertion follows. To see the identification:

$$
\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,C_c^\infty(\prod_{v\in S'-S}F_v^\times))\to C_c^\infty(\prod_{v\in S'-S}F_v^\times/\mathcal O_{F_v}^\times) \tag{6.1.2.12}
$$

the linear operator being given by integration over $\widehat{\mathcal O}_{F,S'-S}^\times$ with respect to $\bigotimes_{v\in S'-S}\mu_v$, we note that it holds upon replacing $C_c^\infty(\prod_{v\in S'-S}F_v^\times)$ with $C_c(\prod_{v\in S'-S}F_v^\times)$: surjectivity holds by the proof [DE, Lemma 1.5.1] upon choosing the function $\phi$ to be $\widehat{\mathcal O}_{F,S'-S}^\times$-invariant, which we can do by compactness of $\widehat{\mathcal O}_{F,S'-S}^\times$.

Indeed, we fix $f\in C_c(\prod_{v\in S'-S}F_v^\times/\widehat{\mathcal O}_{F,S'-S}^\times)$, whose support $K$ is compact. There exists a compact subset $C\subset\prod_{v\in S'-S}F_v^\times$ whose image in the quotient $\prod_{v\in S'-S}F_v^\times/\widehat{\mathcal O}_{F,S'-S}^\times$ contains $K$. Upon replacing the compact subset $C$ with $\widehat{\mathcal O}_{F,S'-S}^\times\cdot C$, also compact by [DE, Lemma 1.1.3(d)], the indicator function $1_C$ qualifies as such $\phi$.

Injectivity holds since the volume of $\widehat{\mathcal O}_{F,S'-S}^\times$ with respect to $\bigotimes_{v\in S'-S}\mu_v$ is finite and nonzero.

It is therefore enough to show that the linear inclusion $C_c^\infty(\prod_{v\in S'-S}F_v^\times)\to C_c(\prod_{v\in S'-S}F_v^\times)$ induces an isomorphism on $\widehat{\mathcal O}_{F,S'-S}^\times$-invariants.

Let $f:\prod_{v\in S'-S}F_v^\times\to\mathbf C$ be a continuous compactly supported function, and assume that $f$ is $\widehat{\mathcal O}_{F,S'-S}^\times$-invariant. Let $K\subset\prod_{v\in S'-S}F_v^\times$ be the support of $f$. It is contained into a finite union of compact subsets of the form $K_{(a_v)_{v\in S'-S}}:=\prod_{v\in S'-S}\pi_v^{a_v}\mathcal O_{F_v}^\times$, for $(a_v)_{v\in S'-S}\in\mathbf Z^{\lvert S'\rvert-\lvert S\rvert}$, each of which is $\widehat{\mathcal O}_{F,S'-S}^\times$-stable. The restriction of $f$ to $K_{(a_v)_{v\in S'-S}}$ is therefore constant, since each $K_{(a_v)_{v\in S'-S}}$ is the orbit under the continuous $\widehat{\mathcal O}_{F,S'-S}^\times$-action on $\prod_{v\in S'-S}F_v^\times$ of the single point $(\pi_v^{a_v})_{v\in S'-S}$. Since each $K_{(a_v)_{v\in S'-S}}$ is open, we deduce that $f$ is locally constant over $\prod_{v\in S'-S}F_v^\times$, hence smooth. This concludes the proof of (1).

In order to finish the proof of part (2), we prove claim (2): we call $G:=\widehat{\mathcal O}_{F,S'-S}^\times$, $M_1:=\mathcal S(\mathbf A_{F,S})$, $M_2:=\mathcal S(\prod_{v\in S'-S}F_v)$ as a $\mathbf C[G]$-module, we have the following short-exact sequence:

$$
0\to M_1\otimes_{\mathbf C}\mathrm{Hom}_{\mathbf C[G]}(\mathbf C,M_2)\to\mathrm{Hom}_{\mathbf C[G]}(\mathbf C,M_1\otimes_{\mathbf C}M_2)\to\mathrm{Tor}_1^{\mathbf C}(M_1,\mathrm{Ext}^1_{\mathbf C[G]}(\mathbf C,M_2))\to 0
$$

where $\mathrm{Tor}_1^{\mathbf C}(M_1,\mathrm{Ext}^1_{\mathbf C[G]}(\mathbf C,M_2))=0$ since $M_1$ is a $\mathbf C$-vector space, and the first map is the inclusion $\mathcal S(\mathbf A_{F,S})\otimes\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))\to\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S})\otimes\mathcal S(\prod_{v\in S'-S}F_v))$, which is therefore a linear isomorphism. The claim therefore follows from Corollary 2.1.4.2 and the fact that the linear space underlying the projective tensor product in Corollary 2.1.4.2 is the algebraic tensor product. follows from the fact that $\widehat{\mathcal O}_{F,S'-S}^\times$ acts trivially on $\mathcal S(\mathbf A_{F,S})$. $\square$

We need the following:

LEMMA 6.1.2.4. *Let $F$ be a number field, $v$ a finite place of $F$. Let $\pi_v$ be a uniformizer at $v$. Let $S,S'$ be finite sets of places of $F$ containing all Archimedean places, with $S\subset S'$.*

*(1) The linear subspace $V$ of $\mathcal S(F_v)$ generated by the elements $f_\xi$, with $f_\xi(x):=f(x)-f(\xi^{-1}x)$ for $f\in\mathcal S(F_v)$, as $\xi\in\mathcal O_{F_v}^\times$, is closed, and $\mathrm H_0(\mathcal O_{F_v}^\times,\mathcal S(F_v))=\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F_v}^\times,\mathcal S(F_v))$.*

## PDF page 292

**292** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

*(2) The linear operator*

$$
\Phi_v:\mathcal S(F_v)\to C_c(F_v) \tag{6.1.2.13}
$$

*defined by sending $f\in\mathcal S(F_v)$ to the continuous function of $g\in F_v$:*

$$
\Phi_v(f)(g):=\int_{\mathcal O_{F_v}^\times}f(gh)\,\mathrm d\mu_v(h) \tag{6.1.2.14}
$$

*is continuous upon endowing $C_c(F_v)$ with the uniform norm, it is valued in $\mathcal S(F_v)$ and continuous with respect to the Hausdorff locally convex topology on $\mathcal S(F_v)$, and its kernel is $V$. The induced linear map:*

$$
N_v:\mathrm H_0(\mathcal O_{F_v}^\times,\mathcal S(F_v))\to\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v)) \tag{6.1.2.15}
$$

*obtained by factoring $\Phi_v$ through the quotient $\mathcal S(F_v)/V\simeq\mathrm H_0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$, is a linear topological isomorphism.*

*(3) The linear subspace $\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))$ of $\mathcal S(\prod_{v\in S'-S}F_v)$ is closed. The induced linear map:*

$$
N_{S,S'}:\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))\to\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v)) \tag{6.1.2.16}
$$

*obtained by factoring $\prod_{v\in S'-S}\Phi_v$ through $\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))$, is a linear topological isomorphism.*

PROOF. (1) : Since $v$ is finite, $\mathcal S(F_v)$ is endowed with the final locally convex topology. Every linear subspace is therefore closed, and hence the quotient $\mathcal S(F_v)/V$, endowed with the quotient topology, is Hausdorff and itself endowed with the final locally convex topology. It follows that we have $\mathrm H_0(\mathcal O_{F_v}^\times,\mathcal S(F_v))=\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F_v}^\times,\mathcal S(F_v))$.

(2) : Since $f\in\mathcal S(F_v)$ is compactly supported, then upon calling $K$ its support we obtain that $\Phi_v(f)$, as a function of $g\in F_v$, continuous by Dominated Convergence and compactness of $\mathcal O_{F_v}^\times$, is supported over $\mathcal O_{F_v}^\times\cdot K$, itself a compact subset of $F_v$ by [DE, Lemma 1.3.1(d)].

The function $\Phi_v(f)$ equals $f\ast 1_{\mathcal O_{F_v}^\times}$, as can be checked upon reducing to the case $f=1_K$ by $\mathbf C$-linearity of $\Phi_v$, given that every element of $\mathcal S(F_v)$ is a finite $\mathbf C$-linear combination of indicator functions $1_K$ for $K$ a compact subset of $F_v$. This shows continuity of $\Phi_v$. It also shows that, since $1_{\mathcal O_{F_v}^\times}$ is itself a Schwartz-Bruhat function on $F_v$, and the dual group of $F_v$ is isomorphic to $F_v$ itself as a Hausdorff locally compact abelian group, $\Phi_v$ is valued in $\mathcal S(F_v)$, since the Fourier transform of a convolution of two Schwartz-Bruhat functions is the product of their Fourier transforms, hence itself a Schwartz-Bruhat function, and the Fourier transform is a linear topological automorphism of $\mathcal S(F_v)$.

Since $\Phi_v(f)$ is $\mathcal O_{F_v}^\times$-invariant, $\Phi_v$ is valued in $\mathrm H^0(\mathcal O_{F_v}^\times,\mathcal S(F_v))$.

We note that the Mellin transform $Z_v(f,c)$ of any $f\in\mathcal S(F_v)$, for $c\in\Omega(F_v^\times)$, is meromorphic, with poles located within the polar set of the function $\rho_v(c)$, and the operator $L_v$ factors through $\Phi_v$ by Theorem D.1.2.1. This implies $\ker(\Phi_v)\subset\ker(L_v)$.

The reverse inclusion also holds, since if $Z_v(f,c)=0$, then $\lvert\cdot\rvert_v\cdot f$ satisfies:

$$
\int_{F_v^\times}f(g)\lvert g\rvert_v^{it}\,\mathrm d\mu_v(g)=\int_{F_v}f(g)\lvert g\rvert_v^{it}\,\mathrm d\mu_v(g)=Z_v(f,\lvert\cdot\rvert_v^{it})=0 \tag{6.1.2.17}
$$

for every $t\in\mathbf R$. This implies that the function $\lvert\cdot\rvert_v\cdot f$, which is smooth and compactly supported over $F_v^\times$, has vanishing Fourier transform, and hence $\lvert\cdot\rvert_v\cdot f=0$. Since $\lvert\cdot\rvert_v$ is continuous and nowhere vanishing over $F_v^\times$, we deduce that $f=0$ over $F_v^\times$, and hence it is zero everywhere over $F_v$ by continuity.

By Theorem 3.4.3.3, the local eigendistribution $\Delta'_v(c)$, as $c\in\Omega(F_v^\times)$ is an element of $V^\perp$, where the orthogonal is formed with respect to the duality $\langle\mathcal S(F_v),\mathcal S(F_v)'_\beta\rangle$.

Let $f\in\ker(\Phi_v)$. Then $Z_v(f,c)=\Delta'_v(c)(f)\cdot L_v(c)$, where $L_v(c)$ is the local Hecke $L$-function at $v$. It follows that we have $\Delta'_v(c)(f)=0$ for every $c\in\Omega(F_v^\times)(1)$ (i.e. $c|_{\mathcal O_{F_v}^\times}=1$), which places $f$ in the closure of

## PDF page 293

**6.1. STRUCTURE THEOREM IV: LOCAL WITHIN GLOBAL** · **293**

$V$, which is $V$ itself by (1). We deduce that $f$ is annihilated by $V^\perp$, which, by Theorem 5.5.3.2, is linearly and topologically generated by the functionals $\{\Delta'_v(c),c\in\Omega(F_v^\times)(1)\}$, and so we have $V=\ker(\Phi_v)$ (since $f$ is then contained in the closure of $V$ with respect to the $\sigma(\mathcal S(F_v),\mathcal S(F_v)'_\beta)$-topology by [NB, Thm.8.9.2(e)], which is the intrinsic topology on $\mathcal S(F_v)$ by [NB, Thm.11.3.6], which applies since $\mathcal S(F_v)$ is barrelled, and since $V$ is closed by (1) we deduce $V=\ker(\Phi_v)$). It follows that $\Phi_v$ induces the linear topological isomorphism $N_v$.

(3) : Since $S'-S$ is comprised of non-Archimedean places only, the linear topologies on the source and target of $N_{S,S'}$ are both the final locally convex topology. $N_{S,S'}$ is therefore a linear topological isomorphism so long as it is bijective. The operator $N_{S,S'}$ is the convolution operator $f\mapsto f\ast 1_{\widehat{\mathcal O}_{F,S'-S}^\times}$, which is therefore valued in $C_c(\prod_{v\in S'-S}F_v)$ and its range is contained in $\mathcal S(\prod_{v\in S'-S}F_v)$, since $\widehat{\mathcal O}_{F,S'-S}^\times$ is compact open in $\prod_{v\in S'-S}F_v$ and hence $1_{\widehat{\mathcal O}_{F,S'-S}^\times}$ is itself a Schwartz-Bruhat function on $\prod_{v\in S'-S}F_v$.

Its kernel coincides with the subspace $V_{S,S'}$ which is linearly generated by the elements $f_\xi(x):=f(x)-f(\xi^{-1}x)$ as functions of $x\in\prod_{v\in S'-S}F_v$, as $f$ varies over the Schwartz-Bruhat functions on $\prod_{v\in S'-S}F_v$ and $\xi$ varies over $\widehat{\mathcal O}_{F,S'-S}^\times$.

To see this, we use Theorem 5.5.3.2 to see that if $f\in\ker(\prod_{v\in S'-S}\Phi_v)$, then $(\bigotimes_{v\in S'-S}\Delta'_v(c))(f)=0$ for all $c\in\Omega(\prod_{v\in S'-S}F_v)(1)=\coprod_{v\in S'-S}\Omega(F_v^\times)(1)$ (i.e. such that $c|_{\widehat{\mathcal O}_{F,S'-S}^\times}=1$, equivalently $c_v|_{\mathcal O_{F_v}^\times}=1$ for every $v\in S'-S$), which implies that $V_{S,S'}^\perp$ annihilates $f$, and hence $f\in V_{S,S'}$ (since $f$ is then in the closure of $V_{S,S'}$ with respect to the $\sigma(\mathcal S(\prod_{v\in S'-S}F_v),\mathcal S(\prod_{v\in S'-S}F_v)'_\beta)$-topology by [NB, Thm.8.9.2(e)], and since $\mathcal S(\prod_{v\in S'-S}F_v)$ is barrelled, then the weakened topology on $\mathcal S(\prod_{v\in S'-S}F_v)$ is equivalent to the intrinsic topology on $\mathcal S(F_v)$ by [NB, Thm.11.3.6], and since $V_{S,S'}$ is closed we deduce $V_{S,S'}=\ker(\prod_{v\in S'-S}\Phi_v)$). $\square$

Let $R\to R'$ be a flat ring map, $M$ an $R$-module, $M'$ an $R'$-module. We refer to the Grothendieck spectral sequence (applied to the composition of the right-exact functor $M'\otimes_{R'}(\cdot)$ on $R'$-modules, and the exact functor $R'\otimes_R(\cdot)$ from $R$-modules to $R'$-modules, to which [Gro-d, Théorème.2.4.1] applies to the opposites of the categories of $R$-modules and $R'$-modules, since, by $R$-flatness of $R'$, we have $\mathrm{Tor}^{R'}_m(R'\otimes_R P,\cdot)=0$ for every projective $R$-module $P$ and every integer $m\ge 1$):

$$
E^2_{p,q}:=\mathrm{Tor}^{R'}_p(\mathrm{Tor}^R_q(M,R'),M')\Rightarrow\mathrm{Tor}^R_{p+q}(M,M')
$$

as the change-of-rings spectral sequence for Tor-functors.

PROOF OF THEOREM 6.1.2.1. We consider the $\mathbf C$-linear map:

$$
\mathrm{Tor}^{\mathbf C[\mathcal O_{F,S}^\times]}_0(\mathbf C,\mathcal S(\mathbf A_{F,S}))\to\mathrm{Tor}^{\mathbf C[\mathcal O_{F,S'}^\times]}_0(\mathbf C,\mathcal S(\mathbf A_{F,S'})). \tag{6.1.2.18}
$$

The $\mathbf C$-algebra map $\mathbf C[\mathcal O_{F,S}^\times]\to\mathbf C[\mathcal O_{F,S'}^\times]$ is flat, and identifies, upon choosing a homomorphic section $\sigma$ to the surjective group homomorphism $\mathcal O_{F,S'}^\times\to\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times$, the $\mathbf C$-algebra $\mathbf C[\mathcal O_{F,S'}^\times]$ with the $\mathbf C$-algebra $\mathbf C[\mathcal O_{F,S}^\times]\otimes_{\mathbf C}\mathbf C[\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times]$.

By Lemma 6.1.2.2(2), the $\mathbf C[\mathcal O_{F,S'}^\times]$-module $\mathcal S(\mathbf A_{F,S'})$ is isomorphic, as a $\mathbf C[\mathcal O_{F,S'}^\times]$-module, to

$$
\mathcal S(\mathbf A_{F,S})\otimes\mathbf C[\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times]
$$

where the $\mathbf C[\mathcal O_{F,S'}^\times]$-module structure on $\mathcal S(\mathbf A_{F,S})$ is defined through the quotient $\mathbf C[\mathcal O_{F,S'}^\times]\to\mathbf C[\mathcal O_{F,S}^\times]$ induced by the quotient by $\sigma(\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times)$, and on $\mathbf C[\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times]$ by the quotient $\mathcal O_{F,S'}^\times\to\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times$.

By the change-of-rings spectral sequence for Tor-functors, we have a canonical $\mathbf C$-linear isomorphism:

$$
\mathrm{Tor}^{\mathbf C[\mathcal O_{F,S}^\times]}_0(\mathbf C,\mathcal S(\mathbf A_{F,S}))\to\mathrm{Tor}^{\mathbf C[\mathcal O_{F,S'}^\times]}_0(\mathbf C,\mathcal S(\mathbf A_{F,S})\otimes\mathbf C[\mathcal O_{F,S'}^\times/\mathcal O_{F,S}^\times])
$$

which implies that the image of the linear operator from (6.1.2.18) is:

$$
\mathrm{Tor}^{\mathbf C[\mathcal O_{F,S'}^\times]}_0(\mathbf C,\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'}))).
$$

## PDF page 294

**294** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

By Lemma 6.1.2.4(3) combined with Corollary 2.1.4.2, the linear isomorphism $N_{S,S'}$ induces a linear isomorphism, which we also denote $N_{S,S'}$:

$$
N_{S,S'}:\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'}))\to\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'})). \tag{6.1.2.19}
$$

Indeed, the linear topological isomorphism from (6.1.2.16) of Lemma 6.1.2.4 induces a linear isomorphism:

$$
\mathcal S(\mathbf A_{F,S})\otimes\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))\to\mathcal S(\mathbf A_{F,S})\otimes\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v)) \tag{6.1.2.20}
$$

where the source is linearly isomorphic to $\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S})\otimes\mathcal S(\prod_{v\in S'-S}F_v))$ since formation of tensor products commutes with formation of quotients on $\mathbf C$-linear spaces.

We have, upon calling $G:=\widehat{\mathcal O}_{F,S'-S}^\times$, $M_1:=\mathcal S(\mathbf A_{F,S})$, $M_2:=\mathcal S(\prod_{v\in S'-S}F_v)$ as a $\mathbf C[G]$-module, the short-exact sequence:

$$
0\to M_1\otimes_{\mathbf C}\mathrm{Hom}_{\mathbf C[G]}(\mathbf C,M_2)\to\mathrm{Hom}_{\mathbf C[G]}(\mathbf C,M_1\otimes_{\mathbf C}M_2)\to\mathrm{Tor}^{\mathbf C}_1(M_1,\mathrm{Ext}^1_{\mathbf C[G]}(\mathbf C,M_2))\to 0
$$

where $\mathrm{Tor}^{\mathbf C}_1(M_1,\mathrm{Ext}^1_{\mathbf C[G]}(\mathbf C,M_2))=0$ since $M_1$ is a $\mathbf C$-vector space, and the first map is the inclusion $\mathcal S(\mathbf A_{F,S})\otimes\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\prod_{v\in S'-S}F_v))\to\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S})\otimes\mathcal S(\prod_{v\in S'-S}F_v))$. It follows that such map is a linear isomorphism, therefore identifying the target of (6.1.2.20) with $\mathrm H^0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S})\otimes\mathcal S(\prod_{v\in S'-S}F_v))$, giving the linear isomorphism $N_{S,S'}$ from (6.1.2.19) upon applying Corollary 2.1.4.2.

Upon evaluating the functor $\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\cdot)$ on the linear surjective map:

$$
\mathcal S(\mathbf A_{F,S'})\to\mathrm H_0(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))
$$

we obtain a linear surjection:

$$
\mathrm H_0(\widehat{\mathcal O}_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))\to\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathrm H_0(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S'}))) \tag{6.1.2.21}
$$

which factors through $\mathrm H_0(\mathcal O_{F,S'}^\times,\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'})))$, since for every element $\xi\in\mathcal O_{F,S'}^\times$ and every Schwartz-Bruhat function $f\in\mathcal S(\mathbf A_{F,S'})$, the function $f(x)-f(\xi^{-1}x)$ of $x\in\mathbf A_{F,S'}$ is annihilated by the linear map from (6.1.2.21).

We therefore obtain a linear surjective map:

$$
\mathrm H_0(\mathcal O_{F,S'}^\times,\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathcal S(\mathbf A_{F,S'})))\to\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathrm H_0(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))) \tag{6.1.2.22}
$$

Since

$$
\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathrm H_0(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'})))\to\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'})))
$$

is surjective, since $\mathrm H_0(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))\to\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$ is and $\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\cdot)$ is right-exact on $\mathbf C[\widehat{\mathcal O}_{F,S'-S}^\times]$-modules, we deduce that the range of $\bar\pi_{S,S'}$ is the image of

$$
\mathrm H_0(\widehat{\mathcal O}_{F,S'-S}^\times,\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'})))
$$

in $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$ under the linear surjective operator $N_G$ from Lemma 4.3.3.1, with $G=\widehat{\mathcal O}_{F,S'-S}^\times$, and $E=\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$, which is complete by Theorem 5.2.1.1, hence quasi-complete, implying that the Lemma applies. Note that to see that the action of $\widehat{\mathcal O}_{F,S'-S}^\times$ on $\mathcal S(\mathbf A_{F,S'})$, and hence on $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S'}^\times,\mathcal S(\mathbf A_{F,S'}))$, is uniformly continuous, it is enough to show that it is so on $\mathcal S(\prod_{v\in S'-S}F_v)$. Since $\mathcal S(\prod_{v\in S'-S}F_v)$ is the strict locally convex inductive limit of a countable sequence of increasingly nested finite dimensional subspaces, and every convergent Cauchy net in $\mathcal S(\prod_{v\in S'-S}F_v)$ is eventually bounded $^1$ (i.e. for $\{f_i\}_{i\in I}$ such Cauchy net, there exists $i_0\in I$ such that $\{f_i\}_{i\in I,i\ge i_0}$ is bounded. We may rename $I_0:=\{i\in I:i\ge i_0\}$ as $I$) by

---

$^1$Return here.

## PDF page 295

**6.2. STRUCTURE THEOREM V: ISOTYPIC EXHAUSTIVENESS** · **295**

[Scha, Ch.II,§6,6.5] such fixed convergent Cauchy net $\{f_i\}_{i\in I}\subset\mathcal S(\prod_{v\in S'-S}F_v)$ and its limit are the image of a convergent Cauchy net contained in a finite dimensional subspace of $\mathcal S(\prod_{v\in S'-S}F_v)$. $^2$

Without loss of generality, we may assume $S'-S=\{v\}$, a single finite place, and that such finite dimensional subspace $V$ is the finite dimensional subspace linearly generated in $\mathcal S(F_v)$ by the locally constant compactly supported functions that are invariant under $\pi_v^N\mathcal O_{F_v}$ for some integer $N$, and whose support is contained in $\pi_v^{N'}\mathcal O_{F_v}$, for $N'\le N$. Since $\pi_v^{N'}\mathcal O_{F_v}$ is $\mathcal O_{F_v}^\times$-stable, and for any $\pi_v^N\mathcal O_{F_v}$-invariant locally constant function $f$ on $F_v$, its translate $\rho_{\mathcal O_{F_v}^\times}(g,f)$ is also $\pi_v^N$-invariant for every $g\in\mathcal O_{F_v}^\times$, we see that the continuous action of $\mathcal O_{F_v}^\times$ preserves $V$, and hence the convergent Cauchy net $\{f_i\}_{i\in I}\subset V$ and its limit, is such that its $\mathcal O_{F_v}^\times$-orbit is also contained in $V$. Since $V$ has its Euclidean topology and the action is continuous, then being $\mathcal O_{F_v}^\times$ profinite its action on $V$ factors through a finite quotient, and it is therefore uniformly continuous. $^3$

We further refer the reader to Lemma 2.1.2.10.

The assumptions of Lemma 4.3.3.1 are therefore met.

By Lemma 4.3.3.1, the range of $N_G$, and hence of $\bar\pi_{S,S'}$, is $\mathrm H^0(\widehat{\mathcal O}^\times_{F,S'-S},\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'})))$, as desired. $\square$

**6.2. Structure Theorem V: isotypic exhaustiveness**

We conclude this Chapter with the final Structure Theorem on the spaces

$$
\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)),\quad \mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))
$$

and their isotypes.

It amounts to the statement that so long as the finite set of places $S$ containing all Archimedean places, is large enough, so as to ensure $\mathrm{Pic}(\mathcal O_{F,S})=1$ holds and, for each given continuous character $\omega$ of $C^1_F$, that $\omega$ is unramified outside $S$, then the transition operator:

$$
\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))
$$

is a linear topological isomorphism. Recall from the First Structure Theorem (see Theorem 5.2.3.1) that $\bar\pi_S$ is a linear topological embedding. The assertion on $\bar\pi_S$ being a linear topological isomorphism therefore amounts to the surjectivity of $\bar\pi_S$, and it requires the homology calculations from the previous section.

**6.2.1. Eventual surjectivity of $\bar\pi_{S,S'}$ and $\bar\pi_S$.**

THEOREM 6.2.1.1 (Fifth Structure Theorem). *Let $F$ be a number field, $S,S'$ finite sets of places of $F$ containing all Archimedean places, such that $S\subset S'$. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$.*

*(1) Let $\omega$ be a continuous character of $J^1_{F,S'}$, unramified outside $S$. Then $\bar\pi_{S,S'}:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S'}))$ from (5.2.3.1) is surjective, hence a linear topological isomorphism.*

*(2) Let $\omega$ be a continuous character of $C^1_F$, unramified outside $S$. Then $\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ induced by the linear topological isomorphism from (5.2.3.2) is surjective, hence a linear topological isomorphism.*

We record here the following Corollary:

COROLLARY 6.2.1.2. *Let $F$ be a number field, $\omega\in\widehat{C^1_F}$ a continuous character. Then $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ is a nuclear Fréchet space.*

PROOF. By Theorem 6.2.1.1, upon choosing $\chi\in\widehat{C_F}$ a continuous character such that $\chi|_{C^1_F}=\omega$, and $S$ a large enough set of places of $F$ such that $\chi$ is unramified outside $S$ and $\mathrm{Pic}(\mathcal O_{F,S})=1$, $\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ is a linear topological isomorphism, with $\omega_S$ the unique continuous

---
$^2$Return here.

$^3$Return here.

## PDF page 296

**296** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

character of $J^1_{F,S}$ descended from $\omega|_{C^1_{F,S}}$ by $\widehat{\mathcal O}^\times_{\Sigma_F-S}$-invariance. By Theorem 5.4.1.1(2), $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F))$ is a nuclear Fréchet space. $\square$

Before we prove the Theorem, we need the following result about the type of continuity for the continuous action $\rho_{F,S}$ of $J_{F,S}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$.

LEMMA 6.2.1.3. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all Archimedean places.*

*(1) The action of $J^1_{F,S}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ is uniformly continuous, i.e. for any convergent Cauchy net $\{f_i\}_{i\in I}\subset\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ with limit $f$, we have $\rho_{F,S}(g,f_i)\to\rho_{F,S}(g,f)$ uniformly as $g\in J^1_{F,S}$.*

*(2) The action of $J^1_{F,S}$ twisted by the continuous character $\omega\in\widehat{J^1_{F,S}}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ is uniformly continuous, i.e. for any convergent Cauchy net $\{f_i\}_{i\in I}\subset\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ with limit $f$, we have $\omega(g)\rho_{F,S}(g,f_i)\to\omega(g)\rho_{F,S}(g,f)$ uniformly as $g\in J^1_{F,S}$.*

PROOF. (1) follows from (2). Since $\omega$ is unitary, for any continuous seminorm $p$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ we have $p(\omega(g)\rho_{F,S}(g,f))=p(\rho_{F,S}(g,f))$ for any $f\in\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$, and so it is enough to treat the case $\omega=1$, i.e. (2) follows from (1) too.

We enow the linear image $\mathcal L_{F,S}$ of $Z_S:\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))\to\mathscr M(\Omega(J_{F,S}))$ with a Hausdorff locally convex topology making the operator $L_S$ continuous.

We have:

$$
Z_S(\rho_{F,S}(g,f_i),c)=c(g)Z_S(f_i,c)
$$

for each $g\in J_{F,S}$, and similarly for $Z_S(\rho_{F,S}(g,f),c)=c(g)Z_S(f,c)$. If $g\in J^1_{F,S}$, then $c(g)$ is unimodular, and so for any continuous seminorm $p$ on $\mathcal L_{F,S}$, we have

$$
p(Z_S(\rho_{F,S}(g,f_i),c)-Z_S(\rho_{F,S}(g,f),c))=p(Z_S(\rho_{F,S}(g,f_i)-\rho_{F,S}(g,f),c))=p(Z_S(f_i-f,c))
$$

and since $f_i\to f$ in $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $p$ is continuous, we have

$$
\sup_{g\in J^1_{F,S}}(Z_S(\rho_{F,S}(g,f_i)-\rho_{F,S}(g,f),c))=p(Z_S(f_i-f,c))\to 0
$$

which means $Z_S(\rho_{F,S}(g,f_i),c)\to Z_S(\rho_{F,S}(g,f),c)$ uniformly over $J^1_{F,S}$ in any locally convex topology on $\mathcal L_{F,S}$ making $Z_S:\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))\to\mathcal L_{F,S}$ continuous.

In particular, we may endow $\mathcal L_{F,S}$ with the quotient topology induced by $L_S$, which is the finest making $L_S$ continuous and a linear topological isomorphism. For any continuous seminorm $p$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$, there therefore exist, by [NB, Thm.5.7.3], a continuous seminorm $q$ on $\mathcal L_{F,S}$ such that $p\le q\circ L_S$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$.

By the foregoing, we obtain

$$
\sup_{g\in J^1_{F,S}}p(\rho_{F,S}(g,f_i)-\rho_{F,S}(g,f))\to 0
$$

and hence the action $\rho_{F,S}$ of $J^1_{F,S}$ on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ is uniformly continuous. $\square$

PROOF OF THEOREM 6.2.1.1. (1) : We apply Lemma 4.3.3.1 to $E:=\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'}))$ and $G:=J^1_{F,S'}$. The Lemma indeed applies because $G$ is compact Hausdorff and abelian, $E$ is complete by Theorem 5.2.1.1(2), hence quasi-complete, and the action $\rho_G:=\bar\omega\cdot\rho_{F,S'}$ is uniformly continuous on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'}))$ by Lemma 6.2.1.3.

The operator $\Phi_G$ therefore takes values in $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'}))$ itself and it is continuous, with range exactly $\mathrm H^0(\omega,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'})))$, i.e. the closed subspace of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'}))$ of the $\omega$-homogeneous elements, equivalently the $G$-invariant elements, i.e. $\mathrm H^0(G,E)$.

## PDF page 297

**6.2. STRUCTURE THEOREM V: ISOTYPIC EXHAUSTIVENESS** · **297**

The linear operator $N_G$ from Lemma 4.3.3.1 is a linear topological isomorphism $N_{S'}:\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S'}))\to\mathrm H^0(\omega,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'})))$. Similarly, upon replacing $S'$ with $S$, we obtain a linear topological isomorphism $N_S:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H^0(\omega_S,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))$. The operator $N_{S'}\circ\bar\pi_{S,S'}\circ N_S^{-1}$ is the natural inclusion linear map:

$$
p_{S,S'}:\mathrm H^0(\omega_S,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S})))\to\mathrm H^0(\omega,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'})))
$$

given by sending an $\omega_S$-homogeneous element $\phi$ in $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$, to $\bar\pi_{S,S'}(\phi)$, which is $\omega$-homogeneous since $\omega$ is unramified outside $S$. Since $\omega$ is unramified outside $S$, every element of $\mathrm H^0(\omega,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'})))$ is already $\widehat{\mathcal O}^\times_{F,S'-S}$-invariant, and hence contained in $\mathrm H^0(\omega,\bar\pi_{S,S'}(\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'}))))$. Upon showing this, then upon observing that this latter is the range of $p_{S,S'}$ by Theorem 6.1.2.1(1), it follows that $\bar\pi_{S,S'}:\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S'}))$ is surjective.

We now prove that every $\widehat{\mathcal O}^\times_{F,S'-S}$-invariant element of

$$
\mathrm H^0(\omega,\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'})))
$$

is contained in $\mathrm H^0(\omega,\mathrm H^0(\widehat{\mathcal O}^\times_{F,S'-S},\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'}))))$.

Since $\mathrm{Pic}(\mathcal O_{F,S})=1$, we have that the continuous quotient homomorphism:

$$
\mathrm{GL}_1(\mathbf A_{F,S'})/(\mathcal O^\times_{F,S'}\cdot\widehat{\mathcal O}^\times_{F,S'-S})\to J_{F,S}
$$

is an isomorphism, compatible with $S'$-, respectively $S$-idelic norms. It induces a continuous isomorphism of Hausdorff locally compact abelian groups:

$$
J^1_{F,S'}/\widehat{\mathcal O}^\times_{F,S'-S}\to J^1_{F,S}. \tag{6.2.1.1}
$$

Since $\omega$ is a continuous character of $J^1_{F,S'}$, unramified outside $S$, it factors through the quotient homomorphism from (6.2.1.1). We call $\omega_S$ the induced character of $J^1_{F,S}$. The inflation linear map in degree-zero group cohomology:

$$
\mathrm{Inf}:\mathrm H^0(G/H,\mathrm H^0(H,M))\to\mathrm H^0(G,M)
$$

for $G$ an abelian group, $H$ a subgroup of $G$, and $M$ a $G$-module, is an isomorphism, and hence, upon choosing $G=J^1_{F,S'}$, acting through $\omega$, $H=\widehat{\mathcal O}^\times_{F,S'-S}$, and $M=\mathrm H_0(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'}))$, with $G/H$ acting through $\omega_S$, the linear map:

$$
\mathrm{Inf}:\mathrm H^0(\omega_S,\mathrm H^0(\widehat{\mathcal O}^\times_{F,S'-S},\mathrm H_0(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'}))))\to\mathrm H^0(\omega,\mathrm H_0(\mathcal O^\times_{F,S'},\mathcal S(\mathbf A_{F,S'})))
$$

is an isomorphism, which proves the assertion.

(2) : In light of Theorem 5.2.1.1, surjectivity of $\bar\pi_S$ follows from that of $\bar\pi_{S,S'}$ for every $S\subset S'$, proved in (1). $\square$

REMARK 6.2.1.4. We mention a few complements on the spaces $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, and their isotypes.

(1) The $\mathbf C$-linear direct sums:

$$
\bigoplus_{\omega\in\widehat{J^1_{F,S}}}\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))(\omega),\quad\bigoplus_{\omega\in\widehat{C^1_F}}\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))(\omega) \tag{6.2.1.2}
$$

equipped with their locally convex inductive topology, are Hausdorff, locally convex, complete, and inherit the properties of the summand spaces proved in the First Structure Theorem (see Theorem 5.2.3.1). They linearly and continuously inject into $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$, respectively $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, with dense image. The direct sum topology is, however, strictly finer than the subspace topology. To see this, it is enough to produce an example of Schwartz-Bruhat function $f\in\mathcal S(\mathbf A_{F,S_\infty})$ such that $\Phi_{F,S_\infty,\omega}(f)$ is nonvanishing for all $\omega\in\widehat{J^1_{F,S_\infty}}$. Indeed, such example would propagate to all the $S$-local cases and the global case too, through the transition operators $\bar\pi_{S_\infty,S}$ and $\bar\pi_{S_\infty}$, which would produce examples of

## PDF page 298

**298** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

elements in $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and in $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ whose projections into each isotype under everywhere unramified characters (and there is an infinitude of them) are nonvanishing, hence elements that are in $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and in $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$, but not in the direct sum subspaces from (6.2.1.2).

The function $f:=\prod_{v\in S_\infty}f_v$ for $f_v$ the self-dual exponentials from [CF, Ch.XV,pp.316,318], is such an example.

(2) The subspace topology on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ inherited from the product topology from Lemma 5.2.3.2(1), is strictly coarser than the intrinsic topology on $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$. This is due to the fact that the Fourier transform of the restriction of $\Phi_{F,S}(f)(g)$ to $J^1_{F,S}$ is Schwartz on $\widehat{J^1_{F,S}}$, whereas elements of the product spaces from (5.2.3.12) and (5.2.3.13) are meromorphic functions on $\Omega(J_{F,S})$ with no such decay condition along the discrete parameter space $\widehat{J^1_{F,S}}$.

This observation leads to realizing that $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$ and $\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F))$ are not closed in the product spaces from (5.2.2.3), and since they are complete with respect to their intrinsic topology by the First Structure Theorem (Theorem 5.2.1.1), their intrinsic topologies are strictly finer than the subspace topology inherited from the products.

**6.2.2. Computation of the isotypes of $\mathrm H_{0,\mathrm{cont}}(\mathcal O^\times_{F,S},\mathcal S(\mathbf A_{F,S}))$.** We conclude this Chapter by refining Theorem 6.2.1.1(2) to describe the range of $\bar\pi_S$ for large enough $S$ explicitly, in terms of the image under $\Phi_{F,S}$ of Schwartz-Bruhat functions on $\mathbf A_{F,S_\infty}$ extended to Schwartz-Bruhat functions on $\mathbf A_{F,S}$ by tensoring with specific, explicit Schwartz-Bruhat functions on each of the non-Archimedean local fields $F_v$, for each finite place $v\in S$.

This finer analysis will be instrumental to perform calculations in Chapter 6.

THEOREM 6.2.2.1 (Description of the Isotypes by Standard Functions). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$. We write $S_f:=S\cap\Sigma_{F,f}$.*

*Let $\omega\in\widehat{C^1_F}$ be a continuous character. Let $\omega_S\in\widehat{J^1_{F,S}}$ be the unique continuous character obtained by descending $\omega|_{C^1_{F,S}}$ to $J^1_{F,S}$ by $\widehat{\mathcal O}^\times_{\Sigma_F-S}$-invariance.*

*Let:*

*(1) For each finite place $v\in S$ at which $\omega_v\ne 1$, we let $\rho_{v,\omega_S}:=\bar\omega_S\cdot 1_{\mathcal O^\times_{F_v}}$, a Schwartz-Bruhat function in $\mathcal S(F_v)$ supported on $\mathcal O^\times_{F_v}$ and such that $Z_v(\rho_{v,\omega_S},c_v)=\mu_v(\mathcal O^\times_{F_v})$ for $c_v\in\Omega(F^\times_v)(\omega_v)_{>0}$, and $Z_v(\rho_{v,\omega_S},c_v)=0$ otherwise.*

*(2) For each finite place $v\in S$ at which $\omega_v=1$, we define $\rho_{v,\omega_S}:=1_{\mathcal O_{F_v}}$.*

*(3) We define $\rho_{\omega_S}\in\mathcal S(\prod_{v\in S_f}F_v)$ to be $\rho_{\omega_S}:=\bigotimes_{v\in S_f}\rho_{v,\omega_S}$.*

*Then the composition:*

$$
\bar\pi_S\circ\Phi_{F,S,\omega_S}:\mathcal S(\mathbf A_{F,S_\infty})\otimes\rho_{\omega_S}\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_F)) \tag{6.2.2.1}
$$

*is a continuous, surjective, open linear operator.*

*We choose $\chi_S\in\widehat{\mathrm{GL}_1(\mathbf A_{F,S})}$ such that its restriction to $\mathrm{GL}_1(\mathbf A_{F,S})^1$ induces $\omega_S$ on the quotient $J^1_{F,S}$.*

*We choose elements $\{g_1=1,\dots,g_{h_F}\}\subset\mathrm{GL}_1(\mathbf A_{F,S})^1$ representing the finitely many elements of $\mathrm{Pic}(\mathcal O_F)$.*

*We define the linear operators:*

$$
\Psi^\infty_{F,S,\chi_S}:\mathcal S(\mathbf A_{F,S_\infty})\to C(\mathrm{GL}_1(\mathbf A_{F,S_\infty})),\quad\Psi^v_{F,S,\chi_S}:\mathcal S(F^\times_v)\to C(F^\times_v) \tag{6.2.2.2}
$$

*for each $v\in S_f$, by:*

$$
\Psi^\infty_{F,S,\chi_S}(f)(x):=\sum_{1\le k\le h_F}\int_{\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1}f(g_{k,\infty}^{-1}g^{-1}x)\chi_{S,\infty}(g_{k,\infty}g)\,\mathrm d\mu_{S_\infty,1}(g) \tag{6.2.2.3}
$$

## PDF page 299

**6.2. STRUCTURE THEOREM V: ISOTYPIC EXHAUSTIVENESS** · **299**

*where, for each $1\le k\le h_F$, $g_{k,\infty}$ is the projection of $g_k$ onto $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$, and*

$$
\Psi^v_{F,S,\chi_S}(f)(x):=\int_{F^\times_v}f(g^{-1}x)\chi_{S,v}(g)\,\mathrm d\mu_v(g) \tag{6.2.2.4}
$$

*with $\chi_{S,\infty}$ and $\chi_{S,v}$ the restrictions to $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$, respectively $F^\times_v$.*

Then:

(1) *$\ker(\Psi^\infty_{F,S,\chi_S})$ and $\ker(\Psi^v_{F,S,\chi_S})$ are closed subspaces, and the operator from (6.2.2.1) agrees with the unique $\mathbf C$-linear extension of $\Psi^\infty_{F,S,\chi_S}\otimes\bigotimes_{v\in S_f}\Psi^v_{F,S,\chi_S}$ to $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F^\times_v)$, and it induces a linear topological isomorphism:*

$$
(\mathcal S(\mathbf A_{F,S_\infty})/\ker(\Psi^\infty_{F,S,\chi_{S,\infty}}))\otimes\rho_{\omega_S}\to\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S})). \tag{6.2.2.5}
$$

(2) *For any $f\in\mathcal S(\mathbf A_{F,S_\infty})$, $\Psi^\infty_{F,S,\chi_{S,\infty}}(f)$ has semi-exponential decay over $J_{F,S}/J^1_{F,S}$.*

EXAMPLE 6.2.2.2. For $F=\mathbf Q$ and $\omega=1$, Theorem 6.2.2.1 informs us that $\mathrm H_{0,\mathrm{cont}}(1,\mathcal S(\mathbf A_{\mathbf Q}))$ is linearly and topologically a quotient of $\mathcal S(\mathbf R)\otimes 1_{\widehat{\mathbf Z}}$. This is already a consequence of Theorem 6.2.1.1(2).

PROOF. Continuity and linearity of $\bar\pi_S\circ\Phi_{F,S}$ is a consequence of continuity and linearity of the factor operators, and of the linear inclusion $\mathcal S(\mathbf A_{F,S_\infty})\otimes\rho_\omega\subset\mathcal S(\mathbf A_{F,S})$.

By Proposition 2.1.4.1(1), $\mathcal S(\mathbf A_{F,S})$ is linearly and topologically isomorphic to $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F_v)$, with $S_f:=S\cap\Sigma_{F,f}$, and the projective tensor product is already complete (see Proposition 2.1.4.1(1) and (2)). Moreover, $\mathcal S(\mathbf A_{F,S_\infty})$ is nuclear Fréchet by Proposition 2.1.1.6, since $\mathbf A_{F,S_\infty}$ is isomorphic, as a Hausdorff locally compact abelian group, to a finite dimensional real Euclidean space.

The one-dimensional subspace $\mathbf C\cdot\rho_\omega\subset\bigotimes_{v\in S_f}\mathcal S(F_v)$ is linearly and topologically complemented by [NB, Thm.7.3.5] (a consequence of the Hahn-Banach Theorem), or by Proposition C.2.5.1(6), since $\bigotimes_{v\in S_f}\mathcal S(F_v)$ carries the finest locally convex topology.

By [Jar, Part III,Ch.15,§15.2,Prop.3(b),p.327], $\mathcal S(\mathbf A_{F,S_\infty})\otimes\rho_\omega$ is a complemented, hence closed, subspace of $\mathcal S(\mathbf A_{F,S})$, and it is a nuclear Fréchet space since $\mathcal S(\mathbf A_{F,S_\infty})$ is (note that we do not need to use nuclearity of $\mathcal S(\mathbf A_{F,S_\infty})$ to show that the tensor product $\mathcal S(\mathbf A_{F,S_\infty})\otimes\rho_\omega$, as a subspace of $\mathcal S(\mathbf A_{F,S})$, carries the projective tensor product topology, because $\mathbf C\cdot\rho_\omega$ is finite dimensional, and so [Jar, Part III,Ch.15,§15.2,Prop.3(b),p.327] suffices).

By [Gro-f, Ch.4,§5,Thm.2(1),p.148] (see also [SN, §2,Cor.3,p.8]), which applies because both source, by the foregoing, and target, by Theorem 5.2.1.1(2) and Theorem 5.4.1.1(2), are LF-spaces, in order to show openness and surjectivity of the operator in (6.2.2.1), it is enough to show surjectivity.

The operator $\Psi^\infty_{F,S,\chi_S}$ is well defined because the innermost integral converges for all $x\in\mathrm{GL}_1(\mathbf A_{F,S_\infty})$, which is shown by means of an argument closely following that for Lemma 2.2.2.1, since $f$ is of rapid decay at infinity over the real Euclidean space $\mathbf A_{F,S_\infty}$, and $\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1$ is an extension of a compact Hausdorff abelian group by the countable discrete subgroup $\mathcal O^\times_F$, whose action on $\mathbf A_{F,S_\infty}$ by left translation is free and proper, admittiing, by Proposition A.2.4.4 applies to $S=S_\infty$, a fundamental domain with non-empty interior, of the form $\tau(\mathbf R_{>0})\cdot E_{S_\infty,0}$, for $\tau$ a choice of continuous homomorphic section to the $S_\infty$-idelic norm.

Upon endowing $C(\mathrm{GL}_1(\mathbf A_{F,S_\infty}/\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1)$ with the topology of uniform convergence on compact subsets, $\Psi^\infty_{F,S,\chi_S}$ is continuous, by an application of Dominated Convergence, using an analog of the estimate from (2.2.2.3) of Lemma 2.2.2.1 (see also (2.3.1.4) from the proof of Proposition 2.3.1.2), and hence its kernel is closed.

Note that the integral defining $\Psi^v_{F,S,\chi_S}$ is convergent since $K_v$ is compact in $F^\times_v$, the open subgroup $\mathcal O^\times_{F_v}$ is compact Hausdorff, $\pi^{\mathbf Z}_v\subset F^\times_v$ is discrete, and $F^\times_v\simeq\pi^{\mathbf Z}_v\times\mathcal O^\times_{F_v}$ as Hausdorff locally compact abelian groups, for any choice $\pi_v\in F^\times_v$ of uniformizer.

$\mathcal S(F_v)$ carries the finest locally convex topology by Proposition 2.1.2.4(1), and hence $\Psi^v_{F,S,\chi_S}$ is continuous with respect to any complex linear topology on $C(F^\times_v)$ promoting $C(F^\times_v)$ to a topological vector space, so

## PDF page 300

**300** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

long as one exists. Since $F^\times_v$ is Hausdorff locally compact, $C(F^\times_v)$ carries the topology of uniform convergence on compact subsets.

The closed subgroup $\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1\subset\mathrm{GL}_1(\mathbf A_{F,S})^1$ is equipped with the Haar measure $\mu_{S_\infty,1}$, where both $\mu_{S_\infty,1}$ and $\mu_{S,1}$ are induced by the choice of a continuous homomorphic section

$$
\tau:\mathbf R_{>0}\to\mathrm{GL}_1(\mathbf A_{F,S_\infty})\subset\mathrm{GL}_1(\mathbf A_{F,S})
$$

to the $S$-idelic norm whose image is in $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ and is, therefore, also a continuous homomorphic section to the $S_\infty$-idelic norm.

The quotient homomorphism $\mathrm{GL}_1(\mathbf A_{F,S})\to\mathrm{GL}_1(\mathbf A_{F,S})/\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ has a canonical section induced by the isomorphism $\mathrm{GL}_1(\mathbf A_{F,S})\simeq\mathrm{GL}_1(\mathbf A_{F,S_\infty})\times\prod_{v\in S_f}F^\times_v$ which in turn induces an isomorphism:

$$
\mathrm{GL}_1(\mathbf A_{F,S})^1/\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1\simeq\prod_{v\in S_f}F^\times_v \tag{6.2.2.6}
$$

The Haar measure induced as per Theorem D.1.2.1 on $\prod_{v\in S_f}F^\times_v$ by the choices $\mu_{S,1}$ and $\mu_{S_\infty,1}$ made in the foregoing, both induced by $\tau$, is unique, and equals the Haar measure $\bigotimes_{v\in S_f}\mu_v$, where $\mu_v$ is the Tamagawa measure on $F^\times_v$ for each place $v\in S_f$ (see Definition A.3.2.2), by design of the measure $\mu_S$ for each $S$.

The arbitrary $f\in\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F^\times_v)$ is a finite $\mathbf C$-linear combination of Schwarz-Bruhat functions of the form $f_\infty\otimes\bigotimes_{v\in S_f}1_{K_v}$ for $K_v\subset F^\times_v$ a non-empty compact subset.

We assume $f$ is of this form. Such $f$ is, by Proposition 2.1.4.1(1) and since, for each $v\in S_f$, $\mathcal S(F^\times_v)\subset\mathcal S(F_v)$, a Schwartz-Bruhat function on $\mathbf A_{F,S}$.

We denote by $\chi_{S,f}$ the restriction of $\chi_S$ to $\prod_{v\in S_f}F^\times_v\subset\mathrm{GL}_1(\mathbf A_{F,S})$.

We compute:

$$
\Phi_{F,S,\omega_S}(f)(x)=\int_{\mathrm{GL}_1(\mathbf A_{F,S})^1}f(g^{-1}x)\chi_S(g)\,\mathrm d\mu_{S,1}(g) \tag{6.2.2.7}
$$

$$
=\int_{\mathrm{GL}_1(\mathbf A_{F,S})^1/\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1}\int_{\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1}\chi_S(g)f(g_f^{-1}g_\infty^{-1}x)\,\mathrm d\mu_{S_\infty,1}(g_\infty)\,\mathrm d(\bigotimes_{v\in S_f}\mu_v)(g_f). \tag{6.2.2.8}
$$

We now analyze the iterated integral in (6.2.2.7). We observe that each $g\in\mathrm{GL}_1(\mathbf A_{F,S})^1$ can be written uniquely as $g_\infty\cdot\xi_{S-S_\infty}\cdot g_{f,1}\cdot g_k$ for a unique $1\le k\le h_F$, with $g_\infty\in\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1$, $\xi_{S-S_\infty}\in\mathcal O^\times_{F,S}/\mathcal O^\times_F$, a free group of rank $|S|-r_1-r_2+1$ and a direct factor of $\mathcal O^\times_{F,S}$ (we implicitly choose a splitting to the quotient homomorphism $\mathcal O^\times_{F,S}\to\mathcal O^\times_{F,S}/\mathcal O^\times_F$), with $g_{f,1}\in\prod_{v\in S_f}\mathcal O^\times_{F_v}$.

We write $g_k=g_{k,\infty}\cdot g_{k,f}$, with $g_{k,\infty}$ the projection of $g_k$ onto $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ and $g_{k,f}$ the projection of $g_k$ onto $\prod_{v\in S_f}F^\times_v$.

We now use the special form of $f=f_\infty\otimes\bigotimes_{v\in S_f}1_{K_v}$, and rewrite (6.2.2.7) as:

$$
\int_{\prod_{v\in S_f}F^\times_v}\chi_{S,f}(g_f)\bigotimes_{v\in S_f}1_{K_v}(g_v^{-1}x_v)\,\mathrm d(\bigotimes_{v\in S_f}\mu_v(g_v))\cdot\sum_{1\le k\le h_F}\int_{\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1}\chi_{S,\infty}(g_\infty g_{k,\infty})f_\infty(g_\infty^{-1}g_{k,\infty}^{-1}x)\,\mathrm d\mu_{S_\infty,1}(g_\infty) \tag{6.2.2.9}
$$

where $g_f=(g_v)_{v\in S_f}$ (noting that for any $g\in\mathrm{GL}_1(\mathbf A_{F,S})^1$, the image of $g=(g_v)_{v\in S}$, where the $v$-indexed coordinates are obtained by viewing $g$ as an element of $\mathrm{GL}_1(\mathbf A_{F,S})$, into the quotient $\mathrm{GL}_1(\mathbf A_{F,S})^1/\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1$ is sent to $(g_v)_{v\in S_f}$ by the isomorphism from (6.2.2.6)), and $g_f=(\xi_{S-S_\infty})_f\cdot g_{f,1}\cdot g_{k,f}$. We further note that $\bigcup_{1\le k\le h_F}(\mathcal O^\times_{F,S}/\mathcal O^\times_F)_f\cdot\prod_{v\in S_f}\mathcal O^\times_{F_v}\cdot g_{k,f}=\prod_{v\in S_f}F^\times_v$.

We now use the isomorphism $\widehat{\prod_{v\in S_f}F^\times_v}\simeq\prod_{v\in S_f}\widehat{F^\times_v}$ from [DE, Prop.3.6.1] through its Corollary, [DE, Cor.3.6.2], combined with functoriality of the formation of the dual group on Hausdorff locally compact abelian

## PDF page 301

**6.2. STRUCTURE THEOREM V: ISOTYPIC EXHAUSTIVENESS** · **301**

groups, to write $\chi_{S,f}=\bigotimes_{v\in S_f}\chi_v$, where $\chi_v$ is obtained by restricting $\chi_S$ to the $v$-indexed coordinate of $\mathrm{GL}_1(\mathbf A_{F,S})$.

We choose a $g_\infty$ denotes the arbitrary element of $g\in\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1$ and $g_f$ the image in $\prod_{v\in S_f}F^\times_v$ of the arbitrary element of $\mathrm{GL}_1(\mathbf A_{F,S})^1/\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1$ through the isomorphism from (6.2.2.6).

We therefore write (6.2.2.9) as:

$$
\Psi^\infty_{F,S,\chi_S}(f_\infty)(x_\infty)\cdot\prod_{v\in S_f}\Psi^v_{F,S,\chi_S}(1_{K_v})(x_v) \tag{6.2.2.10}
$$

a function of $x=(x_v)_{v\in S}\in\mathrm{GL}_1(\mathbf A_{F,S})$, with $x$ also written as $(x_\infty,(x_v)_{v\in S_f})$ for $x_\infty\in\mathrm{GL}_1(\mathbf A_{F,S_\infty})$.

We now study the operator:

$$
\Psi^v_{F,S,\chi_S}:\mathcal S(F^\times_v)\to C(F^\times_v) \tag{6.2.2.11}
$$

defined in (6.2.2.4).

It is uniquely determined by the assignment $1_{K_v}\mapsto\int_{F^\times_v}\chi_{S,v}(g_v)1_{K_v}(g_v^{-1}x_v)\,\mathrm d\mu_v(g_v)$ as a function of $x_v\in F^\times_v$, for any non-empty compact open subset $K_v\subset F^\times_v$.

The function $\bar\chi_v\cdot\Psi_{F,S,\chi_v}(1_{K_v})$ is constant over $F^\times_v$. We denote by $c_v(1_{K_v})$ its value. We then have $\Psi_{F,S,\chi_v}(1_{K_v})=\chi_v\cdot c_v(1_{K_v})$.

Since formation of $c_v$ is $\mathbf C$-linear, we deduce that the operator $\chi_v\cdot\Psi_{F,S,\chi_v}$ is a continuous linear functional on $\mathcal S(F^\times_v)$.

It is nonzero, since for $K_v=\mathcal O^\times_{F_v}$ and $f_v:=\bar\chi_v\cdot 1_{K_v}\in\mathcal S(F^\times_v)$, we have $\Psi_{F,S,\chi_v}(f_v)=\mu_v(\mathcal O^\times_{F_v})\ne 0$.

It follows that $\bar\chi_{S,f}\cdot\bigotimes_{v\in S_f}\Psi_{F,S,\chi_v}$ is a continuous linear functional on $\bigotimes_{v\in S_f}\mathcal S(F^\times_v)\simeq\mathcal S(\prod_{v\in S_f}F^\times_v)$, and it is nonzero, since it is nonzero on the function $\rho'_{\omega_S}:=\bigotimes_{v\in S_f}\rho'_v$ where $\rho'_v=\bar\chi_v\cdot 1_{\mathcal O^\times_{F_v}}$ for each $v\in S_f$.

We have proved that $\Phi_{F,S,\omega_S}$ agrees on $\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F^\times_v)\subset\mathcal S(\mathbf A_{F,S})$, with $\Psi_{F,S,\chi_S}=\Psi^\infty_{F,S,\chi_S}\otimes\bigotimes_{v\in S_f}\Psi^v_{F,S,\chi_S}$.

Since, by Lemma 5.3.1.1, $\mathcal S(F^\times_v)=P_v\mathcal S(F_v)$, it follows that $\Phi_{F,S,\omega_S}$ maps $\mathcal S(\mathbf A_{F,S_\infty})\otimes\mathrm{PV}_{S,S_f}(\rho_{\omega_S})$ onto $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))$, since, by Lemma 5.3.1.3, $\rho'_{\omega_S}=\mathrm{PV}_{S,S_f}(\rho_{\omega_S})$, where $\mathrm{PV}_{S,S_f}$ is Weil's Principal Value Operator from Definition 5.3.1.2 and Definition 5.3.1.4 (see also Lemma 5.3.1.3).

It follows that $\mathrm{PV}_{S,S_f}\circ\Phi_{F,S,\omega_S}$ maps $\mathcal S(\mathbf A_{F,S_\infty})\otimes\rho_{\omega_S}$ onto

$$
\mathrm{PV}_{S,S_f}\Phi_{F,S,\omega_S}(\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}E_v)
$$

where $E_v=\mathcal S(F_v)$ if $\chi_S$, equivalently $\omega_S$, equivalently $\omega$, is unramified at $v\in S_f$, and $E_v=\mathcal S(F^\times_v)$ otherwise.

This proves that $\Phi_{F,S,\omega_S}$ maps $\mathcal S(\mathbf A_{F,S_\infty})\otimes\rho_{\omega_S}$ surjectively onto $\Phi_{F,S,\omega_S}(\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}E_v)$.

In order to show that we have

$$
\Phi_{F,S,\omega_S}(\mathcal S(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}E_v)=\mathrm H_{0,\mathrm{cont}}(\omega_S,\mathcal S(\mathbf A_{F,S}))
$$

it is enough to show that for every Schwartz-Bruhat function $f\in\mathcal S(F_v)$ where $v\in S_f$ is a place at which $\chi_S$ is ramified, then upon calling $\chi_v$ the restriction of $\chi_S$ to $F^\times_v$, there exists a Schwartz-Bruhat function $f_0\in\mathcal S(F_v)$ which vanishes on a compact open neighborhood of $0\in F_v$, and such that $Z_v(f_0,\chi_v|\cdot|^s_v)=Z_v(f,\chi_v|\cdot|^s_v)$ as meromorphic (in fact entire) functions of $s\in\mathbf C$.

To see this, we note that since $f$ is Schwartz-Bruhat over $F_v$, it is locally constant and compactly supported over $F_v$. For any choice $\pi_v\in F^\times_v$ of uniformizer, there exists a large enough integer $N\ge 0$ such that $f$ is constant over $\pi^N_v\mathcal O_{F_v}$. Let $A$ be its value over $\pi^N_v\mathcal O_{F_v}$.

We define $f_0:=f-A\cdot 1_{\pi^N_v\mathcal O_{F_v}}$, and note that $f_0$ is indeed a Schwartz-Bruhat function over $F_v$ supported away from a compact open neighborhood of $0\in F_v$.

## PDF page 302

**302** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

We have $Z_v(f_0, \chi_v|\cdot|^s_v) = Z_v(f, \chi_v|\cdot|^s_v) - A\cdot Z_v(1_{\pi^N_v\mathcal O_{F_v}}, \chi_v|\cdot|^s_v)$ as holomorphic functions on the complex $s$-plane.

We now note that $\pi^N_v\mathcal O_{F_v}$ is a $\mathcal O^\times_{F_v}$-invariant compact open neighborhood of $0\in F_v$, and hence $1_{\pi^N_v\mathcal O_{F_v}}$ is a $\mathcal O^\times_{F_v}$-invariant function. It follows, since $\chi_v|_{\mathcal O^\times_{F_v}}$ is non-trivial, that we have $Z_v(1_{\pi^N_v\mathcal O_{F_v}}, \chi_v|\cdot|^s_v) = 0$.

The calculation from (6.2.2.7) also shows that the induced operator from (6.2.2.5) is a continuous linear bijection, and since both source and target are Fréchet spaces, since $\mathcal S(\mathbf A_{F,S_\infty})/\ker(\Psi^\infty_{F,S,\chi_S})$ is a separated quotient of $\mathcal S(\mathbf A_{F,S_\infty})$ by continuity of $\Psi^\infty_{F,S,\chi_S}$ and $\mathcal S(\mathbf A_{F,S_\infty})$ is a Fréchet space by Proposition 2.1.1.6, and $\mathrm H_{0,\mathrm{cont}}(\omega_S, \mathcal S(\mathbf A_{F,S}))$ is a Fréchet space by Theorem 5.4.1.1(2).

By [NB, Thm.14.4.5], it is a linear topological isomorphism. This proves all the assertions of the Theorem, with the exception of (2).

(2) : We proceed as for the proof of (2.4.2.1) from Theorem 2.4.2.1.

It is enough to replace

$$
\int_{\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1} f(g^{-1}_{k,\infty}g^{-1}x)\chi_{S,\infty}(g_{k,\infty}g)\,\mathrm{d}\mu_{S_\infty,1}(g)
$$

with

$$
\int_{\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1} |f(g^{-1}_{k,\infty}g^{-1}x)|\,\mathrm{d}\mu_{S_\infty,1}(g)
$$

and since $\mathrm{GL}_1(\mathbf A_{F,S_\infty})^1/\mathcal O^\times_F$ is compact Hausdorff and $f(g^{-1}_{k,\infty}g^{-1}x)$, for each $1\le k\le h_F$, decays faster than any positive power of $|x|^{-1}_{S_\infty}$ as $|x|_{S_\infty}\to +\infty$ uniformly as $g\in E_{S_\infty,0}$, we may replace $|f|$ with the indicator function of

$$
\{x\in\mathbf A_{F,S_\infty}\colon |x|_v\in [-A,A]\ \text{for all}\ v\in S_\infty\}
$$

for large enough fixed $A > 0$. By Theorem A.4.1.1, we deduce that there exists a real number $C > 0$ such that, as $|g|_{S_\infty}\to 0^+$, we have:

$$
|\Psi^\infty_{F,S,\chi_{S,\infty}}(f)(g)|\le C|\log|g|_{F,S_\infty}|^{r_1+r_2-1}. \tag{6.2.2.12}
$$

The estimate in (6.2.2.12) and the rapid decay of $f$ over $\mathbf A_{F,S_\infty}$ imply that $\Psi^\infty_{F,S,\chi_{S,\infty}}(f)$ is of semi-exponential decay over $J_{F,S}/J^1_{F,S}$.

$\square$

**6.3. Local and Global Converse Theorems**

In this section, we describe the isotypes of $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$ in terms of ideals of meromorphic functions on the Riemann surface $\Omega(C_F)$.

The main Theorem in this section describes the image of the Mellin transform $L$ from (5.2.3.14) on $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$ and can be viewed as an incarnation of the Converse Theorem for $\mathrm{GL}_1$ (as per [CPS, Thm.1,p.165]).

**6.3.1. Recollections on the Euler factors of Hecke $L$-functions.** Let $F$ be a number field.

We fix a holomorphic parametrization:

$$
\chi|\cdot|^s_F,\ s\in\mathbf C \tag{6.3.1.1}
$$

which will be in force throughout the entirety of this Chapter.

We will be denoting the global holomorphic coordinate $s$ by $z$ when the letter $s$ is otherwise required: the choice of holomorphic parametrization will, however, be understood to remain the same as in (6.3.1.1).

Recall that this means choosing, for each continuous character $\omega\in \widehat{C^1_F}$, a lift $\chi\in \widehat{C_F}$, i.e. a continuous character $\chi\in \widehat{C_F}$ such that $\omega = \chi|_{C^1_F}$.

We then use $\chi$ as base-point for the unique connected component of $\Omega(C_F)$ parametrized by $\omega$, and parametrize the connected component $\Omega(C_F)(\omega)$ by the global holomorphic chart $\chi|\cdot|^s_F,\ s\in\mathbf C$.

## PDF page 303

**6.3. LOCAL AND GLOBAL CONVERSE THEOREMS** · **303**

We denoted, in (3.2.1.2), by $L(s,\chi)$ the completed Hecke $L$-function associated to $\chi$, i.e. $L(\chi|\cdot|^s_F)$ (see (3.2.1.2) from Lemma 3.2.1.1).

The Euler factors of $L(\chi|\cdot|^s_F)$ are, therefore, by Lemma 3.2.1.1, the following.

There exists, for each finite place $v$ of $F$ at which $\chi$ is unramified, a real number $t_v$, such that:

$$
(\chi|\cdot|^s_F)_v = \chi_v|\cdot|^s_v = |\cdot|^{s+it_v}_v. \tag{6.3.1.2}
$$

We have:

$$
t_v = i\,\frac{\log\chi_v}{\log(q_v)} \tag{6.3.1.3}
$$

where $q_v := N(\mathfrak p_v)$, with $\mathfrak p_v$ the unique prime ideal of $\mathcal O_F$ associated to $v$, noting that, for any chosen branch of the logarithm, $\log\chi_v$ is a purely imaginary number.

$t_v$ is unique modulo the additive translation action of the discrete group $(2\pi/\log(q_v))\mathbf Z$ on $\mathbf R$.

In particular, we may find a unique such $t_v$ satisfying $t_v\in [0,2\pi/\log(q_v))$.

Throughout this Chapter, the real number $t_v$ will always be chosen as in the foregoing, so as to arrange for the identities in (6.3.1.2) to hold.

If $v$ is Archimedean, then if $v$ is real, $\chi_v|\cdot|^s_v = |\cdot|^{s+it_v}_v$ if $\chi_v$ is even, for a unique real number $t_v$, and $\chi_v|\cdot|^s_v = \mathrm{sgn}\,|\cdot|^{s+it_v}_v$ if $\chi_v$ is odd, for a unique real number $t_v$.

If $v$ is complex, then $\chi_v|\cdot|^s_v = \chi_{n,s}|\cdot|^{it_v}_v$ for a unique real number $t_v$, and for the unique integer $n\in\mathbf Z$ such that $\chi_v|\cdot|^{it_v}_v(e^{i\theta}) = e^{in\theta}$ for every $\theta\in\mathbf R$.

We deduce that the Euler factor at $v$, for $v$ a place of $F$, of the Hecke $L$-function $L(c) = L(\chi|\cdot|^s_F)$, is, on the holomorphic parametrization of $\Omega(C_F)$ selected in (6.3.1.1):

$$
L_v(c_v) = L_v(\chi_v|\cdot|^s_v) = \frac{1}{1-q^{-s-it_v}_v} \tag{6.3.1.4}
$$

if $v$ is non-Archimedean and $\chi$ is unramified at $v$, it is $L_v(c_v) = 1$ if $v$ is non-Archimedean and $\chi$ is ramified at $v$, and it is given by (3.2.1.4) and (3.2.1.5) if $v$ is Archimedean, for $v$ real, respectively $v$ complex.

Terminology 6.3.1.1 ($S$-local Hecke $L$-functions). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\chi\in \widehat{C_F}$ be a continuous character. Assume $\mathrm{Pic}(\mathcal O_{F,S}) = 1$ and $\chi$ is unramified outside $S$.

We define $\chi_S$ to be the unique continuous character of $J_{F,S}$ obtained by descending the restriction of $\chi$ to $C_{F,S}$ by $\widehat{\mathcal O}^\times_{\Sigma_F-S}$-invariance.

We define:

$$
L_S(\chi_S,s) := \prod_{v\in S} L_v(\chi_v|\cdot|^s_v) \tag{6.3.1.5}
$$

a meromorphic function on the complex $s$-plane whose poles are located at the poles of $\rho_S(\chi|\cdot|^s_{F,S})$ (see (3.3.1.3)), with matching orders of poles.

We refer to $L_S(\chi_S,s)$ as the $S$-local Hecke $L$-function.

We further define:

$$
L_{\Sigma_F-S}(\chi,s) := L_S(\chi_S,s)^{-1}L(s,\chi). \tag{6.3.1.6}
$$

**6.3.2. Converse Theorems.** Recall from (2.2.4.23) and (5.5.2.1) that we have defined:

$$
\mathcal S_0(\mathbf A_F) := \ker(\delta_0)\cap\ker(\widehat{\delta}_0) \tag{6.3.2.1}
$$

where $\delta_0\colon \mathcal S(\mathbf A_F)\to\mathbf C$ is the strongly continuous functional $\delta_0(f) := f(0)$, and $\widehat{\delta}_0$ is its adelic Fourier transform, i.e. $\widehat{\delta}_0(f) := \widehat{f}(0)$.

## PDF page 304

**304** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

We endow $\mathcal S_0(\mathbf A_F)$ with the subspace topology, promoting it to a closed subspace of $\mathcal S(\mathbf A_F)$, being $\delta_0$ and $\widehat{\delta}_0$ continuous functionals on $\mathcal S(\mathbf A_F)$.

From Lemma 5.5.2.1, we know hat the continuous functionals $\delta_0, \widehat{\delta}_0\in\mathcal S(\mathbf A_F)'_\beta$ descend uniquely to continuous functionals on $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$. They are homogeneous with respect to the adjoint of the continuous left-translation action of $C_F$ on $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$ and satisfy:

$$
\rho'_F(g,\delta_0) = \delta_0,\quad \rho'_F(g,\widehat{\delta}_0) = |g|_F\,\widehat{\delta}_0 \tag{6.3.2.2}
$$

for all $g\in C_F$, i.e. $\delta_0$ is a global eigendistribution of weight $c = 1$, and $\widehat{\delta}_0$ is a global eigendistribution of weight $c = |\cdot|_F$. Moreover, for every $\omega\in \widehat{C^1_F}$, both $\delta$ and $\widehat{\delta}_0$ vanish on $\mathrm H_{0,\mathrm{cont}}(\omega, \mathcal S(\mathbf A_F))$ if and only if $\omega\ne 1$.

In the language of Theorem 5.5.1.3 (see (5.5.2.3)), we have

$$
\delta_0 = \Delta_F(1),\quad \widehat{\delta}_0 = \Delta_F(|\cdot|_F).
$$

Theorem 6.3.2.1 (Global Converse Theorem). *Let $F$ be a number field, $\chi\in \widehat{C_F}$ a continuous character. Let $A\mathcal S(\mathbf C)$ be the Schwartz-Bergman space as per Definition D.3.1.3. We parametrize $\Omega(C_F)(\chi|_{C^1_F})$ by the global holomorphic parametrization*

$$
\chi|\cdot|^s_F,\ s\in\mathbf C.
$$

(1) *If $\chi|_{C^1_F}\ne 1$, then the continuous linear map:*

$$
Z\colon \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))\to A\mathcal S(\mathbf C) \tag{6.3.2.3}
$$

*is a linear topological embedding with closed range. equal to $L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)\subset A\mathcal S(\mathbf C)$. If $\chi|_{C^1_F} = 1$, then the continuous linear map:*

$$
Z\circ\Phi_{F,1}\colon \mathcal S_0(\mathbf A_F)\to A\mathcal S(\mathbf C) \tag{6.3.2.4}
$$

*is relatively open with closed range, equal to $((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)$, with $\delta_{\chi|_{C^1_F}} = 0$ if $\chi|_{C^1_F}\ne 1$, and kernel equal to $\ker(\Phi_{F,1})\cap\mathcal S_0(\mathbf A_F)$.*

(2) *The following sequence of $\mathbf C$-linear operators:*

$$
0\to\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))\to\mathbf C^{\oplus 2}\to 0 \tag{6.3.2.5}
$$

where:

(1) *$\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ is the quotient of $\mathcal S_0(\mathbf A_F)$ by $\ker(\Phi_F)\cap\mathcal S_0(\mathbf A_F)$, endowed with the quotient topology.*

(2) *$\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ is the quotient of $\mathcal S_0(\mathbf A_F)$ by $\ker(\Phi_{F,\chi|_{C^1_F}})\cap\mathcal S_0(\mathbf A_F)$, endowed with the quotient topology.*

(3) *The rightmost operator sends $\Phi_{F,\chi|_{C^1_F}}(f)$ to the pair of complex numbers:*

$$
-\overline{\mu}_1(C^1_F)\,f(0)\,\delta_{\chi|_{C^1_F}},\quad \overline{\mu}_1(C^1_F)\,\widehat{f}(0)\,\delta_{\chi|_{C^1_F}} \tag{6.3.2.6}
$$

*is strict exact, and under the Mellin transform $\phi\mapsto M(\phi)(s) := \int_{C_F}\phi(g)\chi(g)|g|^s_F\,\mathrm{d}\overline{\mu}(g)$ it is linearly and topologically isomorphic to the short exact sequence:*

$$
0\to L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)\to L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)\to 0 \tag{6.3.2.7}
$$

*if $\chi|_{C^1_F}\ne 1$, the middle operator in (6.3.2.7) being the identity, and the topology on $L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)$ being the subspace topology inherited from $A\mathcal S(\mathbf C)$, and to the short exact sequence:*

$$
0\to (s-it_0)(1-s-it_0)\,\widehat{\zeta}_F(s+it_0)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)\to\widehat{\zeta}_F(s+it_0)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)\to\mathbf C\oplus\mathbf C\to 0 \tag{6.3.2.8}
$$

*for a real number $t_0\in\mathbf R$ uniquely determined by $\chi$, where the rightmost operator sends an element of $\widehat{\zeta}_F(s+it_0)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)$ to the pair of residues at $s = -it_0, 1-it_0$, the topology on the leftmost space of meromorphic functions from (6.3.2.8) being the subspace topology inherited from $A\mathcal S(\mathbf C)$, and the*

## PDF page 305

**6.3. LOCAL AND GLOBAL CONVERSE THEOREMS** · **305**

*topology on the middle space of meromorphic functions being the quotient topology induced by $L$ from $\mathrm H_{0,\mathrm{cont}}(|\cdot|^{it_0}_F, \mathcal S(\mathbf A_F))$.*

Proof. We will use the First Structure Theorem (see Theorem 5.2.3.1), and specifically the assertion that the continuous linear operator $\overline{\pi}$ from (5.2.3.2), induced by the insertion operators:

$$
\overline{\pi}_S\colon \mathrm H_{0,\mathrm{cont}}((\chi|_{C^1_F})_S, \mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F)) \tag{6.3.2.9}
$$

for $S$ any finite set of places of $F$ containing all the Archimedean places, such that $\chi$ is unramified away from $S$, and with $(\chi|_{C^1_F})_S$ the character of $J^1_{F,S}$ obtained by restricting $\chi$ to $C^1_{F,S}$ and descending it to the quotient $J^1_{F,S}$, is a linear topological embedding.

By the Fifth Structure Theorem (see Theorem 6.2.1.1(2)), for all finite sets of places $S$ of $F$ containing all the Archimedean places, such that $\mathrm{Pic}(\mathcal O_{F,S}) = 1$ and $\chi$ is unramified outside $S$, the linear topological embedding $\overline{\pi}_S$ from (6.3.2.9) is itself a linear topological isomorphism.

We choose $S$ so large as to have $\mathrm{Pic}(\mathcal O_{F,S}) = 1$, and $\chi$ unramified outside $S$.

We choose a continuous homomorphic section $\tau$ to the idelic norm $|\cdot|_F$, and define $\tau_S$ to be the induced continuous homomorphic section to the restriction to $C_{F,S}$ of the idelic norm (noting that the continuous open group homomorphism $C_{F,S}\to C_F$ is an isomorphism for this choice of $S$), descended to $J_{F,S}$ by composition with the quotient homomorphism $C_{F,S}\to J_{F,S}$.

The continuous linear operator

$$
U_{S,\tau_S,(\chi|_{C^1_F})_S}\colon \mathrm H_{0,\mathrm{cont}}((\chi|_{C^1_F})_S, \mathcal S(\mathbf A_{F,S}))\to A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1}) \tag{6.3.2.10}
$$

defined in (5.4.1.2) by $U_{S,\tau_S,(\chi|_{C^1_F})_S}(f) := (Z_S(f,\chi|\cdot|^s_{F,S}), Z_S(\widehat{f},\overline{\chi}|\cdot|^{1-s}_{F,S}))$ is, by the Second Structure Theorem (see Theorem 5.4.1.1(1)), a linear topological embedding. Its range is closed, since the source is complete by the First Structure Theorem (see Theorem 5.2.3.1(2)).

We will abbreviate the notation and write:

$$
U_{S,\chi} := U_{S,\tau_S,(\chi|_{C^1_F})_S}.
$$

We now consider the linear map:

$$
T_{S,\chi}\colon A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1}) \xrightarrow{(\times(1-s-it_0)^{\delta_\chi}L_{\Sigma_F-S}(\chi,s),\,\times(s+it_0)^{\delta_\chi}L_{\Sigma_F-S}(\overline{\chi},1-s))} A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1}) \tag{6.3.2.11}
$$

with $\delta_\chi = 0$ if $\chi|_{C^1_F}\ne 1$, and $\delta_\chi = 1$ if $\chi|_{C^1_F} = 1$, and with $t_0\in\mathbf R$ uniquely determined by $\chi$ and $\tau$ (i.e. $t_0\in\mathbf R$ is the unique real number such that $\chi(\tau(t)) = t^{it_0}$ as smooth functions of $t\in\mathbf R_{>0}$) such that $s = 1-it_0$ is the unique simple pole of $L_{\Sigma_F-S}(\chi,s)$ (if any) contained in $\mathbf C_{>0}$, sending a pair $(\phi,\psi)$ of holomorphic functions on $\mathbf C_{>0}$, respectively $\mathbf C_{<1}$, each Schwartz uniformly on the vertical strips of bounded width of $\mathbf C_{>0}$, respectively $\mathbf C_{<1}$, to the pair $((1-s-it_0)^{\delta_\chi}L_{\Sigma_F-S}(\chi,s)\phi(s), (s+it_0)^{\delta_\chi}L_{\Sigma_F-S}(\overline{\chi},1-s)\psi(s))$, where

$$
L_{\Sigma_F-S}(\chi,s) := \prod_{v\in S}(L_v(\chi_v,s))^{-1}L(s,\chi)
$$

is defined in (6.3.1.6) of Terminology 6.3.1.1.

$T_{S,\chi}$ is indeed valued in $A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$ and continuous, since $(1-s-it_0)^{\delta_\chi}L_{\Sigma_F-S}(\chi,s)$ is holomorphic over $\mathbf C_{>0}-\{1-it_0\}$, and with at most a removable singularity at $s = 1-it_0$ (see Proposition 3.2.1.3), and it grows at most polynomially, uniformly on the vertical strips of bounded width of $\mathbf C_{>0}$, as do its derivatives (see Remark B.1.1.4).

The kernel of the composition $T_{S,\chi}\circ U_{S,\chi}$ is trivial if $\chi|_{C^1_F}\ne 1$, and it is trivial when restricted to the subspace

$$
\mathrm H_{0,\mathrm{cont}}((\chi|_{C^1_F})_S, \mathcal S(\mathbf A_{F,S}))\cap\ker(\Delta_F(1)\circ\overline{\pi}_S)\cap\ker(\Delta_F(|\cdot|_F)\circ\overline{\pi}_S) \tag{6.3.2.12}
$$

## PDF page 306

**306** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

if $\chi|_{C^1_F} = 1$. This subspace of $\mathrm H_{0,\mathrm{cont}}((\chi|_{C^1_F})_S, \mathcal S(\mathbf A_{F,S}))$ is linearly and topologically isomorphic to $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ under $\overline{\pi}_S$.

To study the range of $L$ from (6.3.2.3) and (6.3.2.4), we first study the range of $T_{S,\chi}\circ U_{S,\chi}$ within $A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$.

We define the continuous linear map:

$$
R_{S,\chi}\colon A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1}) \xrightarrow{(\phi,\psi)\mapsto(\phi(s)-\psi(s))|_{\mathbf C_{(0,1)}}} A\mathcal S(\mathbf C_{(0,1)}) \tag{6.3.2.13}
$$

and observe that by the $S$-local functional equation (see (3.3.1.2) of Theorem 3.3.1.1) and the global functional equation (see (3.2.2.2) of Theorem 3.2.2.1), $T_{S,\chi}\circ U_{S,\chi}$ is valued in the kernel of $R_{S,\chi}$.

The operator $T_{S,\chi}$ is sequentially closed. Indeed, for $\{(\phi_m,\psi_m)\}_{m\ge 0}\subset A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$ a sequence such that $\{T_{S,\chi}(\phi_m,\psi_m)\}_{m\ge 0}\subset A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$ is a Cauchy sequence with limit $(\widetilde{\phi},\widetilde{\psi})\in A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$, the convergence of $(1-s-it_0)^{\delta_\chi}L_{\Sigma_F-S}(\chi,s)\phi_m(s)$ to $\widetilde{\phi}(s)$ and of $(s+it_0)^{\delta_\chi}L_{\Sigma_F-S}(\overline{\chi},1-s)\psi_m(s)$ to $\widetilde{\psi}_m(s)$ is uniform over the vertical strips of bounded width within $\mathbf C_{>0}$, respectively within $\mathbf C_{<1}$, by the polynomial growth of $(1-s-it_0)^{\delta_\chi}L_{\Sigma_F-S}(\chi,s)$ and $(s+it_0)^{\delta_\chi}L_{\Sigma_F-S}(\overline{\chi},1-s)$ and their derivatives of any order, uniformly on the vertical strips of bounded width within $\mathbf C_{>0}$, respectively $\mathbf C_{<1}$.

In particular, $\widetilde{\phi}(s)$ is divisible by $(1-s-it_0)^{\delta_\chi}L_{\Sigma_F-S}(\chi,s)$ and $\widetilde{\psi}(s)$ is divisible by $(s+it_0)^{\delta_\chi}L_{\Sigma_F-S}(\overline{\chi},1-s)$ as meromorphic functions over $\mathbf C_{<1}$, i.e. there exist meromorphic functions $\widetilde{\phi}_0$ and $\widetilde{\psi}_0$ over $\mathbf C_{>0}$, respectively $\mathbf C_{<1}$, holomorphic away from the zeros of $(1-s-it_0)^{\delta_\chi}L_{\Sigma_F-S}(\chi,s)$, respectively $(s+it_0)^{\delta_\chi}L_S(\widetilde{\chi},1-s)$, such that $\widetilde{\phi}(s) = (1-s-it_0)^{\delta_\chi}L_{\Sigma_F-S}(\chi,s)\widetilde{\phi}_0(s)$ over $\mathbf C_{>0}$, and $\widetilde{\psi}(s) = (s+it_0)^{\delta_\chi}L_{\Sigma_F-S}(\overline{\chi},1-s)\widetilde{\psi}_0(s)$ over $\mathbf C_{<0}$.

We now prove that in fact both $\widetilde{\phi}_0(s)$ and $\widetilde{\psi}_0(s)$ are holomorphic. To this end, we use the Asymptotic Residue Theorem (see Theorem B.3.2.1), and the polynomial growth of the reciprocal of $L_{\Sigma_F-S}(\chi,s)$ and its derivatives, on a sequence of horizontal segments with growing absolute ordinates, of a vertical strip of the form $\mathbf C_{[-\varepsilon,1+\varepsilon]}$ for any $0<\varepsilon<1$ (see Corollary B.6.1.8).

Since the growth of $L_{\Sigma_F-S}(\chi,s)$, respectively $L_{\Sigma_F-S}(\overline{\chi},1-s)$, together with their holomorphic derivatives of any order, is at most polynomial uniformly over the vertical strips of bounded width of $\mathbf C_{>0}$, respectively $\mathbf C_{<1}$, then $\widetilde{\phi}_0(s)$ and $\widetilde{\psi}_0(s)$ are again elements of $A\mathcal S(\mathbf C_{>0})$, respectively $A\mathcal S(\mathbf C_{<1})$, as a consequence of the Asymptotic Residue Theorem (see Theorem B.3.2.1) and Lemma D.3.1.1.

We have shown that we have:

$$
\lim_{m\to +\infty}T_{S,\chi}(\phi_m,\psi_m) = T_{S,\chi}(\widetilde{\phi}_0,\widetilde{\psi}_0)
$$

in $A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$, which shows that the range of $T_{S,\chi}$ is sequentially closed.

Since $A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$ is a Fréchet space by Lemma D.3.1.2, the range of $T_{S,\chi}$ is closed, and being $T_{S,\chi}$ injective and continuous, it is a linear topological isomorphism onto its image.

Since $R_{S,\chi}$ is continuous, its kernel is closed in $A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$, and hence the range of $T_{S,\chi}\circ U_{S,\chi}$ is closed in the kernel of $R_{S,\chi}$.

We will now analyze the kernel of $R_{S,\chi}$ as a subspace of $A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$.

We define the linear map:

$$
A\colon A\mathcal S(\mathbf C)\to A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})
$$

assigned by sending $\phi\in A\mathcal S(\mathbf C)$ to $(\phi(s),\phi(s))\in A\mathcal S(\mathbf C_{>0})\times A\mathcal S(\mathbf C_{<1})$.

$A$ is continuous, injective, and with closed range since $A\mathcal S(\mathbf C_{>0})$ and $A\mathcal S(\mathbf C_{<1})$ are Hausdorff. It is therefore a linear topological embedding, and its range contains the kernel of $R_{S,\chi}$ (in fact, it agrees with the kernel of $R_{S,\chi}$). It follows that $T_{S,\chi}\circ U_{S,\chi}$ factors through $A$ linearly and topologically, inducing a unique continuous linear operator from $\mathrm H_{0,\mathrm{cont}}((\chi|_{C^1_F})_S, \mathcal S(\mathbf A_{F,S}))$, if $\chi|_{C^1_F}\ne 1$, and from the subspace of $\mathrm H_{0,\mathrm{cont}}((\chi|_{C^1_F})_S, \mathcal S(\mathbf A_{F,S}))$ from (6.3.2.12) if $\chi|_{C^1_F} = 1$, to $A\mathcal S(\mathbf C)$: such operator is $L\circ\overline{\pi}_S$.

## PDF page 307

**6.3. LOCAL AND GLOBAL CONVERSE THEOREMS** · **307**

Since $\overline{\pi}_S$ is a linear topological isomorphism onto $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))$ if $\chi|_{C^1_F}\ne 1$, and onto $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ if $\chi|_{C^1_F} = 1$, we have shown that $L$ is valued in $A\mathcal S(\mathbf C)$ and it is continuous, injective and with closed range. In particular, it is a linear topological embedding, hence relatively open.

To conclude the proof of (1), we are to identify the range explicitly within $A\mathcal S(\mathbf C)$. In order to do this, it is enough to compute the range of $L\circ\overline{\pi}_S$, for the choice of $S$ made at the outset.

Let $f\in\mathcal S(\mathbf A_{F,S})$ be given. Then $Z(\pi_S(f),\chi|\cdot|^s_F) = Z_S(f,\chi_S|\cdot|^s_{F,S})L_{\Sigma_F-S}(\chi,s)$, where $\chi_S$ is the unique character of $J_{F,S}$ obtained by descending to $J_{F,S}$ the restriction of $\chi$ to $C_{F,S}$, being $\chi$ unramified outside $S$.

By combining Theorem 6.2.1.1 with its refinement, Theorem 6.2.2.1, the range of $L$ is linearly generated by all entire functions $\phi$ on the complex $s$-plane satisfying the following three conditions:

(1) There exists $f_\infty\in\mathcal S(\mathbf A_{F,S_\infty})$ such that $\phi$ is of the following form:

$$
\phi(s) = \psi(s)((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L_f(s,\chi) \tag{6.3.2.14}
$$

for $\psi\in\mathscr{O}(\mathbf C)$ of the following form:

$$
\psi(s) = \int_{\mathbf R_{>0}} t^{s+it_0}\,\Psi^\infty_{F,S,\omega_S}(f_\infty)(\tau(t))\,\frac{\mathrm{d}t}{t} \tag{6.3.2.15}
$$

where $\Psi^\infty_{F,S,\omega_S}$ is the linear operator defined in (6.2.2.2) of the Theorem, for $\omega_S := (\chi_S)|_{J^1_{F,S}}$).

(2) $\phi$ is an element of $A\mathcal S(\mathbf C)$.

(3) $\phi$ has zeros at the zeros of $L_f(s,\chi)$ contained in $\mathbf C_{>0}$, with matching multiplicities.

Note that by Theorem 6.2.2.1, the $\mathbf C$-linear subspace of finite linear combinations of entire functions of the form described in (1), (2) and (3), agrees with the range of $L$ in $A\mathcal S(\mathbf C)$, and it is not merely dense in it. This is a consequence of each $\mathcal S(F_v)$ carrying the finest locally convex topology, rendering the algebraic tensor products in Proposition 2.1.4.1 and Theorem 6.2.2.1 topologized with the projective tensor product topology, already complete.

Note also that since we restrict the source of $L$ to the closed co-dimension 2 subspace $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ of $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$, and formation of this closed subspace is compatible with $\overline{\pi}_S$, i.e. $\overline{\pi}_S$ for every $S$ sends $\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$ linearly and topologically isomorphically onto $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$, for $\mathcal S_0(\mathbf A_{F,S}) := \ker(\delta_0)\cap\ker(\widehat{\delta}_0)$ (the Fourier transform being the $S$-adelic Fourier transform, defined using the standard additive character), we can choose $f_\infty$ to satisfy these two vanishing conditions in $\mathcal S(\mathbf A_{F,S_\infty})$, in the sole case they are necessary (i.e. $\chi = 1$).

The meromorphic function $\psi(s)$ therefore has only removable singularities over $\mathbf C_{>0}$, because the integral defining $\psi$ in (6.3.2.15) is absolutely and locally uniformly convergent for $s\in\mathbf C_{>0}$ (by an analog of the estimate from Theorem 2.4.2.1 leading to Corollary 2.4.3.2, the only difference being that the character of $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ being used to define the $\theta$-function operator $\Psi_{F,S,\omega_S}$ is not $\mathcal O^\times_F$: it is only the restriction to $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$ of the $\mathcal O^\times_{F,S}$-invariant character $\chi_S$. With this caveat, the same argument for Theorem 2.4.2.1 leads to the analog of Corollary 2.4.3.2 that implies the regularity of $\psi$ over $\mathbf C_{>0}$. We refer the reader to the proof of Theorem 6.2.2.1(2)).

Moreover, since the poles of the Archimedean local factors $\prod_{v\in S_\infty}L_v(\chi_v|\cdot|^s_v)$ are resolved by the trivial zeros of $L_f(s,\chi)$, the meromorphic function:

$$
u(s) := \psi(s)\prod_{v\in S_\infty}L_v(\chi_v|\cdot|^s_v)^{-1}
$$

also has only removable singularities over the complex $s$-plane, because we know that $\phi$ is entire, as is $((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L(s,\chi)$. Since this latter is nowhere vanishing over $\mathbf C_{\le 0}$, the only singularities of $\psi(s)$ can be located over $\mathbf C_{\le 0}$, and are therefore resolved by the zeros of $\prod_{v\in S_\infty}L_v(\chi_v|\cdot|^s_v)^{-1}$.

## PDF page 308

**308** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

Its unique holomorphic continuation to the complex $s$-plane, which we again denote $u(s)$, satisfies:

$$
\phi(s) = u(s)((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L(s,\chi)
$$

which shows that indeed the range of $L$ is contained within

$$
((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C).
$$

Conversely, let $\phi\in A\mathcal S(\mathbf C)$ be of the form:

$$
\phi(s) = u(s)((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L(s,\chi)
$$

for some entire function $u$ on the complex $s$-plane.

The inverse Fourier transform of $\phi(it)$ is therefore Schwartz-Bruhat over $\mathbf R_{>0}$ and with exponential decay (see Definition D.3.3.1 for $I = \mathbf R$, and Proposition D.3.2.5).

We now choose a finite set $S$ of finite places of $F$, large enough so as to arrange for $\chi$ to be unramified outside of $S$, and $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.

By Proposition 5.3.4.4(3), there exists a Schwartz-Bruhat function $f_0\in\mathcal S_{00}(\mathbf A_{F,S})$ (see (5.3.4.1) from Definition 5.3.4.1 and recall that $\mathcal S_{00}(\mathbf A_{F,S})$ is the closed subspace of $\mathcal S(\mathbf A_{F,S})$ of those Schwartz-Bruhat functions that are entirely supported over $\mathrm{GL}_1(\mathbf A_{F,S})$, vanishing smoothly towards the boundary hyperplanes over $\mathbf A_{F,S_\infty}$), such that $Z_S(f_0,\chi_S|\cdot|^s_{F,S}) = \phi(s)$.

We note that by Corollary B.6.1.8, the meromorphic function

$$
\lambda_S(s) := \frac{1}{((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L_{\Sigma_F-S}(\chi,s)}
$$

has slow growth near its poles, and it is holomorphic over the open vertical strips of bounded width located within the complex $s$-plane away from $\mathbf C_{(0,1)}$.

It grows at most polymomially as $|s|\to +\infty$ over each such strip, as do its holomorphic derivatives of any order (see Remark B.1.1.4).

It follows that $\phi(s)\lambda_S(s)$ is meromorphic on the complex $s$-pane, it has poles located only at the poles of the local Hecke $L$-function $L_S(\chi_S,s)$:

$$
L_S(\chi_S,s) := \prod_{v\in S} L_v(\chi_v|\cdot|^s_v)
$$

with polar multiplicities bounded above by the orders of pole of the poles of $L_S(\chi_S,s)$.

We recall from Terminology 6.3.1.1 that we denote by $\chi_S$ the unique continuous character of $J_{F,S}$ descended by $\widehat{\mathcal O}^\times_{\Sigma_F-S}$-invariance from the restriction of $\chi$ to $C_{F,S}$.

We define $\phi_S(s) := \phi(s)\lambda_S(s)$ and

$$
\psi_S(s) := \frac{Z_S(\widehat{f}_0,\overline{\chi}_S|\cdot|^{1-s}_{F,S})}{((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L_{\Sigma_F-S}(\chi,s)} = \lambda_S(s)Z_S(\widehat{f}_0,\overline{\chi}_S|\cdot|^{1-s}_{F,S})
$$

a meromorphic function on the complex $s$-plane.

Since $Z_S(f_0,\chi_S|\cdot|^s_{F,S})$ is entire and by (3.3.1.2) from Theorem 3.3.1.1 we have

$$
Z_S(f_0,\chi_S|\cdot|^s_{F,S}) = \rho_S(\chi_S|\cdot|^s_{F,S})Z_S(\widehat{f}_0,\overline{\chi}_S|\cdot|^{1-s}_{F,S})
$$

then $Z_S(\widehat{f}_0,\overline{\chi}_S|\cdot|^{1-s}_{F,S})$ has zeros at the poles of $\rho_S(\chi_S\cdot|^s_{F,S})$, with multiplicity bounded below by the orders of pole, respectively.

Such poles are exactly the zeros of $((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L_S(\chi_S,s)^{-1}$, the polar order matching the multiplicity of the zero, respectively.

## PDF page 309

**6.3. LOCAL AND GLOBAL CONVERSE THEOREMS** · **309**

Moreover, the $S$-local functional equation from (3.3.1.2) of Theorem 3.3.1.1 ensures that $Z_S(\widehat{f}_0,\overline{\chi}_S|\cdot|^{1-s}_{F,S})$ also vanishes at each non-trivial zero of $L_f(s,\chi)$, (since $\phi(s) = Z_S(f_0,\chi_S|\cdot|^s_{F,S})$ does) equivalently at each zero of $L_{\Sigma_F-S}(\chi,s)$ contained within $\mathbf C_{(0,1)}$.

It follows that the ratio:

$$
\frac{Z_S(\widehat{f}_0,\overline{\chi}_S|\cdot|^{1-s}_{F,S})}{((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L_{\Sigma_F-S}(\chi,s)}
$$

has only removable singularities over $\mathbf C_{<1}$.

Both $\phi_S$ and $\psi_S$ are Schwartz uniformly over the vertical strips of bounded width of $\mathbf C_{>0}$, respectively $\mathbf C_{<1}$: to see this, we use the functional equation for the Hecke $L$-function $L_f(s,\chi)$ (see (B.1.1.9)) and the boundedness of $L_f(s,\chi)$ over $\mathbf C_{>0}$ and the polynomial growth of $W(s,\chi)$ and its holomorphic derivatives, as $|s|\to +\infty$ uniformly over each vertical strip of bounded width of the complex $s$-plane, together with Corollary B.6.1.8 on the polynomial growth of the reciprocal of $L_{\Sigma_F-S}(\chi,s)$ on a sequence of horizontal segments with growing absolute ordinates, of a vertical strip of the form $\mathbf C_{[-\varepsilon,1+\varepsilon]}$ for any $0<\varepsilon<1$.

By the functional equation for $L_f(s,\chi)$ (see (B.1.1.9)) and the $S$-local functional equation from (3.3.1.2) from Theorem 3.3.1.1, we have:

$$
\phi_S(s) = \frac{Z_S(f_0,\chi_S|\cdot|^s_{F,S})}{((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L_S(\chi_S,s)} \tag{6.3.2.16}
$$

$$
= \frac{\rho_S(\chi|\cdot|^s_{F,S})Z_S(\widehat{f}_0,\overline{\chi}_S|\cdot|^{1-s}_{F,S})}{((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}L_S(\chi_S,s)} \tag{6.3.2.17}
$$

$$
= \rho_S(\chi_S|\cdot|^s_{F,S})\psi_S(s). \tag{6.3.2.18}
$$

It follows by Theorem 5.4.1.1 that $(\phi_S(s),\psi_S(s))$ is in the image of the operator $U_{S,\tau_S,\chi_S|_{J^1_{F,S}}}$ from (5.4.1.2), and hence there exists a Schwartz-Bruhat function $f\in\mathcal S(\mathbf A_{F,S})$ such that $Z_S(f,\chi_S|\cdot|^s_{F,S}) = \phi_S(s)$.

In particular, we have:

$$
Z_S(f,\chi_S|\cdot|^s_{F,S})L_{\Sigma_F-S}(\chi,s)((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}} = \phi(s) = Z(\pi_S(f),\chi|\cdot|^s_F)((s+it_0)(1-s-it_0))^{\delta_{\chi|_{C^1_F}}}
$$

as meromorphic functions on the complex $s$-plane, and hence everywhere on the complex $s$-plane by analytic continuation.

This completes the description of the range of $L$.

(2) : By (1) and by Lemma 5.5.2.1, the sequence of operators in (6.3.2.5) is strict exact, and hence so are the sequences in (6.3.2.7) and (6.3.2.8).

$\square$

The following is a version of Theorem 6.3.2.1, providing a description of the range of the Mellin transform $L$ from (5.2.3.14), restricted to closed subspaces of $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$ defined to account for the removal of finitely many non-Archimedean “Euler factors” from $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$. It can be viewed as an incarnation of a “non primitive version” of the Converse Theorem for $\mathrm{GL}_1$ (see [CPS, Thm.1,p.165]).

Theorem 6.3.2.2 (Converse Theorem for $\mathrm{GL}_1$ - non-principal case). *Let $F$ be a number field, $\chi\in \widehat{C_F}$ a continuous character. Let $A\mathcal S(\mathbf C)$ be the Schwartz-Bergman space as per Definition D.3.1.3. We parametrize $\Omega(C_F)(\chi|_{C^1_F})$ by the global holomorphic parametrization*

$$
\chi|\cdot|^s_F,\ s\in\mathbf C.
$$

*Let $S_0$ be a finite set of finite places of $F$ and denote by $S_\chi$ the finite set of places of $F$ at which $\chi$ is ramified.*

*Let $\mathrm{PV}_{S_0}$ the Weil’s Global Principal Value operator on $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$.*

*We define $q_v := N(\mathfrak p_v)$, with $\mathfrak p_v$ the unique prime ideal of $\mathcal O_F$ corresponding to the finite place $v\in S_0$.*

## PDF page 310

**310** · **CHAPTER 6. LOCAL-GLOBAL STRUCTURES**

(1) *If $\chi|_{C^1_F}\ne 1$, then the continuous linear map:*

$$
Z\colon \mathrm{PV}_{S_0}\,\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))\to A\mathcal S(\mathbf C) \tag{6.3.2.19}
$$

*is a linear topological embedding with closed range equal to $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)\subset A\mathcal S(\mathbf C)$.*

*If $\chi|_{C^1_F} = 1$, then the continuous linear map:*

$$
L\circ\Phi_{F,1}\colon \mathrm{PV}_{S_0}\,\mathcal S_0(\mathbf A_F)\to A\mathcal S(\mathbf C) \tag{6.3.2.20}
$$

*is relatively open with closed range equal to $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)s(s-1)\widehat{\zeta}_F(s)\,\mathscr{O}(\mathbf C)\subset A\mathcal S(\mathbf C)$, and kernel equal to $\mathrm{PV}_{S_0}(\ker(\Phi_{F,1})\cap\mathcal S_0(\mathbf A_F))$.*

(2) *The following sequence of $\mathbf C$-linear operators:*

$$
0\to \mathrm{PV}_{S_0}\,\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))\to \mathrm{PV}_{S_0}\,\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))\to\mathbf C^{\oplus 2}\to 0 \tag{6.3.2.21}
$$

where:

(1) *$\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S_0(\mathbf A_F))$ is the quotient of $\mathcal S_0(\mathbf A_F)$ by $\ker(\Phi_F)\cap\mathcal S_0(\mathbf A_F)$, endowed with the quotient topology.*

(2) *$\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ is the quotient of $\mathcal S_0(\mathbf A_F)$ by $\ker(\Phi_{F,\chi|_{C^1_F}})\cap\mathcal S_0(\mathbf A_F)$, endowed with the quotient topology.*

(3) *The rightmost operator sends $\Phi_{F,\chi|_{C^1_F}}(\mathrm{PV}_{S_0}(f))$ to the pair of complex numbers:*

$$
-\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{it_0}_v)\overline{\mu}_1(C^1_F)\,f(0)\,\delta_{\chi|_{C^1_F}},\quad \prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-1+it_0}_v)\overline{\mu}_1(C^1_F)\,\widehat{f}(0)\,\delta_{\chi|_{C^1_F}} \tag{6.3.2.22}
$$

with $\delta_{\chi|_{C^1_F}} = 0$ if $\chi|_{C^1_F}\ne 1$, and $\delta_1 = 1$.

*is strict exact, and under the Mellin transform $\phi\mapsto M(\phi)(s) := \int_{C_F}\phi(g)\chi(g)|g|^s_F\,\mathrm{d}\overline{\mu}(g)$ it is linearly and topologically isomorphic to the short exact sequence:*

$$
0\to\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)\to\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)L(s,\chi)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C)\to 0 \tag{6.3.2.23}
$$

*if $\chi|_{C^1_F}\ne 1$, the middle operator in (6.3.2.23) being the identity, and the topology on $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)L(s,\chi)\,\mathscr{O}(\mathbf C)$ being the subspace topology inherited from $A\mathcal S(\mathbf C)$, and to the short exact sequence:*

$$
0\to (s-it_0)(1-s-it_0)\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)\widehat{\zeta}_F(s+it_0)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C) \tag{6.3.2.24}
$$

$$
\to\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)\widehat{\zeta}_F(s+it_0)\,\mathscr{O}(\mathbf C)\cap A\mathcal S(\mathbf C) \tag{6.3.2.25}
$$

$$
\to\mathbf C\oplus\mathbf C\to 0 \tag{6.3.2.26}
$$

*for a real number $t_0\in\mathbf R$ uniquely determined by $\chi$, where the rightmost operator sends an element of $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)\widehat{\zeta}_F(s+it_0)\,\mathscr{O}(\mathbf C)$ to the pair of residues at $s = -it_0, 1-it_0$, the topology on the leftmost space of meromorphic functions from (6.3.2.24) being the subspace topology inherited from $A\mathcal S(\mathbf C)$, and the topology on the middle space of meromorphic functions being the quotient topology induced by $L$ from $\mathrm H_{0,\mathrm{cont}}(|\cdot|^{it_0}_F, \mathcal S(\mathbf A_F))$.*

Proof. Both (1) and (2) follow from the combination of Lemma 5.3.1.5 and Theorem 6.3.2.1.

$\square$
