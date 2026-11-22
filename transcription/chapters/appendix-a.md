## PDF page 537

APPENDIX A

**Preparations from Algebraic Number Theory**

In this appendix we review some classic results in algebraic number theory, encompassing compactness of the norm-1 subgroup of the idele class group $C_F$ of a number field $F$, along with the construction of normalized Haar measures on $\mathrm{GL}_1(\mathbf{A}_F)$, $C_F$, and their closed subgroups of norm-1 elements, as well as the construction of fundamental domains for the $F$-action on $\mathbf{A}_F$ and the $F^\times$-action on $\mathrm{GL}_1(\mathbf{A}_F)^1$. We also review an adelic version of the theory of Hardy-Littlewood maximal functions for use in our work with measurable adelic kernel functions.

For $F$ a number field, we denote by:

(1) $\Sigma_F$ the set of places of $F$: equivalence classes of non-trivial absolute values (in the sense of [CF, Ch. II, §13-14]).

(2) $S_\infty$ the set of Archimedean places of $F$, $r_1$ the number of real places, $r_2$ the number of complex places.

(3) $S_{F,f}$ or $S_f$ the set of non-Archimedean places of $F$. We refer to its elements as the *finite* places.

A.1. Topology of $\mathbf{A}_F$, $\mathbf{A}_{F,S}$ and $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, and their class groups 539

A.1.1. The adeles $\mathbf{A}_F$ as a topological ring 539

A.1.1.1. Recollections on restricted products. 539

A.1.2. The adeles as an abelian topological group 540

A.1.2.1. Finiteness results on $\mathbf{A}_F$. 540

A.1.3. The idele group $\mathrm{GL}_1(\mathbf{A}_F)$ 541

A.1.3.1. The idelic topology on $\mathrm{GL}_1(\mathbf{A}_F)$. 541

A.1.3.2. Discreteness of the $F^\times$-action on $\mathrm{GL}_1(\mathbf{A}_F)$. 542

A.1.4. The idele class group $C_F$ 542

A.1.4.1. Finiteness results on the idele class group. 542

A.1.5. $S$-adeles, $S$-ideles and their class groups 543

A.1.5.1. $S$-adeles and $S$-ideles. 543

A.1.5.2. The ring of $S$-adeles $\mathbf{A}_{F,S}$ and its class group $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$. 543

A.1.5.3. The topological group of $S$-ideles $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and its class group $C_{F,S}$. 544

A.2. Orbital structures on adeles and ideles 545

A.2.1. Fundamental domain of the additive $F$-translation action on $\mathbf{A}_F$ 545

A.2.1.1. The adelic fundamental domain $F$. 545

A.2.2. Continuous homomorphic sections to the idelic norm 546

A.2.2.1. The canonical section. 546

A.2.2.2. The section along $F^\times_{v_0}$, for $v_0$ a choice of Archimedean place. 547

A.2.2.3. The diagonal section into $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$. 547

A.2.3. Fundamental domain of the multiplicative $F^\times$-translation action on $\mathrm{GL}_1(\mathbf{A}_F)^1$ 548

A.2.3.1. The logarithm homomorphism. 548

A.2.3.2. The idelic fundamental domain $E^1_F$. 548

A.2.3.3. Topological structure of $E_0$. 550

537

## PDF page 538

**538** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

A.2.3.4. Global description of $\mathrm{GL}_1(\mathbf{A}_F)$. 552

A.2.3.5. Topological structure of $E^1_F$. 552

A.2.3.6. Fundamental domain $E_F$ for the $F^\times$-action on $\mathrm{GL}_1(\mathbf{A}_F)$. 553

A.2.3.7. Product loci, interiors and compactness. 553

A.2.4. Fundamental domain for $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$ and $C_{F,S}$ 553

A.2.4.1. Fundamental domain for the additive $\mathcal{O}_{F,S}$-action on $\mathbf{A}_{F,S}$. 554

A.2.4.2. Fundamental domain for the multiplicative $\mathcal{O}_{F,S}^\times$-action on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$. 554

A.3. Haar measures 555

A.3.1. Tamagawa measure on $\mathbf{A}_F$ 555

A.3.1.1. Self-duality of local additive Tamagawa measures. 557

A.3.2. Tamagawa measure on $\mathrm{GL}_1(\mathbf{A}_F)$ 559

A.3.3. Haar measures on $C_F$ and $C^1_F$ 561

A.3.3.1. Continuous sections of the idelic norm and Radon product decompositions. 561

A.3.4. $S$-local Tamagawa measures 561

A.4. Dirichlet's $S$-unit Theorem: estimates by lattice point-counting 562

A.4.1. Lattice point-counting and Dirichlet's $S$-Unit Theorem 562

A.5. Idelic Hardy-Littlewood Maximal Theorem and Lebesgue Differentiation 566

A.5.1. Hardy-Littlewood Maximal Theorem on the real line 566

A.5.1.1. 1-dimensional Hardy-Littlewood Maximal Theorem. 566

A.5.1.2. 1-dimensional Lebesgue Differentiation Theorem. 568

A.5.2. $D$-sequences, $D'$-sequences, $D''$-sequences in Hausdorff locally compact abelian groups 569

A.5.2.1. $D$-sequences and $D'$-sequences in Hausdorff locally compact abelian groups. 569

A.5.2.2. The case of $S$-local and global groups of ideles and idele classes. 574

A.5.3. Hardy-Littlewood Maximal Theorem on Hausdorff locally compact abelian groups 578

A.5.3.1. Hardy-Littlewood Maximal Theorems on Hausdorff locally compact abelian groups. 579

A.5.4. Lebesgue Differentiation on Hausdorff locally compact abelian groups 582

## PDF page 539

**A.1. TOPOLOGY OF $\mathbf{A}_F$, $\mathbf{A}_{F,S}$ AND $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, AND THEIR CLASS GROUPS** · **539**

**A.1. Topology of $\mathbf{A}_F$, $\mathbf{A}_{F,S}$ and $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, and their class groups**

In this section we review some basic notation and definitions related to the adele ring of a number field $F$ and the idele group $\mathrm{GL}_1(\mathbf{A}_F)$. We will henceforth adopt the terminology and conventions from [CF, Ch. II]. In particular, the square of the complex Euclidean norm is an absolute value according to our conventions. Its equivalence class contains the complex Euclidean norm. We moreover note that a place $v$ of $F$ is required to be non-trivial. Proofs for assertions below are given in many references (such as [CF] and [RV]), so they are generally not given here.

**A.1.1. The adeles $\mathbf{A}_F$ as a topological ring.** Let $F$ be a number field. In this subsection we recall the construction of the adele ring $\mathbf{A}_F$ and its topological ring structure.

A.1.1.1. *Recollections on restricted products.* We recall the definition of restricted product of a collection of pairs $(G_i, K_i)$, indexed by a set $I$, where $G_i$ is a Hausdorff locally compact abelian group, and $K_i \subset G_i$ is a compact open subgroup.

**Definition A.1.1.1.** Let $I_0$ be a finite set, $I_1$ a set, and write $I := I_0 \times I_1$. Let $\{G_i\}_{i \in I}$ be an $I$-indexed collection of Hausdorff locally compact abelian groups, and $\{K_i\}_{i \in I}$ an $I$-indexed collection of subgroups $K_i \subset G_i$ for each $i \in I$, where $K_i = 1$ for every $i \in I_0$, and $K_i$ is compact open in $G_i$ for every $i \in I_1$. We define

$$
\widehat{\prod}_{i \in I}(G_i, K_i) \subset \prod_{i \in I} G_i \tag{A.1.1.1}
$$

as the subset of those $I$-indexed tuples $(x_i) \in \prod_{i \in I} G_i$ such that $x_i \in K_i$ for all but finitely many $i \in I$. We topologize $\widehat{\prod}_{i \in I}(G_i, K_i)$ by defining a neighborhood base at $1$ to be given by the subsets of the form $\prod_{i \in I} U_i$, where $U_i$ is a neighborhood of $1$ in $G_i$ for every $i \in I$, and $U_i = K_i$ for all but finitely many $i \in I$. We refer to $\widehat{\prod}_{i \in I}(G_i, K_i)$ as the *restricted product* of the collection $\{(G_i, K_i)\}_{i \in I}$.

We write $\mathbf{A}_F$ for the adele ring of the number field $F$.

Recall that, upon writing $v$ for the arbitrary place of $F$, this is the topological ring defined as the restricted direct product

$$
\mathbf{A}_F := \widehat{\prod}_v (F_v, R_v) \tag{A.1.1.2}
$$

of the local fields $F_v$, each a finite extension of either $\mathbf{R}$, $\mathbf{C}$, or $\mathbf{Q}_p$ for a unique prime number $p$, and where $R_v$ is the valuation ring $\mathcal{O}_{\mathfrak{p}}$ in case $v = v_{\mathfrak{p}}$ for a prime ideal $\mathfrak{p}$ of $\mathcal{O}_F$, and $R_v = F_v$ for $v$ Archimedean. We denote by

$$
\iota : F \to \mathbf{A}_F \tag{A.1.1.3}
$$

the ring homomorphism sending $\xi \in F$ to the adele whose local component at the place $v \in \Sigma_F$ is the image of $\xi$ under the completion map $\iota_v : F \to F_v$. We call $\iota$ the *diagonal embedding* of $F$ in $\mathbf{A}_F$.

We refer the reader to [RV, Ch. 5, §5.1], [DE, Ch. 13], [CF, Ch. II, §13-14], and Tate's thesis [CF, Ch. XV, §3, §4.1] for more on restricted products and the adeles of a number field.

We recall the following description of the topology on the restricted product of Hausdorff locally compact abelian groups:

**Lemma A.1.1.2.** *Let $I_0$ be a finite set, $I_1$ a set, and $I := I_0 \times I_1$. Let $\{(G_i, K_i)\}_{i \in I}$ be an $I$-indexed collection of pairs $(G_i, K_i)$ of Hausdorff locally compact abelian groups, where $K_i = 1$ for all $i \in I_0$ and $K_i \subset G_i$ is compact open for all $i \in I_1$. Then*

(1) *The restricted product $\widehat{\prod}_{i \in I}(G_i, K_i)$ is a Hausdorff locally compact abelian group.*

## PDF page 540

**540** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

(2) *Let $\{K'_i\}_{i \in I}$ be an $I$-indexed collection of subgroups $K'_i \subset G_i$, with $K'_i = 1$ for all $i \in I_0$, $K'_i \subset G_i$ compact open for all $i \in I_1$, and $K'_i = K_i$ for all but finitely many $i \in I$. Then the restricted product $\widehat{\prod}_{i \in I}(G_i, K'_i)$ is canonically isomorphic, as a Hausdorff locally compact abelian group, to the restricted product $\widehat{\prod}_{i \in I}(G_i, K_i)$.*

(3) *A subset $H \subset \widehat{\prod}_{i \in I}(G_i, K_i)$ has compact closure if and only if there exists an $I$-indexed collection $\{H_i\}_{i \in I}$ with $H_i \subset G_i$ a compact subset for every $i \in I$, and $H_i = K_i$ for all but finitely many $i \in I$, and we have $H \subset \prod_{i \in I} H_i$.*

(4) *For any partition $I = J_1 \coprod J_2$ with $J_1$ a finite subset, the canonical map*

$$
\prod_{j \in J_1} G_i \times \widehat{\prod}_{j \in J_2}(G_j, K_j) \to \widehat{\prod}_{i \in I}(G_i, K_i) \tag{A.1.1.4}
$$

*is an isomorphism of Hausdorff locally compact abelian groups.*

(5) *For any partition $I = J_1 \coprod J_2$ with $J_1$ a finite subset, the subset*

$$
\prod_{j \in J_1} U_i \times \prod_{j \in J_2} K_j \subset \widehat{\prod}_{i \in I}(G_i, K_i) \tag{A.1.1.5}
$$

*with $U_i \subset G_i$ an open subset, is open.*

**Definition A.1.1.3.** Let $F$ be a number field. We define:

(1) $\mathbf{A}_{F,S_\infty}$ as the topological ring $\mathbf{R} \otimes_{\mathbf{Q}} F = \prod_{v \mid \infty} F_v$ topologized with the unique $\mathbf{R}$-linear topology induced by the Euclidean metric topology on $\mathbf{R}$.

(2) $\mathbf{A}^f_F$ as the topological ring obtained as the restricted product of the pairs $(F_v, \mathcal{O}_v)$ as $v$ ranges over all the finite places of $F$. We refer to $\mathbf{A}^f_F$ as the topological ring of the *finite adeles*.

The topological ring $\mathbf{A}_F$ can be equivalently described as the product topological ring

$$
\mathbf{A}_{F,S_\infty} \times \mathbf{A}^f_F \tag{A.1.1.6}
$$

topologized with the product topology. This is a consequence of Lemma A.1.1.2(4) with $J_1 = S_\infty$ and $J_2 = \Sigma_{F,f}$ the respective sets of Archimedean and non-Archimedean places of $F$.

**A.1.2. The adeles as an abelian topological group.** As an abelian topological group, the additive group underlying the topological ring $\mathbf{A}^f_F$ is the inductive limit of the abelian topological groups $\prod_{v \nmid \infty} H_v$ where $H_v \subset F_v$ is a compact open subgroup for every non-trivial finite place $v$, and $H_v = \mathcal{O}_v$ for all but finitely many such $v$.

Each $\prod_{v \nmid \infty} H_v$ is in turn contained in a compact open subgroup of $\mathbf{A}^f_F$ of the form $(1/N)\widehat{\mathcal{O}}_F$ for some integer $N \geq 1$, where $\widehat{\mathcal{O}}_F$ is the completion of $\mathcal{O}_F$ as a discrete additive abelian group with respect to the topology generated by the family of proper subgroups $\{I\mathcal{O}_F\}$ as $I$ varies over the proper ideals of the ring $\mathcal{O}_F$.

A.1.2.1. *Finiteness results on $\mathbf{A}_F$.* We record below certain results on the topology of $\mathbf{A}_F$, its class group $\mathbf{A}_F/F$, and $S$-local analogs.

**Lemma A.1.2.1.** *Let $F$ be a number field. The following short exact sequence of abelian groups*

$$
0 \to F \xrightarrow{\iota} \mathbf{A}_F \to \mathbf{A}_F/F \to 0 \tag{A.1.2.1}
$$

*where the first homomorphism is the diagonal embedding induced by the completion field homomorphism $\iota_v : F \to F_v$ for every place $v$ of $F$, is topologically exact in the strict sense, i.e. $\iota$ is a closed homomorphism upon endowing $F$ with the discrete topology. Moreover*

(1) *The image of $\iota$ is discrete.*

(2) *The quotient topological group $\mathbf{A}_F/F$ is compact Hausdorff.*

## PDF page 541

**A.1. TOPOLOGY OF $\mathbf{A}_F$, $\mathbf{A}_{F,S}$ AND $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, AND THEIR CLASS GROUPS** · **541**

(3) *The abelian group $\mathbf{A}_F/F$ is uniquely divisible, and the canonical continuous homomorphism of Hausdorff locally compact abelian group $\mathbf{A}_{F,S_\infty} \times \widehat{\mathcal{O}}_F \to \mathbf{A}_F$ induces an isomorphism of Hausdorff locally compact abelian groups*

$$
(\mathbf{A}_{F,S_\infty} \times \widehat{\mathcal{O}}_F)/\mathcal{O}_F \to \mathbf{A}_F/F. \tag{A.1.2.2}
$$

*Formation of the sequence in (A.1.2.1) and of the isomorphism in (A.1.2.2) is functorial with respect to field homomorphisms of finite extensions $F'/F$ of the number field $F$.*

**A.1.3. The idele group $\mathrm{GL}_1(\mathbf{A}_F)$.** In this subsection we record basic properties of the idelic topology on the group $\mathrm{GL}_1(\mathbf{A}_F)$.

A.1.3.1. *The idelic topology on $\mathrm{GL}_1(\mathbf{A}_F)$.* Central to number theory is the group of units $\mathbf{A}^\times_F$ of $\mathbf{A}_F$. The subspace topology on $\mathbf{A}^\times_F$ does not render, however, $\mathbf{A}^\times_F$ a topological group, insofar as inversion is not continuous. Moreover, $\mathbf{A}^\times_F$ is not open in $\mathbf{A}_F$. The group $\mathbf{A}^\times_F$ is therefore re-topologized:

**Definition A.1.3.1.** Let $F$ be a number field. We define the *idelic topology* on the unit group $\mathbf{A}^\times_F$ of the adele ring $\mathbf{A}_F$ to be the topology induced by the anti-diagonal map

$$
\mathbf{A}^\times_F \to \mathbf{A}_F \times \mathbf{A}_F \tag{A.1.3.1}
$$

sending $x$ to $(x, x^{-1})$. We denote by $\mathrm{GL}_1(\mathbf{A}_F)$ the group $\mathbf{A}^\times_F$ endowed with the idelic topology, and refer to it as the idele group of $F$.

We refer the reader to [CF, Ch. II, §16] and to [DE, §13.3], for more on the ideles of a number field. We will be recalling further facts on adeles and ideles as the need arises.

**Remark A.1.3.2.** The task of topologizing the adelic points of algebraic groups can be carried out following Weil's approach in [Weil-c] (see, specifically, [Weil-c, Ch. III]) by means of a process of "adelization", or Grothendieck's, by topologizing the adelic points of the underlying scheme. We refer the reader to [Conrad, §2] for an account of the methods and history around the task of topologizing the adelic points of an algebraic group, of which the first special non-trivial case of $(\mathrm{GL}_1)_F$ leads to the ideles $\mathrm{GL}_1(\mathbf{A}_F)$.

One more piece of information about $\mathrm{GL}_1(\mathbf{A}_F)$ is that there exists a canonical homomorphism of abelian topological groups

$$
|\cdot|_F : \mathrm{GL}_1(\mathbf{A}_F) \to \mathbf{R}_{>0} \tag{A.1.3.2}
$$

defined as

$$
|g|_F := \prod_{v \in \Sigma_F} |g_v|_v, \; g \in \mathrm{GL}_1(\mathbf{A}_F) \tag{A.1.3.3}
$$

where $|\cdot|_v$ is the normalized absolute value on $F_v$ contained in $v \in \Sigma_F$.

The assignment of $|g|_F$ in (A.1.3.3) converges since $g_v \in \mathcal{O}^\times_v$ for all but finitely many $v$.

We define the subgroup

$$
\mathrm{GL}_1(\mathbf{A}_F)^1 := \ker(|\cdot|_F) \subset \mathrm{GL}_1(\mathbf{A}_F) \tag{A.1.3.4}
$$

of ideles of "norm 1".

An important feature of the idelic topology on $\mathrm{GL}_1(\mathbf{A}_F)$ is that, contrary to the subspace topology on $\mathbf{A}^\times_F$, it promotes $\mathbf{A}^\times_F$ to a Hausdorff locally compact abelian group.

**Lemma A.1.3.3.** *Let $F$ be a number field. The idele group $\mathrm{GL}_1(\mathbf{A}_F)$ is a Hausdorff locally compact abelian group with respect to the idelic topology, and isomorphic to the restricted product*

$$
\widehat{\prod}_{v \in \Sigma_F} (F^\times_v, \mathcal{O}^\times_{F_v}).
$$

## PDF page 542

**542** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

*The idelic norm $|\cdot|_F$ from (A.1.3.2) is a continuous homomorphism of Hausdorff locally compact abelian groups, and $\mathrm{GL}_1(\mathbf{A}_F)^1 \subset \mathrm{GL}_1(\mathbf{A}_F)$ is a closed subgroup.*

A.1.3.2. *Discreteness of the $F^\times$-action on $\mathrm{GL}_1(\mathbf{A}_F)$.* In this subsection we recall basic results on the continuous left-translation action of $F^\times$ on $\mathrm{GL}_1(\mathbf{A}_F)$, and its orbits.

**Lemma A.1.3.4.** *Let $F$ be a number field. The following short exact sequence*

$$
1 \to F^\times \xrightarrow{\iota} \mathrm{GL}_1(\mathbf{A}_F) \to \mathrm{GL}_1(\mathbf{A}_F)/F^\times \to 1 \tag{A.1.3.5}
$$

*where the first homomorphism is the diagonal embedding induced by the completion field homomorphism $\iota_v : F \to F_v$ for every place $v$ of $F$, is topologically exact in the strict sense, i.e. $\iota$ is a closed homomorphism upon endowing $F^\times$ with the discrete topology. Formation of the sequence in (A.1.3.5) is functorial with respect to field homomorphisms of finite extensions of $F'/F$ of the number field $F$.*

(1) *The image of $\iota$ is discrete.*

(2) *The quotient topological group $\mathrm{GL}_1(\mathbf{A}_F)/F^\times$ is Hausdorff locally compact.*

(3) *The idelic norm $|\cdot|_F$ factors through the quotient $\mathrm{GL}_1(\mathbf{A}_F)/F^\times$. The induced continuous surjective homomorphism*

$$
|\cdot|_F : \mathrm{GL}_1(\mathbf{A}_F)/F^\times \to \mathbf{R}_{>0} \tag{A.1.3.6}
$$

*admits a continuous homomorphic section.*

Some explicit construction of the asserted section in (3) are given in §A.2.2.

**A.1.4. The idele class group $C_F$.** In this subsection we recall the construction and main results on the class group $C_F$ of the idele group, and their consequences.

A.1.4.1. *Finiteness results on the idele class group.*

**Definition A.1.4.1.** Let $F$ be a number field. We define

$$
C_F := \mathrm{GL}_1(\mathbf{A}_F)/F^\times \tag{A.1.4.1}
$$

as the quotient Hausdorff locally compact abelian group. We refer to $C_F$ as the idele class group of $F$.

As per Lemma A.1.3.4(3), the idelic norm $|\cdot|_F : \mathrm{GL}_1(\mathbf{A}_F) \to \mathbf{R}_{>0}$ descends to a continuous homomorphism of Hausdorff locally compact abelian groups

$$
|\cdot|_F : C_F \to \mathbf{R}_{>0} \tag{A.1.4.2}
$$

whose kernel we denote $C^1_F$, a compact Hausdorff subgroup by Lemma A.1.3.4(3).

**Remark A.1.4.2.** Let $F$ be a number field. The strict exact sequence of continuous homomorphisms of Hausdorff locally compact abelian groups from (A.1.3.5) induces the following short exact sequence

$$
1 \to F^\times \xrightarrow{\iota} \mathrm{GL}_1(\mathbf{A}_F)^1 \to C^1_F \to 1 \tag{A.1.4.3}
$$

which is topologically exact in the strict sense, i.e. $\iota$ is a closed homomorphism upon endowing $F^\times$ with the discrete topology. In particular, $C^1_F$ is isomorphic, as a Hausdorff locally abelian group, to $\mathrm{GL}_1(\mathbf{A}_F)^1/F^\times$.

We recall the following fundamental result about the Hausdorff locally compact abelian group $C_F$ and its closed subgroup $C^1_F$.

**Theorem A.1.4.3.** *Let $F$ be a number field.*

(1) *The closed subgroup $C^1_F \subset C_F$ is compact Hausdorff.*

## PDF page 543

**A.1. TOPOLOGY OF $\mathbf{A}_F$, $\mathbf{A}_{F,S}$ AND $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, AND THEIR CLASS GROUPS** · **543**

(2) *The unit group $\mathcal{O}^\times_F$ is finitely generated, and its maximal free subquotient has rank $r_1 + r_2 - 1$.*

(3) *The class group $\mathrm{Cl}(\mathcal{O}_F)$ of fractional ideal classes (equal to the group $\mathrm{Pic}(\mathcal{O}_F)$ of divisor classes) is finite.*

**A.1.5. $S$-adeles, $S$-ideles and their class groups.** We let $F$ be a number field, $S$ a finite set of places of $F$ containing all of the Archimedean places. We denote by $S_f$ the subset of all the finite places of $F$ contained in $S$, i.e. $S_f := \Sigma_{F,f} \cap S$. We study in this subsection $S$-local analogs of $\mathbf{A}_F$ and $\mathrm{GL}_1(\mathbf{A}_F)$, and their class groups $\mathbf{A}_F/F$ and $C_F$.

A.1.5.1. *$S$-adeles and $S$-ideles.* We denote by $\mathbf{A}_{F,S}$ the finite product topological ring:

$$
\mathbf{A}_{F,S} := \prod_{v \in S} F_v \tag{A.1.5.1}
$$

topologized with the product topology, and by

$$
\mathrm{GL}_1(\mathbf{A}_{F,S}) = \prod_{v \in S} F^\times_v \tag{A.1.5.2}
$$

the group of units of $\mathbf{A}_{F,S}$, topologized with the subspace topology. Clearly this topology on $\mathrm{GL}_1(\mathbf{A}_{F,S})$ agrees with the product topology upon endowing each $F^\times_v \subset F_v$ with the subspace topology. The group $\mathrm{GL}_1(\mathbf{A}_{F,S})$ is thereby promoted to a Hausdorff locally compact topological group.

We refer to $\mathbf{A}_{F,S}$ as the *$S$-adele ring* of $F$, and to $\mathrm{GL}_1(\mathbf{A}_{F,S})$ as the *$S$-idele group* of $F$. The ring of $S$-integers in $F$ is

$$
\mathcal{O}_{F,S} = \{\xi \in F : \iota_v(\xi) \in \mathcal{O}_{F_v} \text{ for all } v \notin S\}.
$$

We denote by

$$
\iota_S : \mathcal{O}_{F,S} \to \mathbf{A}_{F,S} \tag{A.1.5.3}
$$

the natural inclusion.

A.1.5.2. *The ring of $S$-adeles $\mathbf{A}_{F,S}$ and its class group $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$.* We have the following $S$-local analog of Lemma A.1.2.1. Recall that we denote by $S_f$ the subset of all the finite places of $F$ contained in $S$, i.e. $S_f := \Sigma_{F,f} \cap S$.

For every $v \in S_f$, we denote by $\mathfrak{p}_v \subset \mathcal{O}_F$ the prime ideal of $\mathcal{O}_F$ corresponding to the finite place $v \in S$.

**Lemma A.1.5.1.** *Let $F$ be a number field, $S$ a finite set of places containing the Archimedean places of $F$. The following short exact sequence of abelian groups*

$$
0 \to \mathcal{O}_{F,S} \xrightarrow{\iota_S} \mathbf{A}_{F,S} \to \mathbf{A}_{F,S}/\mathcal{O}_{F,S} \to 0 \tag{A.1.5.4}
$$

*where the first homomorphism is the diagonal embedding induced by the completion field homomorphism $\iota_v : F \to F_v$ for every place $v \in S$ of $F$, is topologically exact in the strict sense, i.e. $\iota_S$ is a closed homomorphism upon endowing $\mathcal{O}_{F,S}$ with the discrete topology. Moreover*

(1) *The image of $\iota_S$ is discrete.*

(2) *The quotient topological group $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$ is compact Hausdorff.*

(3) *The continuous quotient homomorphism*

$$
(\mathbf{A}_{F,S} \times \prod_{v \in \Sigma_F - S} \mathcal{O}_{F_v})/\mathcal{O}_{F,S} \to \mathbf{A}_{F,S}/\mathcal{O}_{F,S}
$$

*is a proper continuous quotient homomorphism of Hausdorff locally compact abelian groups, whose source is isomorphic to $\mathbf{A}_F/F$ under the continuous injective homomorphism induced by $\mathbf{A}_{F,S} \times \prod_{v \in \Sigma_F - S} \mathcal{O}_{F_v} \to \mathbf{A}_F$. In particular, $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$ is naturally a $\mathbf{Q}$-vector space.*

## PDF page 544

**544** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

A.1.5.3. *The topological group of $S$-ideles $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and its class group $C_{F,S}$.* We define the following $S$-local analog of the idelic norm from (A.1.3.2):

$$
|\cdot|_{F,S} : \mathrm{GL}_1(\mathbf{A}_{F,S}) \to \mathbf{R}_{>0} \tag{A.1.5.5}
$$

by the assignment:

$$
|g|_{F,S} := \prod_{v \in S} |g_v|_v \tag{A.1.5.6}
$$

for every $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$.

We refer to $|\cdot|_{F,S}$ as the *$S$-idelic norm*. We define

$$
C_{F,S} := \mathrm{GL}_1(\mathbf{A}_{F,S} \times \prod_{v \notin S} \mathcal{O}_{F_v})/\mathcal{O}^\times_{F,S} \tag{A.1.5.7}
$$

and refer to it as the *$S$-idele class group*. We note that by Lemma A.1.5.1(1), $C_{F,S}$ is a Hausdorff locally compact abelian group. Moreover, we have $|\mathcal{O}^\times_{F,S}|_{F,S} = 1$, and hence the $S$-idelic norm descends uniquely to a continuous surjective homomorphism of Hausdorff locally compact abelian groups:

$$
|\cdot|_{F,S} : C_{F,S} \to \mathbf{R}_{>0}. \tag{A.1.5.8}
$$

Denote by $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, respectively $C^1_{F,S}$, the kernel of $|\cdot|_{F,S}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})$, respectively on $C_{F,S}$, so $C^1_{F,S} \simeq (\mathrm{GL}_1(\mathbf{A}_{F,S})^1 \times \prod_{v \notin S} \mathcal{O}^\times_{F_v})/\mathcal{O}^\times_{F,S}$ under the canonical quotient map $\mathrm{GL}_1(\mathbf{A}_{F,S}) \times \prod_{v \notin S} \mathcal{O}^\times_{F_v} \to C_{F,S}$ since $|\mathcal{O}^\times_{F,S}|_{F,S} = |\mathcal{O}^\times_{F,S}|_F = 1$ (the first copy of $\mathcal{O}_{F,S}$ is diagonally embedded into $\mathbf{A}_{F,S}$, and the second is diagonally embedded into $\mathbf{A}_{F,S} \times \prod_{v \notin S} \mathcal{O}_{F_v} \subset \mathbf{A}_F$).

We have the following analog of Theorem A.1.4.3:

**Theorem A.1.5.2.** *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places of $F$.*

(1) *The closed subgroup $C^1_{F,S} \subset C_{F,S}$ is compact Hausdorff.*

(2) *The unit group $\mathcal{O}^\times_{F,S}$ is finitely generated, and its maximal free subquotient has rank $|S| - 1$.*

(3) *The abelian group $\mathrm{Pic}(\mathcal{O}_{F,S})$ is finite.*

From the classical description

$$
\widehat{\prod}_{v \notin S} (F^\times_v, \mathcal{O}^\times_{F_v})/F^\times \cdot \prod_{v \notin S} \mathcal{O}^\times_{F_v} \simeq \mathrm{Pic}(\mathcal{O}_{F,S})
$$

we get the short exact sequence

$$
1 \to \left(\prod_{v \in S'_f - S_f} F^\times_v/\mathcal{O}^\times_{F_v}\right)/\mathcal{O}^\times_{F,S'} \to \mathrm{Pic}(\mathcal{O}_{F,S}) \to \mathrm{Pic}(\mathcal{O}_{F,S'}) \to 0 \tag{A.1.5.9}
$$

for $S' \supset S$.

**Remark A.1.5.3 (Uniformization and the Archimedean places).** We note that by choosing $S'$ large enough i so as to arrange $\mathrm{Pic}(\mathcal{O}_{F,S'}) = 1$, we deduce from exactness of (A.1.5.9) the isomorphism of finite abelian groups:

$$
\left(\prod_{v \in S'_f - S_f} F^\times_v/\mathcal{O}^\times_{F_v}\right)/\mathcal{O}^\times_{F,S'} \to \mathrm{Pic}(\mathcal{O}_{F,S}).
$$

## PDF page 545

**A.2. ORBITAL STRUCTURES ON ADELES AND IDELES** · **545**

In particular, for $S = S_{\infty}$ and $S'$ large enough so as to arrange for $\mathrm{Pic}(\mathcal{O}_{F,S'}) = 1$ to hold, and upon renaming $S'$ as $S$, we have the isomorphism of finite abelian groups

$$
\left(\prod_{v\in S_f} F_v^{\times}/\mathcal{O}_{F_v}^{\times}\right)/\mathcal{O}_{F,S}^{\times} \to \mathrm{Pic}(\mathcal{O}_F). \tag{A.1.5.10}
$$

The isomorphism from (A.1.5.10) is compatible with enlargement of $S$, and with the natural isomorphism

$$
\mathrm{GL}_1(\mathbf{A}_F)^1/F^{\times}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 \times \widehat{\mathcal{O}}_F^{\times}) \to \mathrm{Pic}(\mathcal{O}_F).
$$

**A.2. Orbital structures on adeles and ideles**

In this section, we examine adelic and idelic quotients explicitly, constructing relatively compact fundamental domains for the additive $F$-translation action of $F$ on $\mathbf{A}_F$, and the multiplicative translation action of $F^{\times}$ on $\mathrm{GL}_1(\mathbf{A}_F)^1$.

While the topics are covered in detail within the literature (for which our main references will be [**RV**, Ch. 5, §5.1], [**CF**, Ch. XV, §4.1, §4.3]), we will be highlighting certain structural, measure-theoretic and topological properties of these domains, to be used later throughout this work.

**A.2.1. Fundamental domain of the additive $F$-translation action on $\mathbf{A}_F$.** In light of Lemma A.1.2.1, the diagonal image of $F$ in $\mathbf{A}_F$ is discrete and co-compact. We recall how to construct a fundamental domain for the action by additive translation of $F$ on $\mathbf{A}_F$, i.e. a relatively compact subset $D \subset \mathbf{A}_F$ with non-empty interior, such that $F + D = \mathbf{A}_F$, and $(\xi + D) \cap D = \varnothing$ for every $\xi \in F^{\times}$.

A.2.1.1. *The adelic fundamental domain $F$.* In this subsection we describe the compact Hausdorff quotient $\mathbf{A}_F/F$ by means of a fundamental domain within $\mathbf{A}_F$ of the continuous left-translation action by $F$.

Definition A.2.1.1. Let $F$ be a number field. We fix a $\mathbf{Z}$-basis $\{a_1,\dots,a_d\} \subset \mathcal{O}_F$, with $d := [F:\mathbf{Q}]$ and enumerate the infinite places of $F$ as $v_1,\dots,v_{r_1+r_2}$. We denote by $D_{F,\infty} \subset \mathbf{A}_{F,S_{\infty}}$ the half-open unit cube

$$
D_{F,\infty} := \{x \in \mathbf{A}_{F,S_{\infty}}: x = \sum_{1\le i\le r_1+r_2} x_i a_i,\, |x_i|_{v_i} \in [0,1)\}. \tag{A.2.1.1}
$$

We define

$$
D_F := D_{F,\infty} \times \widehat{\mathcal{O}}_F \subset \mathbf{A}_F \tag{A.2.1.2}
$$

and refer to it as the adelic fundamental domain.

Lemma A.2.1.2. Let $F$ be a number field.

(1) The additive topological group $\mathbf{A}_F$ satisfies

$$
\mathbf{A}_F = F + D_F \tag{A.2.1.3}
$$

*where the right side of (A.2.1.3) is the union within $\mathbf{A}_F$ of the additive $F$-translates of the adelic fundamental domain $D_F$ from (A.2.1.2).*

(2) *Upon denoting by $\overline{D}_F$ the closure of $D_F$ in $\mathbf{A}_F$, then for any compact subset $K \subset \mathbf{A}_F$, there exist at most finitely many elements $\xi \in F$ such that*

$$
(\xi + \overline{D}_F) \cap K \ne \varnothing. \tag{A.2.1.4}
$$

We illustrate the example $F = \mathbf{Q}$.

Example A.2.1.3. The additive topological group $\mathbf{A}_{\mathbf{Q}}$ satisfies

$$
\mathbf{A}_{\mathbf{Q}} = \mathbf{Q} + D \tag{A.2.1.5}
$$

## PDF page 546

**546** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

where the right side of (A.2.1.5) is the union within $\mathbf{A}_{\mathbf{Q}}$ of the additive $\mathbf{Q}$-translates of the subset

$$
D := [0,1) \times \widehat{\mathbf{Z}}. \tag{A.2.1.6}
$$

In particular, $\mathbf{A}_{\mathbf{Q}}$ is the union of countably many pre-compact subsets. Moreover, the union in (A.2.1.5) is disjoint.

**A.2.2. Continuous homomorphic sections to the idelic norm.** Recall from Lemma A.1.3.3 and Lemma A.1.3.4 that the idelic norm

$$
|\cdot|_F : \mathrm{GL}_1(\mathbf{A}_F) \to \mathbf{R}_{>0}
$$

is a continuous homomorphism of abelian topological groups, and it descends to the idele class group $C_F$ since $|F^{\times}|_F = 1$ (Product Formula).

In this subsection we present a few constructions of continuous homomorphic sections to the idelic norm; i.e., continuous homomorphisms

$$
s : \mathbf{R}_{>0} \to \mathrm{GL}_1(\mathbf{A}_F)
$$

such that $|\cdot|_F \circ s$ is the identity on $\mathbf{R}_{>0}$. We note that any continuous homomorphic section $s$ to $|\cdot|_F : \mathrm{GL}_1(\mathbf{A}_F) \to \mathbf{R}_{>0}$ also induces a continuous homomorphic section to the idelic norm on $C_F$, by composition with the continuous quotient $\mathrm{GL}_1(\mathbf{A}_F) \to C_F$.

A.2.2.1. *The canonical section.* The topological groups $\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q}})$ and $C_{\mathbf{Q}}$ can be described explicitly. We have an isomorphism of topological groups

$$
\theta : \mathbf{R}^{\times} \times \mathbf{Q}_{>0} \times \widehat{\mathbf{Z}}^{\times} \xrightarrow{\simeq} \mathrm{GL}_1(\mathbf{A}_{\mathbf{Q}}) \tag{A.2.2.1}
$$

given explicitly as $\theta(t,q,h) := tqh$, for $t \in \mathbf{R}^{\times}$, $q \in \mathbf{Q}_{>0}$, $h \in \mathrm{GL}_1(\widehat{\mathbf{Z}})$. It satisfies:

$$
|\theta(t,q,h)|_{\mathbf{Q}} = |t|_{\mathbf{R}} \tag{A.2.2.2}
$$

where $|\cdot|_{\mathbf{R}}$ is the Euclidean absolute value on $\mathbf{R}^{\times}$, which is to say that the idelic norm on $\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q}})$ corresponds on the left side of (A.2.2.1) to the composition of the projection onto $\mathbf{R}^{\times}$, followed by the Euclidean absolute value.

This induces an isomorphism of Hausdorff locally compact abelian groups

$$
\theta : \mathbf{R}_{>0} \times \widehat{\mathbf{Z}}^{\times} \xrightarrow{\simeq} C_{\mathbf{Q}} \tag{A.2.2.3}
$$

Lemma A.2.2.1. The function

$$
s_{\mathbf{Q}} : \mathbf{R}_{>0} \to \mathrm{GL}_1(\mathbf{A}_{\mathbf{Q}}) \tag{A.2.2.4}
$$

*defined as $s_{\mathbf{Q}}(t) := \theta(t,1,1)$, is a canonical continuous section to the idelic norm $|\cdot|_{\mathbf{Q}} : C_{\mathbf{Q}} \to \mathbf{R}_{>0}$.*

Lemma A.2.2.2. *Let $F$ be a number field. The norm homomorphism renders the following diagram of continuous homomorphisms of Hausdorff locally compact abelian groups*

(A.2.2.5)

```latex
\begin{tikzcd}
\mathrm{GL}_1(\mathbf{A}_F) \arrow[r, "|\cdot|_F"]\arrow[d, "N_{F/\mathbf{Q}}"'] & \mathbf{R}_{>0} \arrow[d, equal] \\
\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q}}) \arrow[r, "|\cdot|_{\mathbf{Q}}"'] & \mathbf{R}_{>0}
\end{tikzcd}
```

*commutative, the rightmost vertical arrow being the identity.*

*Moreover, the canonical closed continuous homomorphism*

$$
i_F : \mathrm{GL}_1(\mathbf{A}_{\mathbf{Q}}) \to \mathrm{GL}_1(\mathbf{A}_F) \tag{A.2.2.6}
$$

## PDF page 547

**A.2. ORBITAL STRUCTURES ON ADELES AND IDELES** · **547**

satisfies

$$
N_{F/\mathbf{Q}} \circ i_F = (\cdot)^{[F:\mathbf{Q}]} \tag{A.2.2.7}
$$

*as continuous endomorphisms of $\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q}})$, where the right side in (A.2.2.7) is the endomorphism $g \mapsto g^{[F:\mathbf{Q}]}$.*

Definition A.2.2.3. Let $F$ be a number field. We define the function

$$
s_F : \mathbf{R}_{>0} \to \mathrm{GL}_1(\mathbf{A}_F) \tag{A.2.2.8}
$$

as

$$
s_F := i_F \circ s_{\mathbf{Q}} \circ (\cdot)^{1/[F:\mathbf{Q}]}. \tag{A.2.2.9}
$$

We refer to $s_F$ as the canonical section to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$.

Lemma A.2.2.4. *Let $F$ be a number field. The function $s_F$ from (A.2.2.8) is a continuous homomorphic section to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$. Explicitly, $s_F(t)$ is the idele whose $v$-indexed component, for each Archimedean place $v$, is $t^{1/[F:\mathbf{Q}]}$, and for each non-Archimedean place $v$ is $1$.*

A.2.2.2. *The section along $F_{v_0}^{\times}$, for $v_0$ a choice of Archimedean place.* In the case $F = \mathbf{Q}$, the canonical isomorphism $\theta$ from (A.2.2.3) provides a canonical continuous homomorphic section $s_{\mathbf{Q}}$ to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_{\mathbf{Q}})$ (see Lemma A.2.2.1).

When $F$ is an arbitrary number field other than $\mathbf{Q}$ and an imaginary quadratic field, the number of Archimedean places of $F$ is higher than $1$. Each Archimedean place $v_0 \in S_{\infty}$ induces a continuous section $s_{F,v_0}$ to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$:

Definition A.2.2.5. Let $F$ be a number field. We define the function

$$
s_{F,v_0} : \mathbf{R}_{>0} \to \mathrm{GL}_1(\mathbf{A}_F) \tag{A.2.2.10}
$$

via insertion into $F_{v_0}^{\times}$ preceded by $t \mapsto t^{1/[F_{v_0}:\mathbf{R}]}$ on $\mathbf{R}_{>0}$.

Lemma A.2.2.6. *Let $F$ be a number field. The map $s_{F,v_0}$ from (A.2.2.10) is a continuous homomorphic section to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$.*

Proof. Indeed $\iota_{v_0}^{-1} : \mathbf{R}_{>0} \to T_{v_0}$ is an isomorphism of Hausdorff locally compact abelian groups, and $i_{v_0}$ is a closed injective continuous homomorphism. It follows that $s_{F,v_0}$ is a continuous homomorphism. Moreover, for every $t \in \mathbf{R}_{>0}$, we have $|s_{F,v_0}(t)|_F = |i_{v_0}(\iota_{v_0}^{-1}(t))|_F = |\iota_{v_0}^{-1}(t)|_{v_0}$. If $v_0$ is real, then $|\iota_{v_0}^{-1}(t)|_{v_0} = |t|_{\mathbf{R}} = t$. If $v_0$ is complex, then $|\iota_{v_0}^{-1}(t)|_{v_0} = |t^{1/2}|_{\mathbf{C}} = t$. $\square$

A.2.2.3. *The diagonal section into $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$.* We give one more construction of a section.

Definition A.2.2.7. Let $F$ be a number field. We define the function

$$
s_{F,\delta} : \mathbf{R}_{>0} \to \mathrm{GL}_1(\mathbf{A}_F) \tag{A.2.2.11}
$$

by sending the real number $t \in \mathbf{R}_{>0}$ to the idele $s_{F,\delta}(t)$ whose $v$-indexed component, for every non-Archimedean place $v$ of $F$, is $1$, and for every Archimedean place $v$, it is $t^{1/N_v(r_1+r_2)}$ with $N_v = 1$ if $v$ is real, and $N_v = 2$ if $v$ is complex. We refer to $s_{F,\delta}$ as the diagonal section to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$.

Lemma A.2.2.8. *Let $F$ be a number field. The function $s_{F,\delta}$ is a continuous homomorphic section to the idelic norm.*

Lemma A.2.2.9. *Let $F$ be a number field. For any continuous section $s$ to the idelic norm on $\mathrm{GL}_1(\mathbf{A}_F)$, the continuous homomorphism*

$$
\theta_{F,s} : \mathbf{R}_{>0} \times \mathrm{GL}_1(\mathbf{A}_F)^1 \to \mathrm{GL}_1(\mathbf{A}_F) \tag{A.2.2.12}
$$

*defined as $\theta_{F,s}(t,g_0) := s(t)g_0$, is an isomorphism of Hausdorff locally compact abelian groups.*

## PDF page 548

**548** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

**A.2.3. Fundamental domain of the multiplicative $F^{\times}$-translation action on $\mathrm{GL}_1(\mathbf{A}_F)^1$.** In this subsection we describe a fundamental domain for the continuous left translation action of $F^{\times}$ on $\mathrm{GL}_1(\mathbf{A}_F)^1$, i.e. a relatively compact subset $E \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ with non-empty interior, such that $F^{\times}E = \mathrm{GL}_1(\mathbf{A}_F)^1$, and $\xi E \cap E = \varnothing$ for every $\xi \in F^{\times} - \{1\}$.

A.2.3.1. *The logarithm homomorphism.* In this subsection we recall the structure of the orbit space of $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ under the action of the unit group $\mathcal{O}_F^{\times}$.

Definition A.2.3.1. Let $F$ be a number field. We define the continuous homomorphism

$$
|\cdot|_{\infty} : \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \to \mathbf{R}_{>0} \tag{A.2.3.1}
$$

to be $|\cdot|_{F,S_{\infty}}$ and the closed subgroup

$$
\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 := \{g_{\infty} \in \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) : |g_{\infty}|_{\infty} = 1\} \tag{A.2.3.2}
$$

of $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$.

We define

$$
\mathscr{L} : \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \to \mathbf{R}^{S_{\infty}} \tag{A.2.3.3}
$$

as the map

$$
\mathscr{L}(g_{\infty}) := (\log|g_v|_v)_{v\in S_{\infty}} : \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \to \mathbf{R}^{S_{\infty}} \tag{A.2.3.4}
$$

which is a surjective continuous homomorphism of abelian topological groups. The following is elementary.

Lemma A.2.3.2. *Let $F$ be a number field. Upon defining the hyperplane*

$$
H_{\log} := \{(x_v)_{v\in S_{\infty}} \in \mathbf{R}^{S_{\infty}} : \sum_{v\in S_{\infty}} x_v = 0\} \subset \mathbf{R}^{S_{\infty}} \tag{A.2.3.5}
$$

*the map $\mathscr{L}$ from (A.2.3.3) satisfies the following conditions:*

(1) $\mathscr{L}$ is a continuous group homomorphism, and $\mathscr{L}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1) \subset H_{\log}$.

(2) *$\mathscr{L}$ is a smooth submersion whose kernel is isomorphic, as a Lie group, to the compact Lie group $(\mu_2)^{r_1} \times \mathrm{U}(1)^{r_2}$.*

(3) $\mathscr{L}$ is a proper smooth submersion.

Definition A.2.3.3. Let $F$ be a number field. We define the regulator homomorphism to be the restriction

$$
\mathrm{Reg} : \mathcal{O}_F^{\times} \to H_{\log} \tag{A.2.3.6}
$$

of $\mathscr{L}$ from (A.2.3.3) to $\mathcal{O}_F^{\times} \subset \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$.

Lemma A.2.3.4. *Let $F$ be a number field. The regulator homomorphism satisfies the following conditions:*

(1) *$\mathrm{Reg}(\mathcal{O}_F^{\times})$ is a discrete and co-compact closed subgroup of $H_{\log}$.*

(2) *The kernel $\ker(\mathrm{Reg})$ is the torsion subgroup of $\mathcal{O}_F^{\times}$, which is the finite cyclic group $\mu_F$ of size $w_F$ of the roots of unity contained in $F$.*

(3) *$\mathcal{O}_F^{\times}$ is a finitely generated abelian group, and $\mathcal{O}_F^{\times}/\mu_F$ is finite free of rank $r_1+r_2-1$.*

A.2.3.2. *The idelic fundamental domain $E_F^1$.* Upon denoting

$$
\{\varepsilon_1,\dots,\varepsilon_{r_1+r_2-1}\} \tag{A.2.3.7}
$$

## PDF page 549

**A.2. ORBITAL STRUCTURES ON ADELES AND IDELES** · **549**

a $\mathbf{Z}$-basis for the finite free $\mathbf{Z}$-module $\mathcal{O}_F^{\times}/\mu_F$, for any $g_{\infty} \in \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ there exist unique real numbers $\{x_i\}_{1\le i\le r_1+r_2-1}$ such that

$$
\mathscr{L}(g) = \sum_{i=1}^{r_1+r_2-1} x_i \mathscr{L}(\varepsilon_i) \tag{A.2.3.8}
$$

and a fundamental domain for the left translation action of $\mathscr{L}(\mathcal{O}_F^{\times})$ on $\mathscr{L}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1) \simeq \mathbf{R}^{r_1+r_2-1}$ is given by the parallelotope

$$
P = \left\{\sum_{i=1}^{r_1+r_2-1} x_i \mathscr{L}(\varepsilon_i) : (x_i) \in Q\right\} \tag{A.2.3.9}
$$

where $Q$ is the hypercube

$$
Q := \{(x_i) \in \mathbf{R}^{r_1+r_2-1} : 0 \le x_i < 1\} \subset \mathbf{R}^{r_1+r_2-1}. \tag{A.2.3.10}
$$

Lemma A.2.3.5. *Let $F$ be a hyperplane. The subset $P \subset H_{\log}$ satisfies the following conditions:*

(1) *$P$ is relatively compact with non-empty interior within $H_{\log}$.*

(2) $\mathrm{Reg}(\mathcal{O}_F^{\times})P = H_{\log}$, and for every $\xi \in \mathrm{Reg}(\mathcal{O}_F^{\times})$, $\xi \ne 0$, we have

$$
(\xi + P) \cap P = \varnothing. \tag{A.2.3.11}
$$

The natural map

$$
\mathrm{GL}_1(\mathbf{A}_F) \to \mathrm{Pic}(\mathcal{O}_F)
$$

sends $\mathrm{GL}_1(\mathbf{A}_F)^1$ onto $\mathrm{Pic}(\mathcal{O}_F)$, so there exist ideles

$$
g_1 := 1,\dots,g_{h_F} \in \mathrm{GL}_1(\mathbf{A}_F)^1 \tag{A.2.3.12}
$$

such that their images represent each of the $h_F$ elements of $\mathrm{Pic}(\mathcal{O}_F)$.

Definition A.2.3.6. Let $F$ be a number field, $v_0$ a choice of Archimedean place of $F$. We define

$$
E_0 := \{g \in \mathscr{L}^{-1}(P) : \arg(\iota_{v_0}(g_{v_0})) \in [0,2\pi/w_F)\} \subset \mathscr{L}^{-1}(P) \tag{A.2.3.13}
$$

and

$$
E_F^1 := \bigcup_{i=1}^{h_F} g_i(E_0 \times \widehat{\mathcal{O}}_F^{\times}) \subset \mathrm{GL}_1(\mathbf{A}_F)^1 \subset \mathrm{GL}_1(\mathbf{A}_F) \tag{A.2.3.14}
$$

(If $v_0$ is real, then $\arg(g_{v_0}) \in [0,2\pi/w_F)$ is equivalent to requiring $\iota_{v_0}(g_0)$ is positive, where $\iota_{v_0} : F_{v_0} \simeq \mathbf{R}$ is the unique topological field isomorphism.) We endow $E_F^1$ with the subspace topology and refer to $E_F^1$ as the idelic fundamental domain.

Remark A.2.3.7. The subset $E_F^1$ from (A.2.3.14) is the same as defined in [**CF**, Ch. XV, Def. 4.3.2].

We write each idele $g_i$ from (A.2.3.12) as

$$
g_i = (g_{i,\infty}, g_{i,f}) \tag{A.2.3.15}
$$

with $g_{i,\infty} = \mathrm{pr}_{\infty}(g_i) \in \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ and $g_{i,f} = \mathrm{pr}_f(g_i) \in \mathrm{GL}_1(\mathbf{A}_F^f)$, where $\mathrm{pr}_{\infty} : \mathrm{GL}_1(\mathbf{A}_F) \to \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ and $\mathrm{pr}_f : \mathrm{GL}_1(\mathbf{A}_F) \to \mathrm{GL}_1(\mathbf{A}_F^f)$ are, respectively, the continuous group homomorphisms induced by the first projection $\mathbf{A}_F \to \mathbf{A}_{F,S_{\infty}}$ and the second projection $\mathbf{A}_F \to \mathbf{A}_F^f$.

The subset $E_F^1 \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ from (A.2.3.14) is therefore of the form

$$
E_F^1 = (E_0 \times \widehat{\mathcal{O}}_F^{\times}) \cup (g_{2,\infty}E_0 \times g_{2,f}\widehat{\mathcal{O}}_F^{\times}) \cup \cdots \cup (g_{h_F,\infty}E_0 \times g_{h_F,f}\widehat{\mathcal{O}}_F^{\times}) \subset \mathrm{GL}_1(\mathbf{A}_F)^1. \tag{A.2.3.16}
$$

## PDF page 550

**550** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

A.2.3.3. *Topological structure of $E_0$.* We now focus on $E_0$ (defined in (A.2.3.13)).

Lemma A.2.3.8. *The subset $E_0 \subset \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ satisfies the following conditions:*

(1) *$E_0$ is relatively compact in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ and $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ and its interior within $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ is non-empty.*

(2) $\mathcal{O}_F^{\times} E_0 = \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$, and for every $\xi \in \mathcal{O}_F^{\times}$, $\xi \ne 1$, we have

$$
\xi E_0 \cap E_0 = \varnothing \tag{A.2.3.17}
$$

*where $\mathcal{O}_F^{\times}$ is diagonally embedded into $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$. Moreover, $\mathscr{L}^{-1}(P) = \mu_F E_0$.*

(3) *Upon denoting by $\overline{E}_0$ the closure of $E_0 \subset \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$, for any compact subset $K \subset \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ there exist at most finitely many elements $\xi \in \mathcal{O}_F^{\times}$ such that*

$$
\xi \overline{E}_0 \cap \overline{E}_0 \ne \varnothing. \tag{A.2.3.18}
$$

Due to lack of a reference for a proof in standard books, we give a proof below although the result is very classical.

Proof. Recall that $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$, defined in (A.2.3.1), is the closed subgroup of $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \simeq \prod_{v\in S_{\infty}} F_v^{\times}$ defined as

$$
\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 = \{g_{\infty} \in \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) : |g_{\infty}|_{\infty} = 1\}
$$

which is the kernel of the continuous group homomorphism $|\cdot|_{\infty} := \prod_{v\in S_{\infty}} |\cdot|_v : \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \to \mathbf{R}_{>0}$.

Further recall that the continuous group homomorphism

$$
\mathscr{L} : \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \to \mathbf{R}^{S_{\infty}}
$$

from (A.2.3.3) is a smooth and surjective.

The parallelotope $P$ from (A.2.3.9) within the hyperplane $H_{\log}$ is relatively compact and has non-empty interior (see Lemma A.2.3.5(1)), so the pre-image $\mathscr{L}^{-1}(P)$ also has non-empty interior within the pre-image $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 = \mathscr{L}^{-1}(H_{\log})$.

We now choose an enumeration of the finite set of Archimedean places of $F$:

$$
S_{\infty} = \{v_0,v_1,\dots,v_{r_1+r_2-1}\} \tag{A.2.3.19}
$$

where $v_0$ is a choice of Archimedean place made to define the closed subgroup

$$
T_{v_0} := s_{F,v_0}(\mathbf{R}_{>0}) \subset \mathrm{GL}_1(\mathbf{A}_F)
$$

induced by the $v_0$-section $s_{F,v_0}$ to the idelic norm $|\cdot|_F$ (see Definition A.2.2.5).

The choice of the ordering in (A.2.3.19), along with that of isomorphisms of topological fields $\iota_v : F_v \simeq \mathbf{R}$ if $v$ is real, $\iota_v : F_v \simeq \mathbf{C}$ if $v$ is complex (the same which, for $v = v_0$, were used in the definition of $s_{F,v_0}$ in Definition A.2.2.10) induces an isomorphism of $\mathbf{R}$-vector spaces $\mathbf{R}^{S_{\infty}} \simeq \mathbf{R}^{r_1+r_2}$ (upon choosing within each $F_v$ the $\mathbf{R}$-linear basis given by $1$ if $v$ is real, and $1$, $\iota_v^{-1}(i)$ if $v$ is complex).

The subset $E_0 \subset \mathscr{L}^{-1}(P)$ was defined by the condition

$$
\arg(\iota_{v_0}(g_{v_0})) \in [0,2\pi/w_F)
$$

for $g \in \mathscr{L}^{-1}(P)$ in (A.2.3.13) of Definition A.2.3.6. In other words, we have

$$
E_0 = \mathscr{L}^{-1}(P) \cap \left(\iota_{v_0}^{-1}(\mathbf{R}_{>0}) \times \prod_{k=1}^{r_1+r_2-1} F_{v_k}^{\times}\right). \tag{A.2.3.20}
$$

If $v_0$ is complex, then $\arg(\iota_{v_0}(g_{v_0})) \in [0,2\pi/w_F)$ is equivalent to requiring that $\iota_{v_0}(g_{v_0})$ be a complex number within the sector

$$
\mathbf{R}_{>0} e^{i[0,2\pi/w_F)} \subset \mathbf{C}.
$$

## PDF page 551

**A.2. ORBITAL STRUCTURES ON ADELES AND IDELES** · **551**

In other words, we have

$$
E_0 = \mathscr{L}^{-1}(P) \cap \left(\iota_{v_0}^{-1}(\mathbf{R}_{>0} e^{i[0,2\pi/w_F)}) \times \prod_{k=1}^{r_1+r_2-1} F_{v_k}^{\times}\right). \tag{A.2.3.21}
$$

(1): If $v_0$ is real, we define $U_0 := \iota_{v_0}^{-1}(\mathbf{R}_{>0}) \times \prod_{k=1}^{r_1+r_2-1} F_{v_k}^{\times}$. If $v_0$ is complex, we define $U_0 := \iota_{v_0}^{-1}(\mathbf{R}_{>0} e^{i(0,2\pi/w_F)}) \times \prod_{k=1}^{r_1+r_2-1} F_{v_k}^{\times}$. In either case, $U_0 \subset \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ is open and non-empty. It follows that $U_0 \cap \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ is open in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$, and it is non-empty since it contains

$$
g_{\infty} := (\iota_{v_0}^{-1}(\zeta a)\varepsilon, \prod_{k=1}^{r_1+r_2-1} \{a_k \varepsilon\})
$$

where $\zeta = 1$ if $v_0$ is real, and $\zeta \in e^{i(0,2\pi/w_F)}$ if $v_0$ is complex, with $a, a_k \in \mathbf{R}_{>0} - \{1\}$ chosen so as to have $a^{N_0} \prod_{k=1}^{r_1+r_2-1} a_k^{N_k} = 1$ where, for each $0 \le k \le r_1+r_2-1$, $N_k = 1$ if $v_k$ is real, and $N_k = 2$ if $v_k$ is complex, and with $\varepsilon \in \mathcal{O}_F^{\times}/\mu_F$.

By Lemma A.2.3.5(2), we may and do choose $\varepsilon \in \mathcal{O}_F^{\times}/\mu_F$ so as to have $\mathscr{L}(g_{\infty}) \in \mathrm{Int}(P)$, the interior of $P$ in $H_{\log}$.

By Lemma A.2.3.5(1), $P$ has non-empty interior $\mathrm{Int}(P)$ in $H_{\log}$. The pre-image $\mathscr{L}^{-1}(\mathrm{Int}(P))$ is open and non-empty in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 = \mathscr{L}^{-1}(H_{\log})$ since $\mathscr{L}$ maps $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ surjectively and smoothly onto $H_{\log}$.

In light of (A.2.3.20) and (A.2.3.21), $\mathscr{L}^{-1}(\mathrm{Int}(P)) \cap (U_0 \cap \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1)$ is contained in $E_0$, and it is open and non-empty in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ by the foregoing since it contains $\zeta' g_{\infty}$ for some $\zeta' \in \mu_F$. It follows that $E_0$ has non-empty interior in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$.

By Lemma A.2.3.2(3), $\mathscr{L}$ is a proper smooth submersion, and hence $\mathscr{L}^{-1}(P)$ is relatively compact in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$. Since $E_0 \subset \mathscr{L}^{-1}(P)$, then $E_0$ is also relatively compact in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$. As $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ is closed in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$, $E_0$ is relatively compact in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$.

(2): Since $\mathscr{L}(\mathcal{O}_F^{\times}) = \mathrm{Reg}(\mathcal{O}_F^{\times})$ tessellates $H_{\log} = \mathscr{L}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1)$ by copies of $P$ by Lemma A.2.3.5(2), and since $\mathcal{O}_F^{\times} \to \mathscr{L}(\mathcal{O}_F^{\times})$ is surjective with kernel $\mu_F \subset \mathcal{O}_F^{\times}$ by Lemma A.2.3.4(2), then $(\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}^{-1}(P) = \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$. Indeed, we have

$$
\mathscr{L}((\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}^{-1}(P)) = \mathscr{L}(\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}(\mathscr{L}^{-1}(P)) = \mathscr{L}(\mathcal{O}_F^{\times})P = \mathrm{Reg}(\mathcal{O}_F^{\times})P = H_{\log}
$$

by Lemma A.2.3.5(2) and since $\mathscr{L}^{-1}(P)$ is stable under the action of $\ker(\mathscr{L})$ (and hence of $\mu_F$), then $(\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}^{-1}(P)$ is stable under the action of $\mathcal{O}_F^{\times}\ker(\mathscr{L})$ and since $\mathcal{O}_F^{\times}\ker(\mathscr{L}) = \mathscr{L}^{-1}(\mathscr{L}(\mathcal{O}_F^{\times}))$, then $(\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}^{-1}(P)$ contains $\mathscr{L}^{-1}(\mathscr{L}((\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}^{-1}(P))) = \mathscr{L}^{-1}(H_{\log}) = \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$, and hence $(\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}^{-1}(P) = \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$.

Since $\mathcal{O}_F^{\times} \cap \ker(\mathscr{L}) = \mu_F$, the union $(\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}^{-1}(P)$ is disjoint, i.e. the finite free abelian group $\mathcal{O}_F^{\times}/\mu_F$ tessellates $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ by copies of $\mathscr{L}^{-1}(P)$.

Since $\mu_F$ is cyclic of size $w_F$, it acts on $F_{v_0}^{\times}$ with fundamental domain $\iota_{v_0}^{-1}(\mathbf{R}_{>0})$ if $v_0$ is real (in which case $\mu_F = \{\pm 1\}$), and $\iota_{v_0}^{-1}(\mathbf{R}_{>0} e^{i[0,2\pi/w_F)})$ as fundamental domain, if $v_0$ is complex. It follows that we have $\mu_F E_0 = \mathscr{L}^{-1}(P)$, the finite union being disjoint.

We therefore have (since $\mu_F$ splits off as a direct factor of $\mathcal{O}_F^{\times}$, being $\mathcal{O}_F^{\times}$ a finitely generated abelian group with torsion group $\mu_F$) $\mathcal{O}_F^{\times} E_0 = (\mathcal{O}_F^{\times}/\mu_F)\mu_F E_0 = (\mathcal{O}_F^{\times}/\mu_F)\mathscr{L}^{-1}(P) = \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$, the union being disjoint.

(3): In light of (1) and (2), it is enough to assume $K = \overline{E}_0$, and since $\mu_F$ is finite, it is enough to prove the same assertion with $\mathscr{L}^{-1}(P)$ in place of $E_0$. This in turn reduces to the same assertion for $P \subset H_{\log}$ and its closure, and $\mathrm{Reg}(\mathcal{O}_F^{\times})$ acting on $H_{\log}$. Upon fixing a $\mathbf{Z}$-basis of units for the torsion-free quotient of $\mathcal{O}_F^{\times}$, this in turn reduces to the case of the standard full lattice $\mathbf{Z}^{r_1+r_2-1}$ acting on the Euclidean space $\mathbf{R}^{r_1+r_2-1}$, with $P$ replaced by $[0,1)^{r_1+r_2-1}$. $\square$

## PDF page 552

**552** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

A.2.3.4. *Global description of $\mathrm{GL}_1(\mathbf{A}_F)$.* With no mention of the fundamental domains $E_F^1$ and $E_F$, we describe, in this subsection, the topological group $\mathrm{GL}_1(\mathbf{A}_F)$. Recall that we write $\widehat{\mathcal{O}}_F^{\times}$ for $\mathrm{GL}_1(\widehat{\mathcal{O}}_F)$, and not for the closure of $\mathcal{O}_F^{\times}$ in $\mathrm{GL}_1(\mathbf{A}_F)$.

Proposition A.2.3.9. *Let $F$ be a number field. The following sequences*

$$
1 \to \mathcal{O}_F^{\times} \to \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \times F^{\times} \times \widehat{\mathcal{O}}_F^{\times} \to F^{\times}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \times \widehat{\mathcal{O}}_F^{\times}) \to 1 \tag{A.2.3.22}
$$

*where the unit group $\mathcal{O}_F^{\times}$ is embedded diagonally as a discrete subgroup, and*

$$
1 \to F^{\times}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \times \widehat{\mathcal{O}}_F^{\times}) \to \mathrm{GL}_1(\mathbf{A}_F) \to \mathrm{Pic}(\mathcal{O}_F) \to 1 \tag{A.2.3.23}
$$

*are short exact sequences of Hausdorff locally compact abelian groups, in the strict sense. The short exact sequence in (A.2.3.23) induces the short exact sequence of Hausdorff locally compact abelian groups*

$$
1 \to F^{\times}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 \times \widehat{\mathcal{O}}_F^{\times}) \to \mathrm{GL}_1(\mathbf{A}_F)^1 \to \mathrm{Pic}(\mathcal{O}_F) \to 1 \tag{A.2.3.24}
$$

*which is exact in the strict sense.*

A.2.3.5. *Topological structure of $E_F^1$.*

Proposition A.2.3.10. *The subset $E \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ satisfies the following conditions:*

(1) *$E_F^1$ is relatively compact with non-empty interior in $\mathrm{GL}_1(\mathbf{A}_F)^1$.*

(2) We have

$$
F^{\times} E_F^1 = \mathrm{GL}_1(\mathbf{A}_F)^1 \tag{A.2.3.25}
$$

and for every $\xi \in F^{\times}$, $\xi \ne 1$, we have

$$
\xi E_F^1 \cap E_F^1 = \varnothing. \tag{A.2.3.26}
$$

(3) *Upon denoting by $\overline{E}_F^1 \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ the closure of $E_F^1$, for any compact subset $K \subset \mathrm{GL}_1(\mathbf{A}_F)^1$, there exist at most finitely many elements $\xi \in F^{\times}$ such that:*

$$
\xi \overline{E}_F^1 \cap K \ne \varnothing. \tag{A.2.3.27}
$$

Proof. (1): The subset $E_F^1 \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ was defined upon choosing $g_1 = 1, g_2,\dots,g_{h_F} \in \mathrm{GL}_1(\mathbf{A}_F)^1$ lifting the $h_F$ elements of $\mathrm{Pic}(\mathcal{O}_F)$ and defining $E_F^1 := (E_0 \times \widehat{\mathcal{O}}_F^{\times}) \cup g_2(E_0 \times \widehat{\mathcal{O}}_F^{\times}) \cup \cdots \cup g_{h_F}(E_0 \times \widehat{\mathcal{O}}_F^{\times})$. By compactness and openness of $\widehat{\mathcal{O}}_F^{\times}$ in $\mathrm{GL}_1(\mathbf{A}_F^f)$, $E_F^1$ is relatively compact, and its interior in $\mathrm{GL}_1(\mathbf{A}_F)^1$ is non-empty since $E_0$ has non-empty interior in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$ by Lemma A.2.3.8(1).

(2): By Proposition A.2.3.9, we have a strictly exact sequence of continuous homomorphisms of Hausdorff locally compact abelian groups

$$
1 \to F^{\times}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 \times \widehat{\mathcal{O}}_F^{\times}) \to \mathrm{GL}_1(\mathbf{A}_F)^1 \to \mathrm{Pic}(\mathcal{O}_F) \to 1 \tag{A.2.3.28}
$$

and hence to see that (A.2.3.25) holds and the union is disjoint, it is enough to check that we have

$$
F^{\times}(E_0 \times \widehat{\mathcal{O}}_F^{\times}) = F^{\times}(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \times \widehat{\mathcal{O}}_F^{\times})
$$

within $\mathrm{GL}_1(\mathbf{A}_F)^1$, which follows from $\mathcal{O}_F^{\times} E_0 = \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$, which is given by Lemma A.2.3.8(2). The disjointness condition for non-trivial $F^{\times}$-translates in (A.2.3.26) follows from (A.2.3.17) of Lemma A.2.3.8(2) upon observing that $\xi(\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 \times \widehat{\mathcal{O}}_F^{\times}) \cap (\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 \times \widehat{\mathcal{O}}_F^{\times}) = \varnothing$ within $\mathrm{GL}_1(\mathbf{A}_F)^1$ if $\xi$ is not a global unit.

(3): In light of (1) and (2), it is enough to treat the case $K = \overline{E}_F^1$. Since $\mathrm{Pic}(\mathcal{O}_F)$ is finite by Theorem A.1.4.3(3), it is enough to prove, in light of (A.2.3.16), that, upon denoting by $\overline{E}_0$ the closure of $E_0 \subset \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$, there exist at most finitely many elements $\xi \in \mathcal{O}_F^{\times}$ such that $\xi \overline{E}_0 \cap \overline{E}_0 \ne \varnothing$. This is Lemma A.2.3.8(3). $\square$

## PDF page 553

**A.2. ORBITAL STRUCTURES ON ADELES AND IDELES** · **553**

A.2.3.6. *Fundamental domain $E_F$ for the $F^{\times}$-action on $\mathrm{GL}_1(\mathbf{A}_F)$.*

Lemma A.2.3.11. *Let $F$ be a number field. Let $s_{\infty}$ be any continuous homomorphic section to the continuous homomorphism $|\cdot|_{\infty} : \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \to \mathbf{R}_{>0}$. Then*

$$
\mathbf{R}_{>0} \times \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 \to \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})
$$

*defined by $(t,g^1) \mapsto s_{\infty}(t)g^1$ is an isomorphism of Lie groups.*

The following is immediate from Proposition A.2.3.10(2).

Lemma A.2.3.12. *Let $F$ be a number field. Let $s_{\infty}$ be any continuous homomorphic section to the continuous homomorphism $|\cdot|_{\infty} : \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \to \mathbf{R}_{>0}$. The natural map*

$$
F^{\times} \times \mathbf{R}_{>0} \times E_F^1 \to \mathrm{GL}_1(\mathbf{A}_F)
$$

*via $(\xi,t,g_0) \mapsto \xi s_{\infty}(t) g_0$ is bijective.*

A.2.3.7. *Product loci, interiors and compactness.* For each Archimedean place, we denote by

$$
H_v := \{x \in \mathbf{A}_{F,S_{\infty}} : x_v = 0\} \tag{A.2.3.29}
$$

the hyperplane of those elements $x \in \mathbf{A}_{F,S_{\infty}}$ whose coordinate indexed by the Archimedean place $v$ is zero.

Lemma A.2.3.13. *We fix an Archimedean place $v_0$ of $F$, and let $T_{v_0} \subset F_{v_0}^{\times} \hookrightarrow \mathbf{A}_{F,S_{\infty}}^{\times}$ be the canonical copy of $\mathbf{R}_{>0}$. Let $K_{v_0} \subset T_{v_0,\infty}$ be a compact subset.*

(1) *The subset $K_{v_0} \cdot \overline{E}_0 \subset \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ is compact. If $K_{v_0}$ has non-empty interior in $T_{v_0,\infty}$, then so does $K_{v_0} \cdot \overline{E}_0$ in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$.*

(2) We have $(K_{v_0} \cdot \overline{E}_0) \cap (\bigcup_{v\in S_{\infty}} H_v) = \varnothing$.

(3) *If $K_{v_0}$ has non-empty interior in $T_{v_0,\infty}$, then so does $K_{v_0} \cdot \overline{E}_0$ in $\mathbf{A}_{F,S_{\infty}}$.*

Proof. (1): Compactness of $K_{v_0} \cdot \overline{E}_0$ follows from Lemma A.2.3.8(1). The interior of $K_{v_0} \cdot \overline{E}_0$ in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ contains the open subset

$$
\mathrm{Int}_{T_{v_0,\infty}}(K_{v_0}) \times \mathrm{Int}_{\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1}(\overline{E}_0) \subset T_{v_0,\infty} \times \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1 = \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}).
$$

If $\mathrm{Int}_{T_{v_0,\infty}}(K_{v_0})$ is non-empty then since $\mathrm{Int}_{\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1}(\overline{E}_0) = \mathrm{Int}_{\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1}(E_0)$ is also non-empty by Lemma A.2.3.8(1), so is $\mathrm{Int}_{T_{v_0,\infty}}(K_{v_0}) \cdot \mathrm{Int}_{\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1}(\overline{E}_0) \subset \mathrm{Int}_{\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})}(K_{v_0} \cdot \overline{E}_0)$.

(2): Since $K_{v_0} \subset T_{v_0,\infty}$ and $\overline{E}_0 \subset \mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})^1$, we have $K_{v_0} \cdot \overline{E}_0$ is entirely contained within $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$, and the complement of $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ is $\bigcup_{v\in S_{\infty}} H_v$.

(3): Clearly $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}}) \simeq \prod_{v\in S_{\infty}} F_v^{\times}$ is open in $\mathbf{A}_{F,S_{\infty}}$. If $K_{v_0} \subset T_{v_0,\infty}$ is a compact subset with non-empty interior in $T_{v_0,\infty}$, then by (1) we have that the interior of $K_{v_0} \cdot \overline{E}_0$ in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ is non-empty, and since it is open, it is open and non-empty also in $\mathbf{A}_{F,S_{\infty}}$ because $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ is open in $\mathbf{A}_{F,S_{\infty}}$. The interior

$$
\mathrm{Int}_{\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})}(K_{v_0} \cdot \overline{E}_0)
$$

formed in $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ coincides with the interior $\mathrm{Int}_{\mathbf{A}_{F,S_{\infty}}}(K_{v_0} \cdot \overline{E}_0)$ formed within $\mathbf{A}_{F,S_{\infty}}$ by compactness of $K_{v_0}\overline{E}_0$ and openness of $\mathrm{GL}_1(\mathbf{A}_{F,S_{\infty}})$ in $\mathbf{A}_{F,S_{\infty}}$. $\square$

**A.2.4. Fundamental domain for $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$ and $C_{F,S}$.** In this subsection we construct an $S$-local analog of the fundamental domain $D_F$ from (A.2.1.2) for the $F$-action on $\mathbf{A}_F$, i.e. a fundamental domain for the continuous additive translation action by $\mathcal{O}_{F,S}$ on $\mathbf{A}_{F,S}$, and for the $\mathcal{O}_{F,S}^{\times}$-action on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

## PDF page 554

**554** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

A.2.4.1. *Fundamental domain for the additive $\mathcal{O}_{F,S}$-action on $\mathbf{A}_{F,S}$.* We recall that for $F$ a number field, and $S$ a finite set of places of $F$ containing all the Archimedean places, we denote by $S_f$ the subset of all finite places of $F$ contained in $S$, i.e. $S_f := S \cap \Sigma_{F,f}$.

Definition A.2.4.1. Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places of $F$. We fix a $\mathbf{Z}$-basis $\{a_1,\dots,a_d\} \subset \mathcal{O}_F$ of the finite free $\mathbf{Z}$-module $\mathcal{O}_F$, with $d := [F:\mathbf{Q}]$ and enumerate the infinite places of $F$ as $v_1,\dots,v_{r_1+r_2}$. We denote by $D_{F,\infty} \subset \mathbf{A}_{F,S_{\infty}}$ the half-open unit cube from (A.2.1.1) relative to $\{a_1,\dots,a_d\}$.

We define $D_{F,S} \subset \mathbf{A}_{F,S}$ to be

$$
D_{F,S} := D_{F,\infty} \times \prod_{v\in S\cap \Sigma_{F,f}} \mathcal{O}_{F_v} \tag{A.2.4.1}
$$

and refer to $D_{F,S}$ as the $S$-adelic fundamental domain.

Lemma A.2.4.2. *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places of $F$.*

(1) The additive topological group $\mathbf{A}_{F,S}$ satisfies

$$
\mathbf{A}_{F,S} = \mathcal{O}_{F,S} + D_{F,S} \tag{A.2.4.2}
$$

*where the right side of (A.2.4.2) is the union within $\mathbf{A}_{F,S}$ of the additive $\mathcal{O}_{F,S}$-translates of the adelic fundamental domain $D_{F,S}$ from (A.2.4.1).*

(2) *Upon denoting by $\overline{D}_{F,S}$ the closure of $D_{F,S}$ in $\mathbf{A}_{F,S}$, then for any compact subset $K \subset \mathbf{A}_{F,S}$, there exist at most finitely many elements $\xi \in \mathcal{O}_{F,S}$ such that*

$$
(\xi + \overline{D}_{F,S}) \cap K \ne \varnothing. \tag{A.2.4.3}
$$

Proof. (1): This is a consequence of strong approximation for $\mathbf{A}_F$.

(2): As in the proof of Lemma A.2.1.2(2), it is enough to check that, upon calling $\overline{D}_{F,\infty}$ the closure of $D_{F,\infty}$ from (A.2.1.1) in $\mathbf{A}_{F,S_{\infty}}$, for any compact subset $K \subset \mathbf{A}_{F,S_{\infty}}$ there exist at most finitely many elements $\xi \in \mathcal{O}_F$ such that $(\xi + \overline{D}_{F,\infty}) \cap K \ne \varnothing$. Upon fixing an $\mathbf{R}$-basis for $\mathbf{A}_{F,S_{\infty}} = F \otimes_{\mathbf{Q}} \mathbf{R}$ induced by an integral $\mathbf{Z}$-basis for $\mathcal{O}_F$, say $\{e_1,\dots,e_{[F:\mathbf{Q}]}\}$, the $\mathbf{R}$-linear isomorphism $\mathbf{A}_{F,S_{\infty}} \simeq \mathbf{R}^{[F:\mathbf{Q}]}$ induced by this choice of basis sends $\mathcal{O}_F \subset \mathbf{A}_{F,S_{\infty}}$ to $\mathbf{Z}^{[F:\mathbf{Q}]} = \sum_{1\le i\le [F:\mathbf{Q}]} \mathbf{Z} e_i$. The subset $D_{F,\infty} \subset \mathbf{A}_{F,S_{\infty}}$ is sent homeomorphically onto $[0,1)^{[F:\mathbf{Q}]}$, and (2) follows. $\square$

A.2.4.2. *Fundamental domain for the multiplicative $\mathcal{O}_{F,S}^{\times}$-action on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.* We denote by $w_{F,S}$ the size of the finite torsion subgroup of $\mathcal{O}_{F,S}^{\times}$. We note that $w_{F,S} = w_F$, since the torsion subgroup of $\mathcal{O}_{F,S}^{\times}$ is $\mu_F$ itself, the finite cyclic group of roots of unity contained in $F$.

We call $g_1 := 1,\dots,g_{h_{F,S}}$ a set of representatives within $\mathrm{GL}_1(\mathbf{A}_{F,S})^1 \times \prod_{v\notin S} \mathcal{O}_{F_v}^{\times}$ of the $h_{F,S}$ ideal classes in the finite abelian group $\mathrm{Pic}(\mathcal{O}_{F,S})$.

Definition A.2.4.3. Let $F$ be a number field, $v_0$ a choice of Archimedean place of $F$, $S$ a finite set of places of $F$ containing all the Archimedean places. We denote by $S_f$ the intersection $S \cap \Sigma_{F,f}$. We define

$$
E_{F,S}^1 := \bigcup_{1\le i\le h_{F,S}} g_i(E_{S,0} \times \prod_{v\notin S} \mathcal{O}_{F_v}^{\times}) \subset \mathrm{GL}_1(\mathbf{A}_{F,S})^1 \times \prod_{v\notin S} \mathcal{O}_{F_v}^{\times} = \mathrm{GL}_1(\mathbf{A}_{F,S} \times \prod_{v\notin S} \mathcal{O}_{F_v})^1 \subset \mathrm{GL}_1(\mathbf{A}_F)^1 \tag{A.2.4.4}
$$

where $E_{S,0}$ is defined, upon choosing an Archimedean place $v_0$ of $F$, as:

$$
E_{S,0} := \{g \in \mathscr{L}_S^{-1}(P_S) : \arg(\iota_{v_0}(g_{v_0})) \in [0,2\pi/w_F)\} \subset \mathscr{L}_S^{-1}(P_S) \tag{A.2.4.5}
$$

where $w_F$ is the size of the finite abelian group $\ker(\mathscr{L}_S) \cap \mathcal{O}_{F,S}^{\times} = \mu_F$, and with:

$$
\mathscr{L}_S : \mathrm{GL}_1(\mathbf{A}_{F,S}) \to \mathbf{R}^S \tag{A.2.4.6}
$$

## PDF page 555

**A.3. HAAR MEASURES** · **555**

defined as:

$$
\mathscr{L}_S(g) := (\log |g_v|_v)_{v\in S} \tag{A.2.4.7}
$$

and, upon choosing an integral basis $\{\varepsilon_1,\dots,\varepsilon_{|S|-1}\}$ for $\mathcal{O}_{F,S}^{\times}$, $P_S$ is the parallelotope in the hyperplane $H_S := \{x\in \mathbf{R}^S : \sum_{v\in S}x_v = 0\}$ of $\mathbf{R}^S$ defined as:

$$
P_S := \sum_{1\le i\le |S|-1}[0,1)\mathscr{L}_S(\varepsilon_i) \subset H_S. \tag{A.2.4.8}
$$

We endow $E^1_{F,S}$ with the subspace topology. We refer to $E^1_{F,S}$ as the $S$-idelic *fundamental domain*.

The following is an analog of Proposition A.2.3.10, and is proved in a closely analogous manner.

Proposition A.2.4.4. *The subsets $E_{S,0}\subset \mathrm{GL}_1(\mathbf{A}_{F,S})^1$, and $E^1_{F,S}\subset \mathrm{GL}_1(\mathbf{A}_F)^1$, satisfy the following conditions:*

(1) *$E_{S,0}$ is relatively compact with non-empty interior in $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.*

(2) We have

$$
\mathcal{O}_{F,S}^{\times}E_{S,0} = \mathrm{GL}_1(\mathbf{A}_{F,S})^1 \tag{A.2.4.9}
$$

*and for every $\xi\in \mathcal{O}_{F,S}^{\times}$, $\xi\ne 1$, we have*

$$
\xi E_{S,0}\cap E_{S,0} = \varnothing. \tag{A.2.4.10}
$$

(3) *Upon denoting by $\overline{E}_{S,0}\subset \mathrm{GL}_1(\mathbf{A}_{F,S})^1$ the closure of $E_{S,0}$, for any compact subset $K\subset \mathrm{GL}_1(\mathbf{A}_{F,S})^1$, there exist at most finitely many elements $\xi\in \mathcal{O}_{F,S}^{\times}$ such that:*

$$
\xi\overline{E}_{S,0}\cap K\ne\varnothing. \tag{A.2.4.11}
$$

(4) $E^1_{F,S}$ *is a fundamental domain for the continuous left-translation action of* $\mathcal{O}_{F,S}^{\times}$ *on* $\mathrm{GL}_1(\mathbf{A}_{F,S})^1\times\prod_{v\notin S}\mathcal{O}_{F_v}^{\times}$.

Remark A.2.4.5. For all large enough $S$ we have $\mathrm{Pic}(\mathcal{O}_{F,S}) = 1$, and so

$$
\mathcal{O}_{F,S}^{\times}\cdot E^1_{F,S} = \mathrm{GL}_1(\mathbf{A}_F)^1
$$

since $C_{F,S} = C_F$, compatibly with idelic norms and $S$-idelic norms.

**A.3. Haar measures**

In this section we normalize Haar measures on $\mathbf{A}_F$, $\mathrm{GL}_1(\mathbf{A}_F)$ and their $S$-local analogs $\mathbf{A}_{F,S}$, respectively $\mathrm{GL}_1(\mathbf{A}_{F,S})$, along with certain closed subgroups.

The following section will assume knowledge of Haar measures and the Fourier transform on a Hausdorff locally compact abelian group and its basic properties, for which we refer the reader to §D.1.1.

**A.3.1. Tamagawa measure on $\mathbf{A}_F$.** As an additive abelian topological group, $\mathbf{A}_F$ is Hausdorff and locally compact. As such, it carries a left- and right-invariant Haar measure. Since it is commutative, it is unimodular.

Definition A.3.1.1. Let $F$ be a number field. Denote by $\nu$ the unique Haar measure on $\mathbf{A}_F$ satisfying the condition:

$$
\bar{\nu}(\mathbf{A}_F/F) = 1 \tag{A.3.1.1}
$$

where $\bar{\nu}$ is the Haar measure induced on $\mathbf{A}_F/F$ by $\nu$ on $\mathbf{A}_F$ and counting measure on $F$. We refer to $\nu$ as the Tamagawa measure on $\mathbf{A}_F$, or *additive Tamagawa measure*. For any finite set $S$ of places of $F$ containing the Archimedean places we define $\nu_S$ on $\mathbf{A}_{F,S} = \prod_{v\in S}F_v$ similarly by using $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$ in place of $\mathbf{A}_F/F$.

## PDF page 556

**556** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

The Tamagawa measure on $\mathbf{A}_F$ can be described explicitly as follows. Recall first that for $G$ a Hausdorff locally compact abelian group isomorphic to the restricted product $\widehat{\prod}_{i\in I}(G_i,K_i)$, with $I = I_0\times I_1$ with $I_0$ a finite set, where $K_i = 1$ for all $i\in I_0$ and $K_i\subset G_i$ is a compact open subgroup for every $i\in I_1$, and for $\mu_{G_i}$ Haar measures on each $G_i$ such that $\mu_{G_i}(K_i) = 1$ for all but finitely many $i\in I_1$, there exists a unique Haar measure $\mu_G$ on $G$ such that for every partition $J_1\coprod J_2 = I$ with $J_1$ finite and containing $I_0$, the restriction of $\mu_G$ to the Borel set

$$
\prod_{i\in J_1}G_i\times\prod_{i\in J_2}K_i
$$

is the Radon product $\bigotimes_{i\in I}\mu_{G_i}$. We refer the reader to [RV, Ch.5,Prop.5.5].

Definition A.3.1.2 (Local Additive Tamagawa measures). Let $F$ be a number field, $v\in\Sigma_F$ a place.

(1) If $v$ is a real place, we define $\nu_v$ to correspond to $\mathrm{d}x$ under the unique isomorphism of topological fields $F_v\simeq\mathbf{R}$.

(2) If $v$ is complex, we define $\nu_v$ to correspond to $|\mathrm{d}z\wedge\mathrm{d}\bar{z}| = 2|\mathrm{d}x\wedge\mathrm{d}y|$ via either of the two isomorphisms of topological fields $F_v\simeq\mathbf{C}$.

(3) If $v$ is non-Archimedean, we define $\nu_v$ to be the unique Haar measure on $F_v$ satisfying the condition:

$$
\nu_v(\mathcal{O}_{F_v}) = N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{-1/2} = |\mathrm{disc}(\mathcal{O}_{F_v}/\mathbf{Z}_p)|_p^{1/2} \tag{A.3.1.2}
$$

where $p$ is the residue characteristic of $F_v$ and $N(\mathfrak{a})$ is the $p$-power generating $N_{\mathcal{O}_{F_v}/\mathbf{Z}_p}(\mathfrak{a})$ for a nonzero ideal $\mathfrak{a}$ of $\mathcal{O}_{F_v}$.

We refer to $\nu_v$ as the *local additive Tamagawa measure* on $F_v$.

Lemma A.3.1.3. *Let $F$ be a number field. For every $v\in\Sigma_F$, let $\nu_v$ be the local Tamagawa measure. Let $S$ be a finite set of places of $F$ containing the Archimedean places. Then we have*

$$
\nu = \bigotimes_{v\in\Sigma_F}\nu_v,\quad \nu_S = \bigotimes_{v\in S}\nu_v \tag{A.3.1.3}
$$

as Haar measures $\mathbf{A}_F$ and $\mathbf{A}_{F,S}$ respectively.$^1$

Proof. Since $D_F = D_{F,\infty}\times\widehat{\mathcal{O}}_F$ as per (A.2.1.2), the Haar measure $\nu' := \bigotimes_{v\in\Sigma_F}\nu_v$ restricts to the Borel subset $D_F$ of $\mathbf{A}_{F,S_\infty}\times\widehat{\mathcal{O}}_F$ as the Radon product $\nu_\infty\otimes\nu_f$ where $\nu_\infty = \bigotimes_{v\in S_\infty}\nu_v$ and $\nu_f = \bigotimes_{v\in\Sigma_{F,f}}\nu_v$. Since $\nu'$ is a Haar measure on $\mathbf{A}_F$, there exists a unique real number $c > 0$ such that $\nu = c\nu'$. Since

$$
\nu_f(\widehat{\mathcal{O}}_F) = \prod_{p\in\Pi}\prod_{v\mid p}N_{F_v/\mathbf{Q}_p}(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{-1/2} = N_{F/\mathbf{Q}}(\mathfrak{d}_{F/\mathbf{Q}})^{-1/2}
$$

and $\nu_\infty(D_{F,\infty}) = N_{F/\mathbf{Q}}(\mathfrak{d}_{F/\mathbf{Q}})^{1/2} = |\mathrm{disc}(K/\mathbf{Q})|^{1/2}$ by [CF, Ch. XV, Lemma 4.1.4], we have $c = 1$ since $\nu(D_F) = \bar{\nu}(\mathbf{A}_F/F) = 1$ via Theorem C.4.4.3 applied to the characteristic function of $D_F\subset\mathbf{A}_F$. $\square$

Lemma A.3.1.4. *Let $F$ be a number field. Let $\mu$ be an arbitrary Haar measure on $\mathbf{A}_F$. For any idele $g\in\mathrm{GL}_1(\mathbf{A}_F)$ and any Borel set $B\subset\mathbf{A}_F$, we have*

$$
\mu(gB) = |g|_F\,\mu(B). \tag{A.3.1.4}
$$

Proof. This is [CF, Ch. XV, Lemma 4.1.2]. $\square$

$^1$Double-check for the $S$-local case.

## PDF page 557

**A.3. HAAR MEASURES** · **557**

A.3.1.1. *Self-duality of local additive Tamagawa measures.* We now discuss calculations that identify the local Tamagawa measures chosen in Definition A.3.1.2 on each local field $F_v$, for $F$ a number field, with its own Plancherel measure with respect to an associated choice of non-trivial additive continuous character of $F_v$.

On any Hausdorff locally compact abelian group, there exists a unique Haar measure up to a nonzero constant multiplier, a positive real number. As recalled in Lemma D.1.1.2, Pontryagin duality determines, associated to a choice of Haar measure $\mu_G$ on a Hausdorff locally compact abelian group $G$, a unique Plancherel measure $\mu_{\widehat{G}}$ on the dual group $\widehat{G}$: the unique Haar measure on $\widehat{G}$ such that the inversion formula of (D.1.1.11) holds as stated with no constant correcting factors.

Example A.3.1.5 (Archimedean standard additive characters). For $G = \mathbf{R}$, the Lebesgue measure $\mu_G = \mathrm{d}x$ is self-dual, and it is the local Tamagawa measure chosen for the field of real numbers in Definition A.3.1.2.

Note that the Fourier transform normalization, for $f\in L^1(\mathbf{R})$:

$$
\widehat{f}(y) := \int_{\mathbf{R}}f(x)e^{-2\pi ixy}\,\mathrm{d}x
$$

is dictated by the fact that the continuous group homomorphism

$$
x\mapsto \chi_x(y) = \psi_{r,\mathrm{std}}(xy) := \exp(2\pi ixy)
$$

defines a specific isomorphism $\mathbf{R}\simeq\widehat{\mathbf{R}}$.

With this normalization, indeed $\mathrm{d}x$ is the Plancherel measure on $\widehat{\mathbf{R}}$ uniquely determined by the Haar measure $\mathrm{d}x$ on $\mathbf{R}$.

A similar calculation shows that the local Tamagawa measure for the local field $\mathbf{C}$ chosen in Definition A.3.1.2(2) is indeed self-dual, upon choosing the character

$$
\psi_{c,\mathrm{std}} : z\mapsto \exp(2\pi i\,\mathrm{Tr}_{\mathbf{C}/\mathbf{R}}(z)) = \exp(4\pi i\,\mathrm{Re}(z))
$$

to identify $\mathbf{C}$ with $\widehat{\mathbf{C}}$ (see [CF, Ch. XV, §2.2,Thm. 2.2.2]).

We now compute the Fourier transform of some special Schwartz-Bruhat functions on local fields, adeles and ideles.

Example A.3.1.6 (Local Fourier transform calculations - I). We compute the Fourier transform of the functions $f = 1_{a+p^N\mathbf{Z}_p}$, for $p$ a prime. We parametrize all continuous characters of $\mathbf{Q}_p$ using the standard character

$$
\psi_{\mathrm{std}} : \mathbf{Q}_p\to U(1)
$$

obtained as the composition of the quotient $\mathbf{Q}_p\to\mathbf{Q}_p/\mathbf{Z}_p$, followed the natural injective continuous homomorphism $\mathbf{Q}_p/\mathbf{Z}_p = (\mathbf{Q}/\mathbf{Z})[p^\infty]\subset\mathbf{R}/\mathbf{Z}$, followed by $\exp(2\pi it)$. Then $\chi(g) = \chi_{\mathrm{std}}(cg)$ for a unique $c\in\mathbf{Q}_p$ depending only on $\chi\in\widehat{\mathbf{Q}_p}$. This identifies, as Hausdorff locally compact abelian groups, $\mathbf{Q}_p$ with its dual group. Upon calling $f_0 := 1_{\mathbf{Z}_p}$, then $1_{p^N\mathbf{Z}_p} = f_0(p^{-N}x)$, and $f(x) = f_0(p^{-N}x-p^{-N}a)$. We then have

$$
\widehat{f}(x) = p^{-N}\widehat{f}_0(p^N(x-a)) = p^{-N}\psi_{\mathrm{std}}(ax)\cdot 1_{p^{-N}\mathbf{Z}_p}(x), \tag{A.3.1.5}
$$

since $\mathbf{Z}_p^{\perp} = \mathbf{Z}_p$ under $\mathbf{Q}_p\simeq\widehat{\mathbf{Q}}_p$ by $\psi_{\mathrm{std}}$. In particular, for $a = 0$ we have, as functions of $x\in\mathbf{Q}_p$:

$$
\widehat{1_{p^N\mathbf{Z}_p}} = p^{-N}\cdot 1_{p^{-N}\mathbf{Z}_p}.
$$

As a result, we can compute the Fourier transform of $1_{\mathbf{Z}_p^{\times}} = 1_{\mathbf{Z}_p}-1_{p\mathbf{Z}_p}$, which gives

$$
\widehat{1_{\mathbf{Z}_p^{\times}}} = 1_{\mathbf{Z}_p}-p^{-1}\cdot 1_{p^{-1}\mathbf{Z}_p}. \tag{A.3.1.6}
$$

Example A.3.1.7 (Local Plancherel measures). We exhibit the Plancherel measure for $G = \mathbf{Q}_p$, for $p$ a prime. The choice $\mu_{\mathbf{Q}_p} = \mathrm{d}x$, the standard additive Haar measure, gives the unit ball $\mathbf{Z}_p$ volume $1$. Since $\mathbf{Q}_p$

## PDF page 558

**558** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

is self-dual via $\psi_{\mathrm{std}}$, the Plancherel measure is a positive real multiple of $\mu_{\mathbf{Q}_p}$. Say $\mu_{\widehat{\mathbf{Q}_p}} = c\cdot\mu_{\mathbf{Q}_p}$ for some unique $c\in\mathbf{R}_{>0}$. It is enough to compute:

$$
\widehat{1_{\mathbf{Z}_p}}(y) = \int_{\mathbf{Q}_p}1_{\mathbf{Z}_p}(x)\overline{\psi_{\mathrm{std}}(xy)}\,\mathrm{d}\mu_{\mathbf{Q}_p}(x)
$$

which is $1_{\mathbf{Z}_p}(y)$ by Example A.3.1.6.

By Lemma D.1.1.2(5), this can only be so if $\mu_{\mathbf{Q}_p} = \mu_{\widehat{\mathbf{Q}_p}}$, and so $c = 1$. Note that $\mu_{\mathbf{Q}_p}$ is also the local Tamagawa measure for the local field $\mathbf{Q}_p$ chosen in Definition A.3.1.2(3).

Example A.3.1.8 (Global standard additive character - I). The self-duality of $\mathbf{A}_{\mathbf{Q}}$ is defined by the standard character

$$
\psi_{\mathbf{Q},\mathrm{std}} := \prod_{v\in\Sigma_{\mathbf{Q}}}\psi_{v,\mathrm{std}}
$$

where $\psi_{v,\mathrm{std}}$ is the standard local character defined in Example A.3.1.6 for $v$ the $p$-adic absolute value for $p$ a prime, and in Example A.3.1.5 for $v$ real. Upon choosing $\mu_{\mathbf{A}_{\mathbf{Q}}} = \mathrm{d}x := \prod_v\mathrm{d}x_v$ to be the standard additive Haar measure on $\mathbf{A}_{\mathbf{Q}}$, it is the content of [CF, Ch. XV, Cor. 3.3.1] that $\mu_{\mathbf{A}_{\mathbf{Q}}}$ is self-dual.

This follows from the fact that the Plancherel measure is a positive real multiple of $\mu_{\mathbf{A}_{\mathbf{Q}}}$, and so upon computing the Fourier transform of $e^{-\pi x_\infty^2}\otimes 1_{\widehat{\mathbf{Z}}}$ to be itself with respect to the choice $\mu_{\mathbf{A}_{\mathbf{Q}}}$ of Haar measure on $\mathbf{A}_{\mathbf{Q}}$, we obtain that such constant multiplier must be $1$. Such calculation follows from Example A.3.1.6 combined with [CF, Ch. XV, §3.3, Lemma 3.3.3]; see also [CF, Ch. XV, §3.3, Cor. 3.3.1]. The measure $\mu_{\mathbf{A}_{\mathbf{Q}}}$ is also the additive Tamagawa measure on $\mathbf{A}_{\mathbf{Q}}$ in Definition A.3.1.1 since $\mu_{\mathbf{A}_{\mathbf{Q}}}([0,1)\times\widehat{\mathbf{Z}}) = 1$.

Example A.3.1.9 (Global standard additive character - II). For $F$ an arbitrary number field and $\mathrm{Tr}_{F/\mathbf{Q}} : F\to\mathbf{Q}$ the trace form, we define

$$
\psi_{F,\mathrm{std}} := \psi_{\mathbf{Q},\mathrm{std}}(\mathrm{Tr}_{F/\mathbf{Q}}(\cdot)). \tag{A.3.1.7}
$$

We note that the additive Tamagawa measure $\nu$ chosen on $\mathbf{A}_F$ in Definition A.3.1.1 is self-dual relative to this choice of additive character, by [CF, Ch. XV, §4.1, Thm. 4.1.2].

Example A.3.1.10 (Local Fourier transform calculations - II). Let $F$ be a number field, $v$ a non-Archimedean place of $F$. Let $p$ be the residue characteristic of $F_v$. Throughout this work, we have normalized the additive character on $F_v$ to be the standard additive character $\psi_{F_v,\mathrm{std}} = \psi_{\mathbf{Q}_p,\mathrm{std}}\circ\mathrm{Tr}_{F_v/\mathbf{Q}_p}$, and relative to this choice, the local additive Tamagawa measure $\nu_v$ is self-dual; i.e., the resulting Fourier transform is a unitary automorphism on $L^2(F_v,\nu_v)$.

We recall here the following identity of functions on $F_v$:

$$
\widehat{1_{\mathcal{O}_{F_v}}} = |\mathrm{disc}(\mathcal{O}_{F_v}/\mathbf{Z}_p)|_p^{1/2}1_{\mathfrak{d}_{F_v/\mathbf{Q}_p}^{-1}} \tag{A.3.1.8}
$$

where $\mathfrak{d}_{F_v/\mathbf{Q}_p}^{-1}$ is the inverse different. In particular, if $F_v/\mathbf{Q}_p$ is unramified then $1_{\mathcal{O}_{F_v}}$ is an eigenfunction of the local Fourier transform, with eigenvalue $1$.

Example A.3.1.11 ($S$-local dual lattices). We let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places and all the ramified places of $F$ over $\mathbf{Q}$. The closed subgroup $\mathcal{O}_{F,S}\subset\mathbf{A}_{F,S}$ is discrete and co-compact by Lemma A.1.5.1(2).

We denote by $\psi_v$ the standard additive character on the local field $F_v$, for each $v\in S$, constructed in Example A.3.1.8 and Example A.3.1.9, and recall (see Lemma A.3.1.3) that our normalization for the Haar measure $\nu_S$ on $\mathbf{A}_{F,S}$ gives the quotient $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$, upon endowing $\mathcal{O}_{F,S}$ with the counting measure, volume $1$. This is the additive $S$-local Tamagawa measure defined in Definition A.3.1.1. For the standard additive

## PDF page 559

**A.3. HAAR MEASURES** · **559**

character

$$
\psi_{S,\mathrm{std}} = \bigotimes_{v\in S}\psi_v \tag{A.3.1.9}
$$

and $x\in\mathbf{A}_{F,S}$ an arbitrary element, $\chi_x(y) := \psi_{S,\mathrm{std}}(xy)$ is a continuous characterof $\mathbf{A}_{F,S}$ and the assignment $x\mapsto\chi_x$ is an isomorphism $\mathbf{A}_{F,S}\to\widehat{\mathbf{A}_{F,S}}$ of Hausdorff locally compact abelian groups. This makes $\nu_S$ self-dual (i.e., its own Plancherel measure) due to the same for each $(\psi_v,\nu_v)$.

With respect to the duality pairing

$$
\langle\cdot,\cdot\rangle_S : \mathbf{A}_{F,S}\times\mathbf{A}_{F,S}\to \mathrm{U}(1) \tag{A.3.1.10}
$$

assigned by $\langle x,y\rangle_S := \chi_x(y)$, the closed orthogonal $\Gamma^{\perp}$ of the closed discrete subgroup $\Gamma := \mathcal{O}_{F,S}\subset\mathbf{A}_{F,S}$ is $\mathcal{O}_{F,S}$ itself, under the stated assumptions on $S$. To see this, we proceed as follows.

Since $\Gamma$ is co-compact,$^2$ the isomorphism $\widehat{\mathbf{A}_{F,S}/\Gamma}\simeq\Gamma^{\perp}$ from Lemma D.1.4.6(2) yields $\Gamma^{\perp}$ is discrete. We have $\mathcal{O}_{F,S}\subset\Gamma^{\perp}$, and hence $\Gamma^{\perp}/\mathcal{O}_{F,S}$ is a discrete subgroup of $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$ that is compact, so it is a finite abelian group. We observe that we have a duality pairing analogous to $\langle\cdot,\cdot\rangle_S$ from (A.3.1.10):

$$
\langle\cdot,\cdot\rangle'_S : (\mathbf{A}_{F,S}\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v})\times(\mathbf{A}_{F,S}\times\bigoplus_{v\in\Sigma_F-S}F_v/\mathcal{O}_{F_v})\to \mathrm{U}(1) \tag{A.3.1.11}
$$

defined as:

$$
\langle x',y'\rangle'_S := (\psi_{S,\mathrm{std}}\otimes\bigotimes_{v\in\Sigma_F-S}\psi_v)(x'y') = \psi_{S,\mathrm{std}}(x'_Sy'_S)\prod_{v\in\Sigma_F-S}\psi_v(x'_vy'_v) \tag{A.3.1.12}
$$

where $x'_S$, respectively $y'_S$, denotes the projection of $x',y'$ onto $\mathbf{A}_{F,S}$, and similarly $x'_v$, $y'_v$ denote the projections of $x',y'$ onto $\mathcal{O}_{F_v}$. We note that indeed $\langle\cdot,\cdot\rangle'_S$ is a duality pairing, by [CF, Ch. XV, §2.2, Lemma 2.2.3], and because $S$ contains all the ramified primes of $F$, (so for every $v\in\Sigma_F-S$ and $p$ the prime residue characteristic of the non-Archimedean local field $F_v$, we have $\mathfrak{d}_{F_v/\mathbf{Q}_p}^{-1} = \mathcal{O}_{F_v}$). We therefore have $\psi_v(x'_vy'_v) = 1$ in (A.3.1.12) for every finite place $v$ of $F$ not contained in $S$, which gives:

$$
\langle x',y'\rangle'_S := \langle x'_S,y'_S\rangle_S \tag{A.3.1.13}
$$

for every $x',y'\in\mathbf{A}_{F,S}\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v}$.

We denote by $A := (\mathcal{O}_{F,S})^{\perp,\langle\cdot,\cdot\rangle'_S}$ the orthogonal of $\mathcal{O}_{F,S}\subset\mathbf{A}_{F,S}\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v}$ with respect to the duality pairing $\langle\cdot,\cdot\rangle'_S$. A similar reasoning as in the foregoing, using compactness of $(\mathbf{A}_{F,S}\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v})/\mathcal{O}_{F,S}$, shows that $A$ is discrete and co-compact as a closed subgroup of $\mathbf{A}_{F,S}\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v}$, and it contains $\mathcal{O}_{F,S}$ as a subgroup of finite index.

Since $(\mathbf{A}_{F,S}\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v})/\mathcal{O}_{F,S}$ is an $F$-vector space, as it is isomorphic to $\mathbf{A}_F/F$ (see Lemma A.1.5.1(3)), the quotient $A/\mathcal{O}_{F,S}$ is a finite abelian subgroup of a uniquely divisible abelian group (i.e., a $\mathbf{Q}$-vector space), so it is trivial.

The surjective homomorphism $\mathbf{A}_{F,S}\times\prod_{v\in\Sigma_F-S}\mathcal{O}_{F_v}\to\mathbf{A}_{F,S}$ defined by $y'\mapsto y'_S$, induces a homomorphism $A\to\Gamma^{\perp}$ which is injective and compatible with the finite index subgroups $\mathcal{O}_{F,S}$ of $A$, and $\Gamma = \mathcal{O}_{F,S}$ of $\Gamma^{\perp}$.

It follows that $\Gamma^{\perp}/\mathcal{O}_{F,S}$ is a finite abelian subgroup of $A/\mathcal{O}_{F,S}$, which is trivial, and hence it is itself trivial. We deduce that we have $\mathcal{O}_{F,S} = \Gamma^{\perp}$.

**A.3.2. Tamagawa measure on $\mathrm{GL}_1(\mathbf{A}_F)$.** The topological group $\mathrm{GL}_1(\mathbf{A}_F)$ is a Hausdorff locally compact abelian group, so it is unimodular and has a unique Haar measure specified as follows:

Definition A.3.2.1. Let $F$ be a number field. Denote by $\mu$ the unique Haar measure on $\mathrm{GL}_1(\mathbf{A}_F)$ such that with counting measure on $F^{\times}$ the associated Haar measure $\bar{\mu}$ on $C_F$ and $\mathrm{d}t/t$ on $\mathbf{R}_{>0}\overset{|\cdot|_F}{\simeq}C_F/C^1_F$ give$^2$

---

$^2$Brian suggested the rest of the original exposition of the argument from here onward should be rewritten, so at least reread the revised version now here to check if now OK.

## PDF page 560

**560** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

rise to the measure $\bar{\mu}_1$ on $C^1_F$ with volume

$$
\bar{\mu}_1(C^1_F) = \frac{2^{r_1}(2\pi)^{r_2}h_FR_F}{|d_F|^{1/2}w_F}, \tag{A.3.2.1}
$$

fwhere $d_F\in\mathbf{Z}^+$ is the absolute discriminant of $F$ and $R_F := |\det(\mathscr{L}(\varepsilon_i))_{1\le i\le r_1+r_2-1}|$ is the regulator of $F$. We refer to $\mu$ as the *Tamagawa measure* on $\mathrm{GL}_1(\mathbf{A}_F)$, to $\bar{\mu}$ as the *Tamagawa measure* on $C_F$, and to $\bar{\mu}_1$ as the *Tamagawa measure* on $C^1_F$.

Definition A.3.2.2. Let $F$ be a number field, $v\in\Sigma_F$ a place. Define a Haar measure on $F_v^{\times}$ as follows:

(1) If $v$ is Archimedean, we define $\mu_v$ to be $|\cdot|_v^{-1}\nu_v|_{F_v^{\times}}$ (a Haar measure since $|\cdot|_v$ is normalized),

(2) If $v$ is non-Archimedean, we define $\mu_v$ to be the unique Haar measure on $F_v^{\times}$ satisfying the condition:

$$
\mu_v(\mathcal{O}_{F_v}^{\times}) = |\mathrm{disc}(\mathcal{O}_{F_v}/\mathbf{Z}_p)|_p^{1/2}, \tag{A.3.2.2}
$$

where $p$ is the residue characteristic of $F_v$.

We refer to $\mu_v$ as the *local multiplicative Tamagawa measure* on $F_v^{\times}$.

Lemma A.3.2.3. *Let $F$ be a number field. For every $v\in\Sigma_{F,f}$, let $\mu_v$ be the local multiplicative Tamagawa measure on $F_v^{\times}$. We have, as Haar measures on $F_v^{\times}$:*

$$
\mu_v = \frac{q_v}{q_v-1}\frac{\nu_v}{|\cdot|_v} \tag{A.3.2.3}
$$

*where $q_v$ is the size of the residue field at $v$ and $\nu_v$ is the local additive Tamagawa measure on $F_v$.*

Proof. Since $|\cdot|_v$ is the normalized absolute value on $F_v$, the measure $|\cdot|_v^{-1}\nu_v$ for $\nu_v$ the local additive Tamagawa measure on $F_v$ is a Haar measure on $F_v^{\times}$. There therefore exists a unique real number $c > 0$ such that $\mu_v = c|\cdot|_v^{-1}\nu_v$. It is enough to compute the measure of $\mathcal{O}_{F_v}^{\times}$ with respect to each measure and show that we have $c = q_v/(q_v-1)$.

We have

$$
\int_{\mathcal{O}_{F_v}^{\times}}\frac{\mathrm{d}\nu_v(g_v)}{|g_v|_v} = \int_{\mathcal{O}_{F_v}^{\times}}\mathrm{d}\nu_v(g_v) = \int_{\mathcal{O}_{F_v}-\mathfrak{m}_{F_v}}\mathrm{d}\nu_v(g_v) = \nu_v(\mathcal{O}_{F_v})-\nu_v(\mathfrak{m}_{F_v}) = \left(1-\frac{1}{q_v}\right)\nu_v(\mathcal{O}_{F_v}) \tag{A.3.2.4}
$$

since $\mathfrak{m}_{F_v}$ has index $q_v$ in $\mathcal{O}_{F_v}$.

Since $\nu_v$ is the local additive Tamagawa measure on $F_v$, this in turn reads as

$$
\frac{q_v-1}{q_v}\nu_v(\mathcal{O}_{F_v}) = \frac{q_v-1}{q_v}|\mathrm{disc}(\mathcal{O}_{F_v}/\mathbf{Z}_p)|_p^{1/2} = \frac{q_v-1}{q_v}\mu_v(\mathcal{O}_{F_v}^{\times}).
$$

This gives $c = q_v/(q_v-1)$, so (A.3.2.3) holds. $\square$

The measure $\mu$ is explicitly described in terms of the $\mu_v$'s:

Lemma A.3.2.4. *Let $F$ be a number field. For every $v\in\Sigma_F$, let $\mu_v$ be local multiplicative Tamagawa measure on $F_v^{\times}$. We have, as Haar measures on $\mathrm{GL}_1(\mathbf{A}_F)$,*

$$
\mu = \bigotimes_{v\in\Sigma_F}\mu_v. \tag{A.3.2.5}
$$

This is [RV, Thm. 7.21]. The restricted produce measure makes sense since $\mu_v(\mathcal{O}_{F_v}^{\times}) = 1$ for all but finitely many $v$.

Remark A.3.2.5 (On the normalizations for additive character and measure). The Tamagawa measures on $\mathbf{A}_F$ and $\mathrm{GL}_1(\mathbf{A}_F)$ constructed in this section are the same choices of Haar measures made on $\mathbf{A}_F$ and $\mathrm{GL}_1(\mathbf{A}_F)$ made in [CF, Ch.XV,p.313,328,334].

## PDF page 561

**A.3. HAAR MEASURES** · **561**

The former is also the same choice of normalized Haar measure made in [Co, Appendix I,(34),p.57]. Its purpose is to normalize the adelic Poisson Summation Formula, removing the volume factor (which equals $1$, under this choice of normalization; see Theorem 2.2.3.2 as well as [CF, Ch.XV,§4.2,Thm.4.2.1].

They are special cases of general Tamagawa measures on the adelic points of algebraic groups over a number field, for which we refer the reader to [Oes, §3.1,4] (the former corresponding to the invariant differential on $(\mathbf{G}_a)_F$ given by $\mathrm{d}x$, and the latter to $\mathrm{d}x/x$ on $(\mathrm{GL}_1)_F$, $x$ being the standard global parameter on $\mathbf{A}^1_F$).

**A.3.3. Haar measures on $C_F$ and $C^1_F$.** We now return to the orbit structure of $\mathrm{GL}_1(\mathbf{A}_F)$ under the left-translation action of the discretely embedded diagonal copy of $F^{\times}$.

A.3.3.1. *Continuous sections of the idelic norm and Radon product decompositions.* We choose

$$
s : \mathbf{R}_{>0}\to\mathrm{GL}_1(\mathbf{A}_F)
$$

a continuous homomorphic section to the idelic norm $|\cdot|_F : \mathrm{GL}_1(\mathbf{A}_F)\to\mathbf{R}_{>0}$. By Lemma A.2.2.9,

$$
\theta_{F,s} : \mathbf{R}_{>0}\times\mathrm{GL}_1(\mathbf{A}_F)^1\to\mathrm{GL}_1(\mathbf{A}_F)
$$

defined as $\theta_{F,s}(t,g_0) = s(t)g_0$ is an isomorphism of Hausdorff locally compact abelian groups. Thus, $(\mathrm{d}t/t)\otimes\mu^1$ corresponds to $\mu$ under any such $\theta_{F,s}$. In particular,

$$
\mu(s([1,T])\cdot E^1_F) = \log(T)\bar{\mu}_1(C^1_F)
$$

where $\bar{\mu}_1(C^1_F)$ is given by (A.3.2.1).

**A.3.4. $S$-local Tamagawa measures.** Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. The local additive and multiplicative Tamagawa measures on each $F_v$ and $F_v^{\times}$ can be assembled together into $S$-local Tamagawa measures. We introduce the relevant definitions and terminology here.

Definition A.3.4.1 ($S$-local additive and multiplicative Tamagawa measures). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We define:

(1) The Haar measure on $\mathbf{A}_{F,S}$ given by

$$
\nu_S = \bigotimes_{v\in S}\nu_v \tag{A.3.4.1}
$$

is called the *$S$-local additive Tamagawa measure on $\mathbf{A}_{F,S}$*, where $\nu_v$ is the additive local Tamagawa measure on $F_v$ from Definition A.3.1.2 for each $v\in S$.

(2) The Haar measure on $\mathrm{GL}_1(\mathbf{A}_{F,S})$ given by

$$
\mu_S = \bigotimes_{v\in S}\mu_v \tag{A.3.4.2}
$$

is called the *$S$-local multiplicative Tamagawa measure on $\mathrm{GL}_1(\mathbf{A}_{F,S})$*, where $\mu_v$ is the multiplicative local Tamagawa measure on $F_v^{\times}$ from Definition A.3.2.2 for each $v\in S$.

(3) We define:

(1) $\mu_{S,1}$ to be the unique Haar measure on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$ determined as per Theorem D.1.2.1 by the choices of $\mu_S$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and $\mathrm{d}t/t$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})/\mathrm{GL}_1(\mathbf{A}_{F,S})^1\overset{|\cdot|_{F,S}}{\simeq}\mathbf{R}_{>0}$,

(2) $\bar{\mu}_S$ to be the unique Haar measure on $C_{F,S}$ determined as per Theorem D.1.2.1 by the choices $\mu_S$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and the counting measure on $\mathcal{O}_{F,S}^{\times}$,

(3) $\bar{\mu}_{S,1}$ to be the unique Haar measure on $C^1_{F,S}$ determined as per Theorem D.1.2.1 by the choices $\mu_{S,1}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$ and the counting measure on $\mathcal{O}_{F,S}^{\times}$.

## PDF page 562

**562** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

REMARK A.3.4.2 (On the normalizations of additive character and measures). We recall that the $S$-local Tamagawa measure $\nu_S$ on $\mathbf{A}_{F,S}$, obtained as the product of the local additive Tamagawa measures $\nu_v$ on each of the local fields $F_v$, is self-dual with respect to the choice of standard additive character $\psi_v$ whose construction is discussed in Example A.3.1.8 and Example A.3.1.9 (see also Remark A.3.2.5), and relative to the resulting Fourier transform.

We caution the reader that while all but finitely may of the non-Archimedean places $v$ of the number field $F$ are such that the local Fourier transform of the Schwartz-Bruhat function $1_{\mathcal{O}_{F_v}}$ with respect to the self-dual $\nu_v$ satisfies:

$$
\mathcal{F}_v(1_{\mathcal{O}_{F_v}}) = 1_{\mathcal{O}_{F_v}}
$$

finitely may of them may not. Namely, for any finite place $v$ with residue characteristic $p$ we have

$$
\mathcal{F}_v(1_{\mathcal{O}_{F_v}}) = |\mathrm{disc}(\mathcal{O}_{F_v}/\mathbf{Z}_p)|_p^{1/2} 1_{\mathfrak{d}_{F_v/\mathbf{Q}_p}^{-1}}
$$

as seen in Example A.3.1.10, so this agrees with $1_{\mathcal{O}_{F_v}}$ if and only if $v$ is unramified over $p$.

The volume of $\mathbf{A}_{F,S}/\mathcal{O}_{F,S}$ with respect to the unique Haar measure induced as per Theorem D.1.2.1 on the compact Hausdorff quotient by the $S$-local additive Tamagawa measure $\nu_S$ on $\mathbf{A}_{F,S}$ and by the counting measure on $\mathcal{O}_{F,S}$, is the prime-to-$S_f$ part of $|\mathrm{disc}(K/\mathbf{Q})|^{1/2}$, similarly to the proof of Lemma A.3.1.3. This is $1$ unless $S$, which already contains all the Archimedean places of $F$, contains all finite places of $F$ that ramify over $\mathbf{Q}$.

**A.4. Dirichlet's $S$-unit Theorem: estimates by lattice point-counting**

In this section we illustrate two applications of Dirichlet's $S$-unit Theorem (see Theorem A.1.5.2(2)) resting on lattice point-counting techniques that go back to Davenport's paper on a principle of Liouville (see [Davenport-1]). These techniques will enable us to make estimates on the growth of lattice point-counting functions counting the number of $S$-units contained in certain convex polytopes, with the aim of applying such estimates to the study of the $S$-local adelic $\theta$-functions through Theorem 2.4.2.1.

**A.4.1. Lattice point-counting and Dirichlet's $S$-Unit Theorem.** Theorem 2.4.2.1 rests upon the following estimate, which is obtained with a lattice point-counting argument enabled by Dirichlet's $S$-Unit Theorem.$^3$

THEOREM A.4.1.1 (Estimates on point-counting functions of the lattice of $S$-units). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

*Define:*

(1) $Q \subset \mathbf{A}_{F,S_\infty}$ *the compact hypercube with non-empty interior:*

$$
Q := \{x \in \mathbf{A}_{F,S_\infty} : |x_v|_v \le 1,\ v \in S_\infty\}. \tag{A.4.1.1}
$$

(2)

$$
u := 1_Q \otimes \bigotimes_{v \in S_f} 1_{\mathcal{O}_{F_v}}, \tag{A.4.1.2}
$$

*a boundedly supported and bounded (by $1$) piece-wise continuous function on $\mathbf{A}_{F,S}$.*

*There exist real numbers $C > 0$ and $\varepsilon > 0$ such that for all $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$ with $|g|_{F,S} < \varepsilon$ we have:*

$$
\sum_{\xi \in \mathcal{O}_{F,S}^\times} u(\xi g) \le C\, |\log|g|_{F,S}||^{|S|-1}. \tag{A.4.1.3}
$$

---
$^3$Maybe put in a Remark indicating relation to an assertion in a paper of Connes.

## PDF page 563

**A.4. DIRICHLET'S $S$-UNIT THEOREM: ESTIMATES BY LATTICE POINT-COUNTING** · **563**

The proof of Theorem A.4.1.1 mirrors a method first devised by Davenport and reprised in [Schm, Lemma 1, p. 347], and for which we refer the reader to [Davenport-1, §2, Thm., p. 180].

The idea is to estimate a lattice point-counting function by means of a volume of a convex polytope within $\mathbf{R}^S$, which is then computed by slicing it by hyperplane sections: an "approximate Fubini" calculation. This is at the heart of [Davenport-1, §2, Thm., p. 180], and applied in the proof of [Schm, Lemma 1, p. 347].

PROOF. Define

$$
Z := \prod_{v \in S_\infty} (-\infty,0] \times \prod_{v \in S_f} (-\infty,0] \tag{A.4.1.4}
$$

and denote by $H_{\mathrm{log}}$ the hyperplane $\{(x_v)_{v \in S} \in \mathbf{R}^S : \sum_{v \in S} x_v = 0\}$ and denote by $\mathscr{L}_S : \mathrm{GL}_1(\mathbf{A}_{F,S}) \to \mathbf{R}^S$ the logarithm homomorphism, $g \mapsto (\log|g|_v)_{v \in S}$, so $Z = \mathscr{L}_S(\mathrm{GL}_1(\mathbf{A}_{F,S}) \cap (Q \times \prod_{v \in S_f} \mathcal{O}_{F_v}))$.

For fixed $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$, the condition on $\xi \in \mathcal{O}_{F,S}^\times$ that $u(\xi g) \ne 0$ is that $|\xi_v g_v|_v \le 1$ for all places $v$ of $F$. We can therefore compute

$$
\sum_{\xi \in \mathcal{O}_{F,S}^\times} u(\xi g) = |\mathcal{O}_{F,S}^\times \cap g^{-1} \cdot (Q \times \prod_{v \in S_f} \mathcal{O}_{F_v})|. \tag{A.4.1.5}
$$

Since the condition $|\xi_v g_v|_v \le 1$ intervenes solely through the absolute value at $v$ for each $v \in S$, we can apply $\mathscr{L}_S$ to rewrite:

$$
\sum_{\xi \in \mathcal{O}_{F,S}^\times} u(\xi g) = |\mathscr{L}_S(\mathcal{O}_{F,S}^\times) \cap (-\mathscr{L}_S(g) + \prod_{v \in S} (-\infty,0])| = |\mathscr{L}_S(\mathcal{O}_{F,S}^\times) \cap (-\mathscr{L}_S(g) + Z)|. \tag{A.4.1.6}
$$

(Note that typically $g \notin \mathcal{O}_{F,S}^\times$, so this count depends very much on $g$.)

We choose the continuous homomorphic section $\tau$ to the $S$-idelic norm given by the diagonal section $s_{F,\delta}$ from (A.2.2.11). Its image is contained within the closed subgroup $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})$ (as for any continuous homomorphic section). This choice of $\tau$ ensures $|\log|\tau(t)_v|_v| \le |\log(t)|$ for all $t \in \mathbf{R}_{>0}$ since $\tau(t)_v = t^{1/n_v}$ for an integer $n_v \in \{1,2\}$, an inequality that will be useful later.

For the fundamental domain $E_{S,0}$ from (A.2.4.5) for the continuous left-translation action of $\mathcal{O}_{F,S}^\times$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, the product $\tau(\mathbf{R}_{>0}) \cdot E_{S,0}$ is a fundamental domain for the action of $\mathcal{O}_{F,S}^\times$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})$. Thus, since both sides of the desired bound (A.4.1.3) are $\mathcal{O}_{F,S}^\times$-invariant, for the purposes of proving that bound we can limit $g$ to vary within $\tau(\mathbf{R}_{>0}) \cdot E_{S,0}$. Going a step further, recall that $E_{S,0}$ maps onto $\ker(\mathrm{Pic}(\mathcal{O}_F) \to \mathrm{Pic}(\mathcal{O}_{F,S}))$, and that if $g_1,\dots,g_k$ are representatives in $E_{S,0}$ for the elements of that kernel then

$$
\tau(\mathbf{R}_{>0}) \cdot E_{S,0} = \coprod g_i \tau(\mathbf{R}_{>0}) \cdot (E_{S_\infty,0} \times \widehat{\mathcal{O}}_F^\times). \tag{A.4.1.7}
$$

We are going to first prove (A.4.1.3) by working separately with points of the form $g_i g$ for $g \in \tau(\mathbf{R}_{>0}) \cdot (E_{S_\infty,0} \times \widehat{\mathcal{O}}_F^\times)$; such $g$ we shall refer to as "basic". In what follows, we fix $i$ (this will yield some constants depending on $i$, from which we'll arrive at uniform constants at the end).

In light of (A.4.1.6), $\sum_{\xi \in \mathcal{O}_{F,S}^\times} u(\xi g_i g)$ is the number of points of the lattice $\mathscr{L}_S(\mathcal{O}_{F,S}^\times)$ in $H_{\mathrm{log}}$ contained in the $-\mathscr{L}_S(g_i g)$-translate of the box $Z \subset \mathbf{R}^S$. Note that with respect to the standard Euclidean inner product on $\mathbf{R}^S$, $H_{\mathrm{log}}$ is the hyperplane in $\mathbf{R}^S$ orthogonal to the line $\mathbf{R} \cdot (\sum_{v \in S} \mathbf{e}_v)$, where $\{\mathbf{e}_v\}_{v \in S}$ is the standard basis indexed by $S$.

We write $\mathbf{e} := \sum_{v \in S} \mathbf{e}_v$ and choose on the line $\mathbf{R} \cdot \mathbf{e}$ the normalized Lebesgue measure $\lambda_{\mathbf{e}}$ giving the segment $[0,1) \cdot \mathbf{e}$ volume $1$. By Theorem D.1.2.1 there exists a unique Haar measure $\lambda_0$ on $H_{\mathrm{log}}$ such that the quotient measure induced on $\mathbf{R}\mathbf{e} \simeq \mathbf{R}^S/H_{\mathrm{log}}$ by the Lebesgue measure $\lambda$ on $\mathbf{R}^S$ (normalized so as to give the hypercube $[0,1)^S$ volume $1$) and by $\lambda_0$ on $H_{\mathrm{log}}$ is $\lambda_{\mathbf{e}}$. We further endow $H_{\mathrm{log}}$ with the inner product induced by the Euclidean inner product on $\mathbf{R}^S$. Note that neither such inner product nor the measures $\lambda_{\mathbf{e}}$ and $\lambda_0$ depend on the choice of enumeration of the places in $S$.

## PDF page 564

**564** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

For $\{\varepsilon_k, 1 \le k \le |S|-1\} \subset \mathcal{O}_{F,S}^\times$ a set of fundamental $S$-units, $\{\mathscr{L}_S(\varepsilon_k), 1 \le k \le |S|-1\}$ is an $\mathbf{R}$-basis for $H_{\mathrm{log}}$. We denote by $|\det \mathscr{L}_S(\mathcal{O}_{F,S}^\times)|$ the absolute Jacobian of the change of basis matrix from any orthonormal basis on $H_{\mathrm{log}}$ to $\{\mathscr{L}_S(\varepsilon_k), 1 \le k \le |S|-1\}$; equivalently, it is the volume of the parallelotope $\sum_{1 \le k \le |S|-1} [0,1) \cdot \mathscr{L}_S(\varepsilon_k)$ in $H_{\mathrm{log}}$.

As convenient notation, let

$$
N_S(g_i g) := |(-\mathscr{L}_S(g_i g) + Z) \cap \mathscr{L}_S(\mathcal{O}_{F,S}^\times)|
$$

(we have seen that this count is $\sum_{\xi \in \mathcal{O}_{F,S}^\times} u(\xi g_i g)$). We note that $(-\mathscr{L}_S(g_i g) + Z) \cap H_{\mathrm{log}}$ is convex, so its intersection with any affine line in $H_{\mathrm{log}}$ is also convex and thus is an interval; in other words, the region $(-\mathscr{L}_S(g_i g) + Z) \cap H_{\mathrm{log}}$ inside $H_{\mathrm{log}}$ is of "class $m=1$" in the lexicon from [Schm, Lemma 1, p. 347]. Before we can apply [Schm, Lemma 1, p. 347], we need to prove:

CLAIM A.4.1.2. There exists a real number $\varepsilon > 0$ such that for every basic $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$ with $|g|_{F,S} < \varepsilon$ and every $i$, the closed convex subset $(-\mathscr{L}_S(g_i g) + Z) \cap H_{\mathrm{log}} \subset H_{\mathrm{log}}$ is contained in the closed ball in $H_{\mathrm{log}}$ of radius $C_0|\log|g|_{F,S}|$ centered at the origin for some real number $C_0 > 0$ dependent on $S$ but not on $g$ nor $i$.

We grant the Claim for a moment, and draw some conclusions. The ball in that Claim can be fed into [Schm, Lemma 1, p. 347] when its radius is sufficiently large in a manner we need to precisely control. We pick a (very small) real number $0 < \varepsilon < 1$ making $|\log(\varepsilon)|$ large relative to successive minima of the lattice $\mathscr{L}_S(\mathcal{O}_{F,S}^\times)$ in $H_{\mathrm{log}}$ as specified in the technical condition [Schm, §2, (2.2), Lemma 1, p. 347], so for all basic $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$ that satisfy $|g|_{F,S} < \varepsilon$ (so $|\log|g_i g|_{F,S}| = |\log|g|_{F,S}| > |\log(\varepsilon)|$) we have

$$
N_S(g_i g) = \frac{\lambda_0((-\mathscr{L}_S(g_i g) + Z) \cap H_{\mathrm{log}})}{|\det(\mathscr{L}_S(\mathcal{O}_{F,S}^\times))|} + O(|\log|g|_{F,S}||^{|S|-2}) \tag{A.4.1.8}
$$

as $|g|_{F,S} \to 0$, where the implied constant has absorbed the constant $C_0 > 0$ from Claim A.4.1.2 and depends only on $S$, moreover through the geometry of the lattice $\mathscr{L}_S(\mathcal{O}_{F,S}^\times)$ inside $H_{\mathrm{log}}$.

The real number $\varepsilon > 0$ likewise depends only on $S$, moreover through the successive minima of the lattice $\mathscr{L}_S(\mathcal{O}_{F,S}^\times) \subset H_{\mathrm{log}} \simeq \mathbf{R}^{|S|-1}$, which in turn only depends on $\mathscr{L}_S(\mathcal{O}_{F,S}^\times)$ and the normed structure on the hyperplane $H_{\mathrm{log}}$ inside the Euclidean space $\mathbf{R}^S$. We now prove the Claim.

PROOF OF CLAIM A.4.1.2. We are considering only $g$ basic, which we recall means that $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$ is constrained to vary over $\tau(\mathbf{R}_{>0}) \cdot (E_{S_\infty,0} \times \widehat{\mathcal{O}}_F^\times)$ from (A.4.1.7). The subset $Z$ from (A.4.1.4) is a closed pointed cone in $\mathbf{R}^S$. Since $H_{\mathrm{log}} \cap Z = \{0\}$, the intersection of $(\mathscr{L}_S(g_i g) + H_{\mathrm{log}}) \cap Z$ is carried onto the intersection of $H_{\mathrm{log}}$ with $-\mathscr{L}_S(g_i g) + Z$ under translation by $-\mathscr{L}_S(g_i g)$ on $\mathbf{R}^S$.

Let's find a real number $C_0 > 0$ depending only on $|S|$ such that $(-\mathscr{L}_S(g_i g) + Z) \cap H_{\mathrm{log}}$ is contained in the closed ball in $\mathbf{R}^S$ centered at the origin and of radius $C_0 |\log|g|_{F,S}| + M_i$ for a constant $M_i$ depending only on the fixed $g_i$ and $S$. Observe that the vector $\mathscr{L}_S(g_i g)$ has supremum norm bounded above by the maximum of the real numbers $|\log|(g_i)_v g_v|_v|$ as $v$ varies over the finitely many places of $F$ in $S$, with these real numbers equal to $|\log|g_i|_v|$ for finite $v$ (which is $1$ for all but finitely many $v$) since $g$ is basic: we have $g = \tau(t_0) g_0$ for a unique $t_0 \in \mathbf{R}_{>0}$ and $g_0 \in E_{S_\infty,0} \times \widehat{\mathcal{O}}_F^\times$.

Since $E_{S_\infty,0}$ is relatively compact in $\mathbf{R}^{S_\infty}$, we conclude that $\log(|(g_i g)_w|_w)$ is bounded as $g$ varies over $E_{S_\infty,0} \times \widehat{\mathcal{O}}_F^\times \subset \mathrm{GL}_1(\mathbf{A}_{F,S})$ and $w$ varies over the places in $S$. In particular, for each $v \in S$, we have $|\log|(g_i g)_v|_v| \le C_0 \max_{v \in S_\infty} |\log|\tau(t)_v|_v|$ for a real number $C_0 > 0$ and all basic $g = \tau(t_0) g_0$ with real $t_0 > 0$ and $g_0 \in E_{S_\infty,0} \times \widehat{\mathcal{O}}_F^\times$. Since we chose the diagonal section $\tau = s_{F,\delta}$, for every $v \in S_\infty$ we have $|\log|\tau(t)_v|_v| \le |\log(t)|$ for all $t \in \mathbf{R}_{>0}$. Hence, the sup-norm of $\mathscr{L}_S(g_i g) \in \mathbf{R}^S$ is bounded above by $C_0|\log(t_0)| + B_i$. where $B_i = \max_{v \in S_f} |\log(|(g_i)_v|)|$. But $\tau$ is a section to the idelic norm and $g_0 \in \mathrm{GL}_1(\mathbf{A}_{F,S})^1$, so $|g|_{F,S} = |\tau(t_0|_{F,S} = t_0$, yielding that $\mathscr{L}_S(g_i g)$ has sup-norm as most $C_0 |\log(|g|_{F,S})| + B_i$ as desired.

## PDF page 565

**A.4. DIRICHLET'S $S$-UNIT THEOREM: ESTIMATES BY LATTICE POINT-COUNTING** · **565**

All norms on $\mathbf{R}^S$ are equivalent, such as the sup-norm and its natural inner product norm, so upon denoting $\|\cdot\|$ the norm induced on $H_{\mathrm{log}}$ by the inner product inherited from $\mathbf{R}^S$ we conclude that $\|\mathscr{L}_S(g_i g)\| \le C_1|\log|g|_{F,S}| + M_i$ for all $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$ with some real number $C_1 > 0$ dependent on $S$ but not on $g$ and some $M_i > 0$ depending on $i$ and $S$.

We denote by $B_0(r)$ the closed ball of radius $r > 0$ in $\mathbf{R}^S$ centered at $0$. We claim there exists a real number $A_i > 0$ independent of $g$ such that

$$
Z \cap (\mathscr{L}_S(g_i g) + H_{\mathrm{log}}) \subset B_0(A_i\|\mathscr{L}_S(g_i g)\|) \subset B_0(A_i(C_1|\log|g|_{F,S}| + M_i)) \tag{A.4.1.9}
$$

for all basic $g$ such that $|g|_{F,S} < \varepsilon_i$. The second containment follows from how we made $C_1$ above. To see the first, we claim more broadly that for a closed polyhedral cone $Z$ in a Euclidean space $V$ with vertex at the origin and a hyperplane $H$ which meets $Z$ in exactly $\{0\}$, for all $v \in V$ the intersection $(v + Z) \cap H$ is contained in the closed ball $B_0(C\|v\|)$ centered at $0$ with radius $C\|v\|$ where $C = \max(1/\sin(\theta_i)) \ge 1$ where $0 < \theta_i < \pi$ are the finitely many angles by which $H$ meets the faces of $Z$ (we make the convention $\theta_1 = \pi/2$ if $\dim V = 1$ so that $C = 1$).

The case $\dim V \le 1$ is trivial (as $H = \{0\}$). In general, we pick any $v \in V$ and $z \in Z$ such that $v + z \in H$ and replace everything with its intersection with the span of $v$ and $z$: if that span is $1$-dimensional then $v + z = 0$ and so there is nothing to do, whereas if the span is $2$-dimensional then the two angles made against the line $H$ by the two faces of $Z$ (a single face if $Z$ is a closed half-ray) are among the original angles before the planar slicing.

This reduces us to the case $\dim V = 2$, so $H$ is a line through the origin meeting the closed convex cone $Z$ only in $\{0\}$. By the triangle inequality, via $-v$ translation it is equivalent (at the cost of replacing $C$ with $C + 1$) to now consider $Z \cap (v + H)$ instead. We can also assume that intersection is non-empty (or else there is nothing to do). The parallel translate $v + H$ meets $Z$ in a line segment inside the affine line $v + H$, so an upper bound on the norms of all points in $(v + H) \cap Z.$ is the largest norm among the endpoints of that line segment. If $0 < \theta_1, \theta_2 < \pi$ are the angles by which the two faces of the acute cone $Z$ meet the line $H$ at the origin (a single angle when $\dim Z = 1$) then the endpoints of the line segment have respective norms $\|v\|/\sin(\theta_1)$ and $\|v\|/\sin(\theta_2)$. This settles our general claim about putting $(v + Z) \cap H$ inside a closed ball of radius $C\|v\|$ centered at $0$.

Using the now-established (A.4.1.9), if we shrink $\varepsilon_i$ further to make $C_1 x + M_1 \le 2C_1 x$ for all $x > |\log(\varepsilon_i)|$ then

$$
Z \cap (\mathscr{L}_S(g_i g) + H_{\mathrm{log}}) \subset B_0(2A_i C_1|\log|g|_{F,S}|)
$$

for all basic $g$ such that $|g|_{F,S} < \varepsilon_i$. Translating by $-\mathscr{L}_S(g)$ with Euclidean norm at most $C_1|\log(|g|_{F,S})| + M_i \le 2C_1|\log(|g|_{F,S})|$ yields that $(-\mathscr{L}_S(g_i g) + Z) \cap H_{\mathrm{log}}$ is contained in a closed ball $B_0(C_3|\log|g|_{F,S}|)$ for the real number $C_3 = 2(\max A_i)C_1 + 2C_1$ that is independent of such $g$ and $i$. Since $|g_i g|_{F,S} = |g|_{F,S}$, we can rename $C_3$ as $C_0$ to finish.

$\square$

We have proved the estimate in (A.4.1.8) for $g_i g$ for all $i$ and all $g$ basic such that $|g_i g|_{F,S} < \varepsilon$. We shall show that this in turn implies that (A.4.1.3) holds for $g_i g$ with $g$ basic such that $|g_i g|_{F,S} < \varepsilon$.

By Claim A.4.1.2, there exists $C_0 > 0$ such that

$$
(-\mathscr{L}_S(g_i g) + Z) \cap H_{\mathrm{log}} \subset B_0(C_0|\log|g_i g|_{F,S}|) \cap H_{\mathrm{log}}
$$

for all basic $g$ with $|g_i g|_{F,S} < \varepsilon$. The $\lambda_0$-measure of that ball is $C_1 C_0^{|S|-1} |\log|g_i g|_{F,S}||^{|S|-1}$ for some real number $C_1 > 0$ dependent on $|S|$ but not on $g$ nor $i$. Upon renaming $C_1 C_0^{|S|-1}$ as $C$, the estimate in (A.4.1.3) holds for all $g_i g$ with basic $g$ such that $|g_i g|_{F,S} < \varepsilon$. Since both $\sum_{\xi \in \mathcal{O}_{F,S}^\times} u(\xi g)$, and $|\log|g|_{F,S}||^{|S|-1}$ are $\mathcal{O}_{F,S}^\times$-invariant functions of $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$ and the points $g_i$ satisfy $|g_i|_{F,S} = 1$, we deduce that (A.4.1.3) holds for all $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$ such that $|g|_{F,S} < \varepsilon$.

$\square$

## PDF page 566

**566** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

**A.5. Idelic Hardy-Littlewood Maximal Theorem and Lebesgue Differentiation**

In this section we collect analogs of the Maximal Theorem on the Hardy-Littlewood maximal function (see [Fol, Thms.3.17,3.18]) and of Lebesgue's Differentiation Theorem (see [Fol, Thm.3.21]) for absolutely integrable functions on idele and $S$-idele groups and their quotient groups of idele classes. Our main reference is [HR-2, Ch. XI, pp. 637-672].

**A.5.1. Hardy-Littlewood Maximal Theorem on the real line.** We begin by recalling the elementary fact that for $f : \mathbf{R} \to \mathbf{R}$ a continuous function and every $x \in \mathbf{R}$, we have

$$
f(x) = \lim_{h \to 0^+} \frac{1}{2h} \int_{x-h}^{x+h} f(y)\,\mathrm{d}y. \tag{A.5.1.1}
$$

For $f$ discontinuous but measurable and locally integrable over $\mathbf{R}$ with respect to the Lebesgue measure, the identity in (A.5.1.1) remains valid for almost all $x \in \mathbf{R}$. This is the content of the $1$-dimensional Differentiation Theorem of Lebesgue, for which we refer the reader to [Fol, Thm.3.18] and [Fol, Thm.3.21].

In this section we discuss a generalization of the Differentiation Theorem, to locally integrable functions over a Hausdorff locally compact abelian group equipped with some additional structure, and with respect to a regular Radon measure.

A key tool to proving such analog of the Differentiation Theorem is an analog for Hausdorff locally compact abelian groups of the Hardy-Littlewood Maximal Theorem, which will be of interest itself and used throughout Chapter 6$^4$ of this work.

For $f : \mathbf{R} \to \mathbf{C}$ a measurable and absolutely integrable function, we define:

$$
(Mf)(x) := \limsup_{r > 0} \frac{1}{2r} \int_{x-r}^{x+r} |f(y)|\,\mathrm{d}y \tag{A.5.1.2}
$$

and refer to it as the Hardy-Littlewood Maximal Function of $f$. We illustrate the Hardy-Littlewood Maximal Theorem in the special case of the $1$-dimensional Euclidean space only, to explain the techniques used in the proof. We will then show how to use it to deduce Lebesgue's Differentiation Theorem.

A.5.1.1. *$1$-dimensional Hardy-Littlewood Maximal Theorem.* In the $1$-dimensional case for functions over the real line, it asserts the following:

THEOREM A.5.1.1 (Hardy-Littlewood Maximal Theorem over $\mathbf{R}$). Let $f : \mathbf{R} \to \mathbf{C}$ be a measurable function.

(1) *If $f \in L^1_{\mathrm{loc}}(\mathbf{R},\mathrm{d}x)$ is such that $f \log^+|f|) \in L^1_{\mathrm{loc}}(\mathbf{R},\mathrm{d}x)$, with $\log^+(u) := \max\{\log(u),0\}$ for $u > 0$, then $Mf$ is measurable and finite almost everywhere.*

(2) *If $f \in L^1(\mathbf{R},\mathrm{d}x)$ then for any real number $\alpha > 0$, we have:*

$$
|\{x \in \mathbf{R} : (Mf)(x) > \alpha\}| \le \frac{3}{\alpha} \|f\|_{L^1(\mathbf{R},\mathrm{d}x)}. \tag{A.5.1.3}
$$

(3) *For $p > 1$, if $f \in L^p(\mathbf{R},\mathrm{d}x)$ then there exists a real number $C_p > 0$ independent of $f$ such that*

$$
\|Mf\|^p_{L^p(\mathbf{R},\mathrm{d}x)} \le \frac{2^p \cdot 3p}{p-1} \|f\|^p_{L^p(\mathbf{R},\mathrm{d}x)}. \tag{A.5.1.4}
$$

PROOF. (1) : We note that $Mf$ is measurable since the function of $x$ given by $\frac{1}{2r} \int_{x-r}^{x+r} |f(x)|\,\mathrm{d}y$ is continuous for every $r > 0$. We let $r > 0$ be an arbitrary real number. Since $f \in L^1_{\mathrm{loc}}(\mathbf{R},\mathrm{d}x)$, $f \cdot \mathrm{1}_{[-r,r]}$ is absolutely integrable over $\mathbf{R}$. Following the proof of [HR-2, Ch. XI, 44.50(d), p. 670], we choose an arbitrary

---
$^4$Put in labels to refer to Chapters 10-11 instead

## PDF page 567

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **567**

real number $0 < \delta < 1$ and have for some real number $C_0 > 0$ independent of $f$:

$$
\int_{[-r,r]} (Mf)(y)\,\mathrm{d}y = \int_0^{+\infty} |[-r,r] \cap \{x \in \mathbf{R} : (Mf)(x) > y\}|\,\mathrm{d}y \tag{A.5.1.5}
$$

$$
= \int_0^{1/\delta} |[-r,r] \cap \{x \in \mathbf{R} : (Mf)(x) > y\}|\,\mathrm{d}y + \int_{1/\delta}^{+\infty} |[-r,r] \cap \{x \in \mathbf{R} : (Mf)(x) > y\}|\,\mathrm{d}y
$$

$$
\le \frac{2r}{\delta} + \int_{1/\delta}^{+\infty} \left\{ \frac{C_0}{(1-\delta)y} \int_{[-r,r]} |\{x \in \mathbf{R} : |f(x)| > \delta y\}| \cdot |f(x)|\,\mathrm{d}x \right\} \mathrm{d}y
$$

where we used [HR-2, Ch. XI, 44.50(a.ii), p. 669] to obtain the last inequality.

We now apply [Fol, Thm. 7.27] to the Lebesgue measure $\mu$ on $\mathbf{R}$, $\varphi(y) = \log(y)$, and $E = [-r,r]$, to obtain:

$$
\frac{C_0}{(1-\delta)} \int_{1/\delta}^{+\infty} \left\{ \int_{[-r,r]} |\{x \in \mathbf{R} : |f(x)| > \delta y\}| \cdot |f(x)|\,\mathrm{d}x \right\} \frac{\mathrm{d}y}{y} = \frac{C_0}{(1-\delta)} \int_{x \in [-r,r]} |f(x)| \int_1^{+\infty} |\{y \in \mathbf{R} : |f(x)| > y\}| \frac{\mathrm{d}y}{y}\,\mathrm{d}x \tag{A.5.1.6}
$$

$$
= \frac{C_0}{(1-\delta)} \int_{x \in [-r,r]} |f(x)| \log^+|f(x)|\,\mathrm{d}x \tag{A.5.1.7}
$$

which gives the local integrability of $Mf$ over $\mathbf{R}$, and hence its finiteness almost everywhere.

(2) : By (1), $Mf$ is measurable and finite almost everywhere over $\mathbf{R}$. By [StSha-III, Ch. 3, §1, Thm. 1.1(iii), p. 101] we deduce that (A.5.1.3) holds.

(3) : We proceed directly as follows. For every real number $\delta \ge 0$, we define $F_\delta(x) := f(x)$ if $|f(x)| > \delta/2$, and $F_\delta(x) := 0$ otherwise. We therefore have $|f(x)| \le |F_\delta(x)| + \delta/2$ for all $x \in \mathbf{R}$.

We note that $F_\delta$ is absolutely integrable for every $\delta > 0$, since, by [Fol, Thm. 6.17], we have:

$$
|\{x \in \mathbf{R} : |f(x)| > \delta/2\} \le \frac{2^p}{\delta^p} \|f\|^p_{L^p(\mathbf{R},\mathrm{d}x)}
$$

for every $\delta > 0$, and hence $F_\delta(x)$ is nonzero only on a measurable subset of $\mathbf{R}$ of finite Lebesgue measure.

We apply (2) to $F_\delta$ for each $\delta > 0$. By (2), we obtain:

$$
|\{x \in \mathbf{R} : (Mf)(x) > \delta\}| \le |\{x \in \mathbf{R} : (MF_\delta)(x) > \delta/2\}| \le \frac{2 \cdot 3}{\delta} \int_{\mathbf{R}} |F_\delta(x)|\,\mathrm{d}x = \frac{2 \cdot 3}{\delta} \int_{|f(x)| > \delta/2} |f(x)|\,\mathrm{d}x. \tag{A.5.1.8}
$$

By Fubini's Theorem,

$$
\|Mf\|^p_{L^p(\mathbf{R},\mathrm{d}x)} = \int_{\mathbf{R}} |(Mf)(x)|^p\,\mathrm{d}x = p \int_0^{+\infty} y^{p-1} |\{x \in \mathbf{R} : (Mf)(x) > y\}|\,\mathrm{d}y. \tag{A.5.1.9}
$$

By combining (A.5.1.9) and (A.5.1.8) we obtain:

$$
\|Mf\|^p_{L^p(\mathbf{R},\mathrm{d}x)} \le 2 \cdot 3p \int_0^{+\infty} \int_{|f(x)| > y/2}^{+\infty} y^{p-2} |f(x)|\,\mathrm{d}x\,\mathrm{d}y = 2^p \cdot 3p \int_0^{+\infty} \int_{|f(x)| > y} y^{p-2} |f(x)|\,\mathrm{d}x\,\mathrm{d}y \tag{A.5.1.10}
$$

and Fubini's Theorem (along with the equality $\int_0^a y^{p-1}\,\mathrm{d}y/y = a^{p-1}/(p-1)$) gives

$$
\int_0^{+\infty} \int_{|f(x)| > y} y^{p-2} |f(x)|\,\mathrm{d}x\,\mathrm{d}y = \frac{1}{p-1} \int_{\mathbf{R}} |f(x)|^{p-1} |f(x)|\,\mathrm{d}x = \frac{1}{p-1} \|f\|^p_{L^p(\mathbf{R},\mathrm{d}x)}. \tag{A.5.1.11}
$$

Upon combining (A.5.1.11) and (A.5.1.10) we deduce that (A.5.1.4) holds. $\square$

## PDF page 568

**568** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

REMARK A.5.1.2. Since $M$ is a quasi-linear$^5$ operator on measurable functions on $\mathbf{R}$, we may apply the Interpolation Theorem of Marcinkiewicz (see [HuWe, p.996-998]) to deduce (A.5.1.4) from (2), after reducing to the case $f$ is nonnegative and compactly supported.

We refer the reader to [StSha-III, Ch. 3, §1, Thm. 1.1, p. 101] for the case of functions on $\mathbf{R}^d$ for every $d \ge 1$ in the case $p = 1$. We further refer the reader to [Fol, Thm.3.17] for the maximal theorem in the case $d \ge 1$ and $p = 1$, where the method of proof gives indeed the constant $3^d$ in place of $3$ in (A.5.1.3), resting on the Vitali-type Covering Lemma in [Fol, Lemma 3.15] (see also [StSha-III, Ch.3, §1, Lemma 1.2, p. 102]).

A similar argument as for (3) in Theorem A.5.1.1 generalizes the case $p > 1$ to the case of $d$-dimensional real Euclidean spaces. The dependence on the dimension of the constant that appears in the $d$-dimensional analog of (A.5.1.4) for $p > 1$, can be removed (see [StStr, Thm. A], building on previous work of E. Stein on spherical maximal functions).

The inequality in (A.5.1.3) is called weak $(1,1)$-type while (A.5.1.4) is called strong $(p,p)$-type.

A.5.1.2. *$1$-dimensional Lebesgue Differentiation Theorem.* Using the weak $(1,1)$-estimate from (A.5.1.3) for the Hardy-Littlewood maximal function, we can prove the following Theorem of Lebesgue:

THEOREM A.5.1.3 (Lebesgue's Differentiation Theorem). *Let $f \in L^1_{\mathrm{loc}}(\mathbf{R},\mathrm{d}x)$ be a locally integrable function on $\mathbf{R}$. Then, for almost all $x \in \mathbf{R}$, the following identity:*

$$
f(x) = \lim_{r \to 0^+} \frac{1}{2r} \int_{x-r}^{x+r} f(y)\,\mathrm{d}y \tag{A.5.1.12}
$$

holds.

PROOF. It is enough to treat the case of real-valued $f$. We define the local-at-$x$ "oscillation" of $f$, denoted $\omega_f(x)$, as follows. For every $x \in \mathbf{R}$, we define:

$$
\omega_f(x) := \left| \limsup_{r \to 0^+} \frac{1}{2r} \int_{x-r}^{x+r} f(y)\,\mathrm{d}y - \liminf_{r \to 0^+} \frac{1}{2r} \int_{x-r}^{x+r} f(y)\,\mathrm{d}y \right|. \tag{A.5.1.13}
$$

We fix a real number $r_0 > 0$, large enough so as to have $x \in (-r_0,r_0)$, and consider $F_{r_0} := \mathrm{1}_{[-r_0,r_0]} \cdot f$.

By [Fol, Prop. 7.9], for every real number $\varepsilon > 0$, there exists a continuous compactly supported function $\varphi \in C_c(\mathbf{R})$ such that $\|F_{r_0} - \varphi\|_{L^1(\mathbf{R},\mathrm{d}y)} < \varepsilon$. We call $g := F_{r_0} - \varphi$, and note that we have $\omega_{F_{r_0}}(y) = \omega_g(y)$, since $\omega_\varphi(y) = 0$ for every $y \in \mathbf{R}$ by continuity of $\varphi$.

Since $\omega_g \le 2Mg$, by (A.5.1.3) from Theorem A.5.1.1(2) we have for every $\alpha > 0$ that

$$
|\{y \in \mathbf{R} : \omega_{F_{r_0}}(y) > \alpha\}| \le \frac{2 \cdot 3}{\alpha} \|g\|_{L^1(\mathbf{R},\mathrm{d}y)} < \frac{2 \cdot 3\varepsilon}{\alpha} \tag{A.5.1.14}
$$

and $\varepsilon > 0$ being arbitrary, we deduce that $\{y \in \mathbf{R} : \omega_{F_{r_0}}(y) > \alpha\}$ has Lebesgue measure zero; i.e., $A_rF_{r_0}(x) := \frac{1}{2r} \int_{x-r}^{x+r} F_{r_0}(y)\,\mathrm{d}y$ converges almost everywhere as $r \to 0^+$. To identify the limit it is enough to find a sequence of real numbers $0 < r < r_0$ on which it is possible to do so. We have $\|F_{r_0} - A_rF_{r_0}\|_{L^1(\mathbf{R},\mathrm{d}y)} \to 0$,$^6$ and hence there exists such a sequence such that $(A_rF_{r_0})(x) \to F_{r_0}(x)$ for almost all $x \in (-r_0,r_0)$.

We let $x \in (-r_0,r_0)$ be such that $A_rF_{r_0}(x)$ converges as $r \to 0^+$. It follows that $\lim_{r \to 0^+} A_rF_{r_0}(x) = \lim_{r \to 0^+} \frac{1}{2r} \int_{x-r}^{x+r} f(y)\,\mathrm{d}y$, since such limit equals the limit as $r > 0$ tends to zero while varying over the positive reals $r \in (0,r_1)$, with $r_1$ small enough so as to have $(x-r_1,x+r_1) \subset (-r_0,r_0)$.

We now let $N_k \subset (-k,k)$ be the null set of those points at which (A.5.1.12) does not hold. We have, for every integer $k \ge 1$, $N_k \subset N_{k+1}$, and hence $|\bigcup_{k \ge 1} N_k| = \lim_{k \to +\infty} |N_k| = 0$. We deduce that (A.5.1.12) holds almost everywhere over the real line. $\square$

---
$^5$Means what? Do we care?

$^6$Should briefly explain this convergence to 0

## PDF page 569

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **569**

**A.5.2. $D$-sequences, $D'$-sequences, $D''$-sequences in Hausdorff locally compact abelian groups.** We will be recording, throughout this subsection and the next, analogs of both Theorem A.5.1.1 and Theorem A.5.1.3, when $\mathbf{R}$ is replaced by a Hausdorff locally compact abelian group $G$ equipped with a decreasing sequence of Borel measurable subsets satisfying certain axioms.

This is discussed in detail in [HR-2, Ch.XI,§44,44.50], the proofs are close in structure and technique to those presented above for Theorem A.5.1.1 and Theorem A.5.1.3, and we will be only providing complementary details to the arguments in loc.cit..

We will then show that the structural assumptions on $G$ are all satisfied by all the Hausdorff locally compact abelian groups of interest to this work, i.e. $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, $C_F$, $C_{F,S}$ and $J_{F,S}$, and closed subgroups of norm-$1$ elements, for $F$ a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

The ability to use analogs of the Hardy-Littlewood maximal function for these choices of $G$, and the analog of both the Maximal Theorem and Lebesgue's Differentiation Theorem, will be instrumental for us to make sense of certain measurable kernel functions over self-products of the above groups, along their diagonal, and compute their integrals on such diagonals (used to compute some nuclear operator traces).

We refer the reader to [Bris-a, Bris-b] for related techniques, aimed at computing traces of trace-class integral operators on $L^2$-spaces of a large class of metric measure spaces.

A.5.2.1. *$D$-sequences and $D'$-sequences in Hausdorff locally compact abelian groups.* We begin with a definition, introducing the additional structure on a Hausdorff locally compact abelian group for an analog of the Hardy-Littlewood maximal function to be available, and for analogs of the Hardy-Littlewood Maximal Theorem and Lebesgue's Differentiation Theorem to hold.

DEFINITION A.5.2.1. Let $G$ be a Hausdorff locally compact abelian group. Let $\lambda$ be a Haar measure on $G$. Let $\{U_k\}_{k \ge 0}$ be a sequence of $\lambda$-measurable subsets in $G$ with $e \in U_k$ for all $k$. We call $\{U_k\}_{k \ge 0}$ a $D$-sequence in $G$ if $\{U_k\}_{k \ge 0}$ satisfies the following conditions:

(1) (Integrability) For every integer $k \ge 0$, $\lambda(U_k)$ is finite and nonzero.

(2) (Monotonicity) For every integer $k \ge 0$, we have $U_{k+1} \subset U_k$.

(3) (Doubling) There exists a positive real number $C > 0$ such that, for every integer $k \ge 0$, we have:

$$
0 < \lambda(U_k U_k^{-1}) < C\,\lambda(U_k). \tag{A.5.2.1}
$$

We say a $D$-sequence $\{U_k\}_{k \ge 0}$ is open, respectively symmetric, if and only if for each integer $k \ge 0$, $U_k$ is open, respectively symmetric.

We say a $D$-sequence $\{U_k\}_{k \ge 0}$ is a $D'$-sequence in $G$ if and only if for every neighborhood $V$ of the neutral element in $G$, there exists an integer $k \ge 0$ such that $U_k \subset V$.

REMARK A.5.2.2. The preceding definition can be pushed a bit further: a $D'$-sequence $\{U_k\}_{k \ge 0}$ is called a $D''$-sequence in $G$ if and only if it is a $D'$-sequence and there exists a specified sequence $\{V_k\}_{k \ge 0}$ of $\lambda$-measurable subsets of $G$ satisfying $V_k V_k^{-1} \subset U_k$ for every integer $k \ge 0$ and a positive real number $C' > 0$ such that, for every integer $k \ge 0$, we have:

$$
\lambda(U_k) \le C'\,\lambda(V_k). \tag{A.5.2.2}
$$

One usually writes $\{U_k,V_k\}_{k \ge 0}$ for the datum of a $D''$-sequence in $G$. We will not use this concept.

Before we state and prove analogs of the Hardy-Littlewood Maximal Theorem and the Lebesgue Differentiation Theorem, we discuss criteria for a Hausdorff locally compact abelian group to admit a $D$-sequence, respectively a $D'$-sequence.

## PDF page 570

**570** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

PROPOSITION A.5.2.3. *Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a choice of Haar measure on $G$.*

(1) *If $G$ is first countable and locally profinite, then it admits a $D''$-sequence of the form $\{U_k,V_k\}_{k \ge 0}$, with, for each integer $k \ge 0$, $U_k = U_k^{-1}$, $V_k = U_k^2$, $C' = 1$, and $U_k$ is a compact open subgroup of $G$.*

(2) *Let $H \subset G$ be an open subgroup. Let $\{U_k\}_{k \ge 0}$ be a sequence of subsets of $H$. Then $\{U_k\}_{k \ge 0}$ is a $D$-sequence, respectively a $D'$-sequence, for $H$ if and only if it is so for $G$. It is open, respectively symmetric, for $H$ if and only if it is so for $G$.*

PROOF. (1) : By [DE, Thm. 4.1.6] and [DE, Prop. 4.1.5], $G$ admits a unit-neighborhood base comprised of compact open subgroups. We may assume such base to be countable. Indeed, for every countable unit-neighborhood base $B$ of $e$ we may find for each $U \in B$ an open, hence closed (hence compact open) subgroup $N_U \subset U$. The subset $\{N_U : U \in B\}$ is a countable unit-neighborhood base comprised of compact open subgroups. We may extract a cofinal sequence $\{U_k\}_{k \ge 0}$ from it.

Since $U_k$ is a subgroup for each integer $k \ge 0$, we have $U_k^{-1} = U_k$ and $U_k U_k^{-1} \subset U_k$. The sequence $\{U_k\}_{k \ge 0}$ is therefore an open symmetric $D$-sequence, with the choice $C = 1$.

Since $\{U_k\}_{k \ge 0}$ is cofinal in a neighborhood base of the neutral element in $G$, for any neighborhood $V$ of the neutral element in $G$ there exists a large enough integer $k \ge 0$ with $U_k \subset V$. The $D$-sequence $\{U_k\}_{k \ge 0}$ is therefore a $D'$-sequence.

(2) : Since $\mu_G|_H$ is a Haar measure for $H$, for every $\mu_G$-measurable subset $A \subset G$ we see that $A \cap H$ is $\mu_H$-measurable and $\mu_H(A \cap H) = \mu_G(A \cap H)$. In particular, if $A \subset H$ then $\mu_H(A) = \mu_G(A)$. This implies that all the defining conditions on the $D$-sequence, respectively $D'$-sequence $\{U_k\}_{k \ge 0}$ for $G$ hold for the same sequence as a $D$-sequence, respectively $D'$-sequence for $H$. $\square$

REMARK A.5.2.4. Let $G$ be a countable discrete abelian group. Then $U_k := \{e\}$ for every integer $k \ge 0$, is an open, symmetric $D$-sequence, a $D'$-sequence, and $\{U_k,U_k\}_{k \ge 0}$ is a $D''$-sequence. Indeed, every Haar measure $\lambda$ on $G$ is proportional to the counting measure by [DE, Prop.1.4.4], the constant of proportionality given by $c := \lambda(\{e\}) \ne 0$.

It follows that, under the above choices, $\lambda(U_k) = c$ for every $k \ge 0$, and $U_{k+1} \subset U_k$. The doubling condition holds with $C = 2$. Since every unit-neighborhood of $G$ contains $e$, $\{U_k\}_{k \ge 0}$ is a $D'$-sequence.

Upon choosing $V_k := U_k$ for every integer $k \ge 0$, and $C' = 1$, then $\lambda(U_k) = \lambda(V_k)$, and hence (A.5.2.2) holds too, and $\{U_k,V_k\}_{k \ge 0}$ is a $D''$-sequence.

LEMMA A.5.2.5. *Let $G_1,G_2$ be Hausdorff locally compact abelian groups, and let $G := G_1 \times G_2$ be the product topological group. Let $\mu_1,\mu_2$ be Haar measures on $G_1$, respectively $G_2$. Let $\mu := \mu_1 \otimes \mu_2$ be the product Haar measure on $G$. Let $\{U_k\}_{k \ge 0}$ be a sequence of $\mu_1$-measurable subsets in $G_1$, and $\{U'_k\}_{k \ge 0}$ a sequence of $\mu_2$-measurable subsets in $G_2$. If $\{U_k\}_{k \ge 0}$ is a $D$-sequence, respectively a $D'$-sequence, for $G_1$, and $\{U'_k\}_{k \ge 0}$ is a $D$-sequence, respectively a $D'$-sequence, for $G_2$, then $\{U_k \times U'_k\}_{k \ge 0}$ is a $D$-sequence, respectively a $D'$-sequence, for $G$. For each integer $k \ge 0$, if $U_k$ and $U'_k$ are open, respectively symmetric, then so is $U_k \times U'_k$.*

PROOF. Since, for any two measurable subsets $B_1 \subset G_1$, $B_2 \subset G_2$, we have $\mu(B_1 \times B_2) = \mu_1(B_1)\mu_2(B_2)$, and since the property of being an open subset respectively a symmetric subset is stable under finite products, all defining conditions for $\{U_k \times U'_k\}_{k \ge 0}$ follow from those of $\{U_k\}_{k \ge 0}$, respectively $\{U'_k\}_{k \ge 0}$. $\square$

PROPOSITION A.5.2.6. *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is second-countable. Let $H \subset G$ be a closed subgroup. Let $\mu_H$ be a choice of Haar measure on $H$, $\mu_G$ a choice of Haar measure on $G$, and $\mu_{G/H}$ the unique Haar measure on $G/H$ induced by the choices $\mu_G$ on $G$ and $\mu_H$ on $H$ as per Theorem D.1.2.1. Assume $H$ is discrete, and normalize $\mu_H$ so as to have $\mu_H(\{1\}) = 1$. Let $q : G \to G/H$ be the continuous quotient homomorphism.*

*Assume that there exists a relatively compact Borel subset $E \subset G$ whose interior is non-empty and contains the neutral element, and such that the continuous map $q|_E : E \to G/H$ is a bijection.*

## PDF page 571

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **571**

*Let $\{U_k\}_{k \ge 0}$ be a sequence of Borel sets in $G/H$ such that $U_{k+1} \subset U_k$ for every integer $k \ge 0$. Then $\{U_k\}_{k \ge 0}$ is a $D$-sequence for $G/H$, respectively a $D'$-sequence for $G/H$, if and only if*

$$
\{q^{-1}(U_k) \cap E\}_{k \ge 0}
$$

*is a $D$-sequence, respectively a $D'$-sequence, for $G$. If $E$ is symmetric then $\{U_k\}_{k \ge 0}$ is symmetric if and only if $\{q^{-1}(U_k) \cap E\}_{k \ge 0}$ is.*

REMARK A.5.2.7. In light of Lemma A.5.2.10 below, if $H$ is discrete then there exists a Borel section to $q : X \to X/H$. Discreteness of $H$ is essential to ensure that such Borel section $F \subset X$ (i.e. a Borel subset $F$ such that $q|_F$ is a continuous bijection) can be used to compute the $\mu_{G/H}$-measure of measurable subsets $A$ in $X/H$, by computing the $\mu_G$-measure of $q^{-1}(A) \cap F$.

Before proving the Proposition, we record here the following result from [Kech, Ch. II, §15, Thm. 15.1] for which we need only an elementary special case:

THEOREM A.5.2.8 (Lusin-Souslin Theorem on Borel embeddings). *Let $X,Y$ be separable and completely metrizable$^7$ topological spaces, $f : X \to Y$ a continuous map.*

*For $B \subset X$ a Borel set, if $f|_B$ is injective then $f(B) \subset Y$ is a Borel set.*

We only need this for the quotient map $G \to G/H$ with $G$ a second-countable locally compact topological abelian group and $H$ a discrete subgroup. In such cases, we can pick a fundamental domain $F \subset G$ with $\mu(\partial F) = 0$ (for a Haar measure $\mu$ on $G$) such that $\mathrm{Int}(F) \to G/H$ is a homeomorphism onto an open image who complement in $G/H$ has measure $0$. In such cases. the conclusion of Theorem A.5.2.8 is clear when we complete the $\sigma$-algebra of Borel sets (i.e., we regard all measure-$0$ sets as Borel sets).

REMARK A.5.2.9 (Spherical boundedness and second-countability). Let $G$ be a Hausdorff locally compact abelian group. As such, it is a completely regular topological space (see [Fol, Cor. 4.33]), i.e. for a point $x \in G$ and a closed subset $A \subset G$ not containing $x$, there exists a continuous real-valued function $f$ on $G$ such that $f(x) = 1$ and $f(A) = \{0\}$. In making this deduction, the group structure and continuity of the group operations, is not being used.

First countability is in fact a necessary and sufficient condition for a Hausdorff topological group to be metrizable (i.e. the underlying topology, uniformizable in the sense of [Bou-GT, Ch. II, §4.1, Def. 1, p. 198], see [Bou-GT, Ch. III, §3.1, Def. 1, p. 243], which is to mean that it is induced by a uniform structure, is in fact metrizable, which is to mean it is induced by a metric); see [Birkhoff, Theorem, p. 428].

The metric inducing the topology can be chosen to be left-invariant, and a direct construction is given in [Struble, Lemma 1, p. 217].

The second axiom of countability for Hausdorff locally compact topological groups $G$ (not necessarily abelian) is characterized by boundedness of the spheres with respect to a left-invariant metric inducing the topology: this is [Struble, Theorem, p. 217]. Recall that a subset $B \subset G$ is called bounded if for any unit-neighborhood $U$, there exist finitely many $g_1,\dots,g_N$ such that $g_1U \cup \dots \cup g_NU$ contains $B$ (i.e. $B$ is "totally bounded" with respect to the uniform structure on $G$; we refer the reader to [Bou-GT, Ch. II, Exercises, §4,(7), p. 210]).

If $G$ is a Hausdorff locally compact second countable topological group, then there exists a family of open subsets $\{U_r\}_{r \in \mathbf{R}_{>0}}$ such that, for all real numbers $r_1,r_2 > 0$, $U_r$ is bounded and symmetric, and $U_{r_1}U_{r_2} \subset U_{r_1+r_2}$, and such that $\{U_r\}_{r > 0}$ is a unit-neighborhood base, and $\bigcup_{r > 0} U_r = G$. This is [Struble, Lemma 2, p. 218].

We record here the following general existence result for Borel fundamental domains:$^8$

---
$^7$Need to record meaning, criteria, and relevant examples of "completely metrizable"

$^8$Why is this being recorded? It is never needed in such generality.

## PDF page 572

**572** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

LEMMA A.5.2.10. *Let $X$ be a Hausdorff locally compact topological space. Assume $X$ is second countable. Let $H$ be a countable discrete abelian group acting on $H$ properly and freely. Let $q : X \to X/H$ be the continuous quotient.*

*Let $E \subset X$ be a Borel subset such that $q|_E : E \to X/H$ is injective. Then there exists a Borel subset $F \subset X$ such that $E \subset F$ and the continuous $q|_F : F \to X/H$ is a bijection.*

PROOF. Since $X$ is Hausdorff locally compact and second countable, there exists an exhaustion of $X$ by a sequence of compact subsets $\{K_m\}_{m \ge 0}$. We denote by $q_m : K_m \to X/H$ the composition of the continuous inclusion $K_m \subset X$ followed by the quotient map $q$. For each integer $m \ge 1$, $K_m$ is metrizable by the Urysohn Metrization Theorem, since it is Hausdorff, compact, second countable.

By [Bog, Vol. 2, Ch. 6, Thm. 6.9.7, p. 38] applied to $Y = X/H$, which is Hausdorff since the action of $H$ on $X$ is proper (see [Bou-GT, Ch. III, §4.4, Prop. 8(b), p. 256]), and for $f = q_m$ for every integer $m \ge 0$ there exists a Borel subset $B_m \subset K_m$ such that $q_m(B_m) = q_m(K_m)$, with $q_m$ injective on $B_m$, and the set-theoretic inverse map $q_m^{-1} : q_m(K_m) \to B_m$ is Borel.

It follows that we have $q(\bigcup_{m \ge 0} B_m) = X/H$, since $\bigcup_{m \ge 0} q(K_m) = X/H$. Since $H$ is countable, the set of the $B_m$'s and all of their $H$-translates is comprised of Borel subsets $B \subset X$ such that $q|_B : B \to X/H$ is injective, and such that $X$ is covered by their union. We define $\mathcal{B}$ to be the set of all the $H$-translates of the $B_m$'s, and of $E$. Clearly $\mathcal{B}$ is countable.

We enumerate the elements $\{U_k\}_{k \ge 1} = \mathcal{B}$ setting $U_0 := E$ and $U_{-1} := \varnothing$. We define $U'_0 := U_0$ and, for each integer $k \ge 1$:

$$
U'_k := U_k \cap (X - (\bigcup_{0 \le i \le k-1} H \cdot U_i)) \tag{A.5.2.3}
$$

and set $F := \bigcup_{k \ge 0} U'_k$. Then $F$ contains $E$, and it is a Borel subset of $X$, since each $U'_k$ is.

We have $q(F) = X/H$. Indeed, each $U_k$ is contained in the union $\bigcup_{k \ge 0} H \cdot U'_k$, and hence $q(U_k)$ is contained in $q(\bigcup_{k \ge 0} U'_k) = q(F)$ for every integer $k \ge 0$. Since $\bigcup_{k \ge 0} U_k = X$, we deduce $q(F) = X/H$.

For any $h \in H$, $h \ne 1$, we have $h \cdot F \cap F = \varnothing$. Indeed, $(h \cdot U'_k) \cap U'_{k'}$ is non-empty only if $k = k'$, in which case, since $q|_{U_k}$ is injective, we must have $h = 1$: if $x \in U'_k$ is such that $y := h \cdot x \in U'_k$, then $q(x) = q(y)$, which forces $y = x$ and hence $h = 1$. Since $U'_k$ and $U'_{k'}$ are disjoint for all pairs of integers $(k,k')$ with $k \ne k'$, we deduce that we have $h \cdot F \cap F = \varnothing$ for all $h \in H$ with $h \ne 1$. It follows that the continuous $q|_F : F \to X/H$ is a bijection. $\square$

Proof of Proposition A.5.2.6. We note that since $q$ is continuous, for any Borel subset $B \subset G/H$ clearly $q^{-1}(B)$ is a Borel subset of $G$.

By [Klee, (2.4), p. 487], since $G$ admits a countable unit-neighborhood base, and each member of such base is invariant under all inner automorphisms of $G$ (since $G$ is abelian), $G$ admits an invariant metric $d$ (i.e. both left- and right-invariant).

By [Klee, (2.5), p. 487], the invariant metric on $G$ promotes $G$ to a complete metric space $(G,d)$. Indeed, if $\{g_k\}$ is a Cauchy sequence and we consider all $k,m$ large enough so that $g_k g_m^{-1} \in \overline{U}$ for a chosen $e$-neighborhood $U$ in $G$. We can arrange that $\overline{U}$ is compact, so convergence of the Cauchy sequence follows.

We deduce that $G$ is completely metrizable,$^9$ and there exists an invariant complete metric on $G$. Since $G$ is second-countable by assumption, it is a second-countable completely metrizable space and hence it is separable. In particular, Theorem A.5.2.8 applies with $X = G$ and $Y = G/H$, since the quotient $q : G \to G/H$ is open and hence $G/H$ is also second countable and (as for $G$) completely metrizable, hence separable and completely metrizable.

By Theorem A.5.2.8, for every subset $B \subset G$, since $q|_{B \cap E}$ is injective (being injective on $E$ itself), then if $B \cap E$ is Borel so is $q(B \cap E)$. If $B = q^{-1}(q(B))$ set-theoretically, then $q(B \cap E) = q(B)$.

---
$^9$what does "completely metrizable" mean?

## PDF page 573

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **573**

We now observe that by Lemma A.5.2.10, there exists a Borel subset $F \subset G$ such that $q|_F : F \to G/H$ is a continuous bijection and $F$ contains $E$. For every measurable subset $A \subset G/H$ with finite $\mu_{G/H}$-measure, the indicator function $\mathbf{f} := \mathrm{1}_{q^{-1}(A) \cap F}$ of $q^{-1}(A) \cap F$ is $\mu_G$-integrable by [Bou-II, Ch. VII, §2, No. 3, Prop. 5(d), INT VII.33] applied to $X = G$, $\lambda^\sharp = \mu_G$, $\lambda = \mu_{G/H}$, and $\beta = \mu_H$. Indeed, we have

$$
\int_{G/H} \int_H \mathrm{1}_{q^{-1}(A) \cap F}(h^{-1}x)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_{G/H}(q(x)) = \int_{G/H} \mathrm{1}_A(\pi(x))\,\mathrm{d}\mu_{G/H}(\pi(x)) = \mu_{G/H}(A). \tag{A.5.2.4}
$$

Here we are using discreteness of $H$ once more: not only through Lemma A.5.2.10, but also through the equality $\mu_H(\{h\}) = 1$. By (A.5.2.4) and Lemma D.1.2.3 we see that indeed $\mathrm{1}_{q^{-1}(A) \cap F}$ is $\mu_G$-integrable, and hence [Bou-II, Ch. VII, §2, No. 3, Prop.5(c), INT VII.33] applies.

We have $\mathbf{f}^\flat = \mathrm{1}_A$, in the notation from loc.cit., and so by [Bou-II, Ch. VII, §2, No. 3, Prop. 5(c),(12), INT VII.33] we have:

$$
\mu_G(q^{-1}(A) \cap F) = \mu_{G/H}(A). \tag{A.5.2.5}
$$

In particular, upon choosing $A$ contained in $q(E)$, we obtain $q^{-1}(A) \cap F = q^{-1}(A) \cap E$, and so we have:

$$
\mu_G(q^{-1}(A) \cap E) = \mu_{G/H}(A). \tag{A.5.2.6}
$$

We can now prove the Proposition.

(1) : Let $\{U_k\}_{k \ge 0}$ be a Borel $D$-sequence for $G/H$ contained in $q(E)$. Then $\{q^{-1}(U_k) \cap E\}_{k \ge 0}$ is a sequence of Borel subsets of $G$ such that $q^{-1}(U_{k+1}) \cap E \subset q^{-1}(U_k) \cap E$ and by (A.5.2.6) we have $\mu_G(q^{-1}(U_k) \cap E) = \mu_{G/H}(U_k)$ for every integer $k \ge 0$. The integrability, monotonicity and doubling conditions for $\{q^{-1}(U_k) \cap E\}_{k \ge 0}$ are therefore satisfied, and hence $\{q^{-1}(U_k) \cap E\}_{k \ge 0}$ is a Borel $D$-sequence for $G$.

Conversely, if $\{q^{-1}(U_k) \cap E\}_{k \ge 0}$ is a Borel $D$-sequence for $G$, then by Theorem A.5.2.8 each image $q(q^{-1}(U_k) \cap E) = U_k$ is a Borel subset of $G/H$ and by (A.5.2.6) applied to $A = U_k$, we deduce that $\mu_{G/H}(U_k) = \mu_G(q^{-1}(U_k) \cap E)$. Thus, the integrability, monotonicity and doubling conditions for $U_k$ are satisfied, so $\{U_k\}_{k \ge 0}$ is a Borel $D$-sequence for $G/H$ entirely contained in $q(E)$.

Assume that every unit-neighborhood in $G/H$ contains some $U_k$, for some integer $k \ge 0$. Let $V$ be an arbitrary unit-neighborhood in $G$. We want to prove that there exists an integer $k \ge 0$ such that $q^{-1}(U_k) \cap E$ is contained in $V$. Since $V$ contains an open unit-neighborhood, we may assume $V$ is open.

Then $V \cap \mathrm{Int}(E)$ is also an open unit-neighborhood in $G$, and hence $q(V \cap E)$ is a unit-neighborhood in $G/H$ since $q$ is open and a group homomorphism. We choose an integer $k \ge 0$ such that $q(V \cap E)$ contains $U_k$. Since $q|_E$ is injective, we deduce that $V \cap E$ contains $q^{-1}(U_k) \cap E$, and hence we have $q^{-1}(U_k) \cap E \subset V$. We deduce that if $\{U_k\}_{k \ge 0}$ is a $D'$-sequence for $G/H$ contained in $q(E)$, then $\{q^{-1}(U_k) \cap E\}_{k \ge 0}$ is a $D'$-sequence for $G$.

Conversely, assume that $\{q^{-1}(U_k) \cap E\}_{k \ge 0}$ is a $D'$-sequence for $G$ (so $\{U_k\}$ is a $D$-sequence for $G/H$ by what has already been done). Let $V \subset G/H$ be an arbitrary unit-neighborhood. Then $q^{-1}(V)$ is a unit-neighborhood in $G$. There exists an integer $k \ge 0$ such that $q^{-1}(U_k) \cap E \subset q^{-1}(V)$, which implies that we have $q(q^{-1}(U_k) \cap E) \subset V$. Since $q(q^{-1}(U_k) \cap E) = U_k$, we deduce that we have $U_k \subset V$, and hence $\{U_k\}_{k \ge 0}$ is a $D'$-sequence for $G/H$.

Assume now that $E$ is symmetric, i.e. $E^{-1} = E$. Since $q$ is a homomorphism, then $U_k$ is symmetric if $q^{-1}(U_k) \cap E$ is, since we have $U_k = q(q^{-1}(U_k) \cap E)$. Assume now that $U_k$ is symmetric. Then so is $q^{-1}(U_k)$, and hence so is the intersection $q^{-1}(U_k) \cap E$.

(2) : For each integer $k \ge 0$, $q^{-1}(V_k)$ is a Borel subset of $G$. In light of (A.5.2.6), the condition in (A.5.2.2) holds for $\{U_k,V_k\}_{k \ge 0}$ if and only if it holds for $\{q^{-1}(U_k) \cap E, q^{-1}(V_k) \cap E\}_{k \ge 0}$.

Assume $V_k V_k^{-1} \subset U_k$. Then $q^{-1}(V_k V_k^{-1}) \subset q^{-1}(U_k)$. We have $q^{-1}(V_k) \cdot q^{-1}(V_k)^{-1} = q^{-1}(V_k V_k^{-1})$, and hence $q^{-1}(V_k) \cdot q^{-1}(V_k)^{-1} \cap E \subset q^{-1}(V_k V_k^{-1}) \cap E$. It follows that we have $q^{-1}(V_k) \cdot q^{-1}(V_k)^{-1} \cap E \subset q^{-1}(U_k) \cap E$.

## PDF page 574

**574** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

Since we have $(q^{-1}(V_k) \cap E) \cdot (q^{-1}(V_k) \cap E)^{-1} \subset (q^{-1}(V_k) \cdot q^{-1}(V_k)^{-1}) \cap E$ (here we use that $E$ is symmetric), we deduce that $(q^{-1}(V_k) \cap E) \cdot (q^{-1}(V_k) \cap E)^{-1} \subset q^{-1}(U_k) \cap E$ too.

Conversely, if $(q^{-1}(V_k) \cap E) \cdot (q^{-1}(V_k) \cap E)^{-1} \subset q^{-1}(U_k) \cap E$ holds, then so does $q(q^{-1}(V_k) \cap E) \cdot q((q^{-1}(V_k) \cap E)^{-1}) \subset q(q^{-1}(U_k) \cap E)$. Since $q(q^{-1}(V_k) \cap E) = V_k$, $q((q^{-1}(V_k) \cap E)^{-1}) = V_k^{-1}$, for the settled case of $D$-sequences and $D'$-sequences, and $q(q^{-1}(U_k) \cap E) = U_k$, we deduce that we have $V_k V_k^{-1} \subset U_k$.

It follows that $\{U_k,V_k\}_{k \ge 0}$ is a $D''$-sequence for $G/H$ if and only if $\{q^{-1}(U_k) \cap E, q^{-1}(V_k) \cap E\}_{k \ge 0}$ is a $D''$-sequence for $G$. $\square$

REMARK A.5.2.11. We highlight that in [Klee, (2.4), p. 487] the terminology "countable complete system of neighborhoods" of a point $x \in X$ of a topological space $X$ (which is a topological group in loc.cit.) means a "countable neighborhood base" at $x$.

A.5.2.2. *The case of $S$-local and global groups of ideles and idele classes.* We now return to the Hausdorff locally compact abelian groups of interest to this work. Let $F$ be a number field, and let $\tau : \mathbf{R}_{>0} \to \mathrm{GL}_1(\mathbf{A}_F)$ be a choice of continuous section to the idelic norm.

We recall from (A.2.3.14) that we have $E^\mathrm{1}_F \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ a relatively compact subset with non-empty interior, which is a fundamental domain for the continuous left-translation action of the discrete subgroup $F^\times \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ on $\mathrm{GL}_1(\mathbf{A}_F)^1$.

The construction of $E^\mathrm{1}_F$ is, recall, as follows: for a fixed choice of Archimedean place $v_0$, and denoting by $\iota_{v_0}$ an isomorphism of topological fields from $F_{v_0}$ to either $\mathbf{R}$ (if $v_0$ is real) or $\mathbf{C}$ (if $v_0$ is complex):

$$
E_0 := \{g \in \mathscr{L}^{-1}(P) : \arg(\iota_{v_0}(g_{v_0})) \in [0,2\pi/w_F)\} \subset \mathscr{L}^{-1}(P) \tag{A.5.2.7}
$$

where $w_F$ is the number of roots of unity contained in $F$ (note that if $F$ has a real place, then $w_F = 2$), and $P$ is the following relatively compact subset of the Lie group $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1$ with non-empty interior:

$$
P_0 := \left\{ \sum_{i=1}^{r_1+r_2-1} x_i \mathscr{L}(\varepsilon_i) : (x_i) \in Q_0 \right\} \tag{A.5.2.8}
$$

from (A.2.3.9), for $\{\varepsilon_1,\dots,\varepsilon_{r_1+r_2-1}\}$ a $\mathbf{Z}$-linear basis for the maximal torsion-free quotient of the unit group $\mathcal{O}_F^\times$,

$$
Q_0 := \{(x_i) \in \mathbf{R}^{r_1+r_2-1} : 0 \le x_i < 1\} \subset \mathbf{R}^{r_1+r_2-1}, \tag{A.5.2.9}
$$

and $\mathscr{L}$ is the logarithm homomorphism $\mathscr{L}((u_v)_{v \in S_\infty}) = (\log|u_v|_v)_{v \in S_\infty}$.

We then define:

$$
E^\mathrm{1}_F := \bigcup_{i=1}^{h_F} g_i(E_0 \times \widehat{\mathcal{O}}^\times_F) \subset \mathrm{GL}_1(\mathbf{A}_F)^1 \subset \mathrm{GL}_1(\mathbf{A}_F) \tag{A.5.2.10}
$$

where $h_F$ is the class number of $F$ and $\{g_i\}_{1 \le i \le h_F}$ is a set of representatives in $\mathrm{GL}_1(\mathbf{A}_F)^1$ for the ideal classes in $\mathrm{Pic}(\mathcal{O}_F)$, with $g_1 = 1$; see (A.2.3.14).

We now adjust the construction of $E^\mathrm{1}_F$, to obtain another fundamental domain, enjoying additional symmetries. We define:

$$
P_1 := \left\{ \sum_{i=1}^{r_1+r_2-1} x_i \mathscr{L}(\varepsilon_i) : (x_i) \in Q_1 \right\} \tag{A.5.2.11}
$$

with

$$
Q_1 := \{(x_i) \in \mathbf{R}^{r_1+r_2-1} : -1/2 \le x_i < 1/2\} \subset \mathbf{R}^{r_1+r_2-1} \tag{A.5.2.12}
$$

## PDF page 575

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **575**

and

$$
B^1_F := E_1 \times \widehat{\mathcal{O}}^\times_F \tag{A.5.2.13}
$$

with

$$
E_1 := \{g \in \mathscr{L}^{-1}(P_1) : \arg(\iota_{v_0}(g_{v_0})) \in [0,\pi/w_F) \cup [2\pi-\pi/w_F,2\pi)\} \subset \mathscr{L}^{-1}(P_1) \tag{A.5.2.14}
$$

endowed with the subspace topology.

In a similar manner and following Definition A.2.4.3, for $S$ a finite set of places of $F$ containing all the Archimedean places, and upon writing $S_f$ for $S \cap \Sigma_{F,f}$, the finite set of those finite places of $F$ contained in $F$, we define, upon choosing an Archimedean place $v_0$ of $F$:

$$
B^1_{F,S} := \{g \in \mathscr{L}_S^{-1}(P_S) : \arg(\iota_{v_0}(g_{v_0})) \in [0,\pi/w_F) \cup [2\pi-\pi/w_F,2\pi)\} \subset \mathscr{L}_S^{-1}(P_S) \tag{A.5.2.15}
$$

for

$$
\mathscr{L}_S : \mathrm{GL}_1(\mathbf{A}_{F,S}) \to \mathbf{R}^S \tag{A.5.2.16}
$$

defined as

$$
\mathscr{L}_S(g) := (\log|g_v|_v)_{v \in S} \tag{A.5.2.17}
$$

and, upon choosing an integral basis $\{\varepsilon_1,\dots,\varepsilon_{|S|-1}\}$ for $\mathcal{O}^\times_{F,S}$, $P_S$ is the parallelotope in the hyperplane $H_S := \{x \in \mathbf{R}^S : \sum_{v \in S} x_v = 0\}$ of $\mathbf{R}^S$ defined as

$$
P_S := \sum_{1 \le i \le |S|-1} [-1/2,1/2) \mathscr{L}_S(\varepsilon_i) \subset H_S. \tag{A.5.2.18}
$$

We endow $B^1_{F,S}$ with the subspace topology.

LEMMA A.5.2.12. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

(1) *For $g_1 := 1$ and $\{g_i\}_{1 \le i \le h_F} \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ a choice of representatives for the $h_F$ ideal classes in $\mathrm{Pic}(\mathcal{O}_F)$, $\bigcup_{1 \le i \le h_F} g_i B^1_F$ is a fundamental domain for the continuous left-translation action of $F^\times$ on $\mathrm{GL}_1(\mathbf{A}_F)^1$.*

(2) *$B^1_{F,S}$ is a fundamental domain for the continuous left-translation action of $\mathcal{O}^\times_{F,S}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.*

(3) *For $g_1 := 1$ and $\{g_i\}_{1 \le i \le h_{F,S}} \subset \mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,S})^1$ a choice of representatives for the $h_{F,S}$ ideal classes in $\mathrm{Pic}(\mathcal{O}_{F,S})$, $\bigcup_{1 \le i \le h_{F,S}} g_i B^1_{F,S}$ is a fundamental domain for the continuous left-translation action of $\mathcal{O}^\times_{F,S}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1$.*

PROOF. (1) : We will be showing that $B^1_F$ is a fundamental domain within $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty} \times \widehat{\mathcal{O}}_F)^1$ for the continuous left-translation action of the global unit group $\mathcal{O}^\times_F$. To this end, we proceed as follows. The kernel of $\mathscr{L}_F := \mathscr{L} \times (\log|\cdot|_v)_{v \in \Sigma_{F,f}} : \mathrm{GL}_1(\mathbf{A}_{F,S_\infty} \times \widehat{\mathcal{O}}_F)^1 \to \mathbf{R}^{S_\infty}$ is the finite group of roots of unity $\mu_F \subset \mathcal{O}^\times_F$, while the image of $\mathscr{L}_F$ is the finite-dimensional Euclidean space $H = \{\sum_{v \mid \infty} x_v = 0\} \subset \mathbf{R}^{S_\infty}$. We know $\mathscr{L}_F(\mathcal{O}^\times_F/\mu_F)$ is a lattice in $H$, and $Q_1 \times \{0\} \simeq Q_1$ is a fundamental domain for the additive translation action of $\mathscr{L}_F(\mathcal{O}^\times_F/\mu_F) \simeq \mathscr{L}(\mathcal{O}^\times_F/\mu_F)$ on $H$.

In order to prove that $B^1_F$ is a fundamental domain for the continuous left-translation action of $\mathcal{O}^\times_F$ on $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty} \times \widehat{\mathcal{O}}_F)^1$, it remains to note that $e^{i[0,\pi/w_F) \cup i[2\pi-\pi/w_F,2\pi)}$ is a fundamental domain within $\mathrm{U}(1)$ of the action of the finite cyclic group $\mu_F = e^{\frac{2\pi i\mathbf{Z}}{w_F}}$.

We now let $\{g_1,\dots,g_{h_F}\}$ be representatives in $\mathrm{GL}_1(\mathbf{A}_F)^1$ for the $h_F$ ideal classes in $\mathrm{Pic}(\mathcal{O}_F)$, with $g_1 = 1$. By (A.2.3.24), the disjoint union $\bigcup_{1 \le i \le h_F} g_i B^1_F$ is a fundamental domain for the continuous left-translation action of $F^\times$ on $\mathrm{GL}_1(\mathbf{A}_F)^1$.

(2) : The same argument provided for (1) shows that (2) holds upon replacing the containment $\mathbf{R}^{S_\infty} \supset H$ with $\mathbf{R}^S \supset H_S$ and noting that $\ker(\mathscr{L}_S) \cap \mathcal{O}^\times_{F,S} = \mu_F$.

## PDF page 576

**576** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

(3) : By choosing the $g_i$'s to be representatives of $h_{F,S}$ ideal classes in $\mathrm{Pic}(\mathcal{O}_{F,S})$ in $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1$, the subset $\bigcup_{1 \le i \le h_{F,S}} g_i B^1_{F,S}$ is a fundamental domain for the continuous left-translation action of $\mathcal{O}^\times_{F,S}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1$, in light of (2) by adapting the method of proof of (1). $\square$

LEMMA A.5.2.13. Let $F$ be a number field.

(1) *The interior $\mathrm{Int}(E_1)$ of $E_1$ from (A.5.2.14) is a symmetric unit-neighborhood in $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1$.*

(2) The following sequence of subsets:

$$
U_{S_\infty,k} := \mathscr{L}^{-1}(P_k) \tag{A.5.2.19}
$$

with

$$
P_k = \{\sum_{i=1}^{r_1+r_2-1} x_i \mathscr{L}(\varepsilon_i) : -1/(k+1) < x_i < 1/(k+1) \text{ for all } 1 \le i \le r_1+r_2-1\} \tag{A.5.2.20}
$$

*is a symmetric $D'$-sequence for $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1$, and $\{U_{S_\infty,k},U_{S_\infty,2k}\}_{k \ge 0}$ is a $D''$-sequence for $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1$.*

PROOF. (1) : Since $\mathrm{Int}(Q_1)$ from (A.5.2.12) is a symmetric unit-neighborhood in $\mathbf{R}^{r_1+r_2-1}$, then, for $\mathrm{Int}(E_1)$ to be a symmetric unit-neighborhood in $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1$, it is enough for the subset$^{10}$

$$
U := \{z \in \mathbf{C}^\times : |z| \in e^{(-1/4,1/4)}, \arg(z) \in (0,\pi/t) \cup (2\pi-\pi/t,2\pi)\}
$$

to be a symmetric unit-neighborhood$^{11}$ of $1 \in \mathbf{C}^\times$ for $t \ge 2$.

Indeed, if $z \in U$, then $|z^{-1}| \in e^{(-1/4,1/4)}$ also holds. Since $\arg(z^{-1}) = -\arg(z) \bmod 2\pi$, and for any $\delta \in [0,2\pi)$ we have that $\delta \in (0,\pi/t) \bmod 2\pi$ if and only if $-\delta \in (2\pi-\pi/t,2\pi) \bmod 2\pi$, then $U$ is a symmetric unit-neighborhood of $1$ in $\mathbf{C}^\times$.

(2) : The logarithm homomorphism $\mathscr{L}$ is injective on each $P_k$, and $\mathscr{L}(P_k) \subset \mathscr{L}(P_1)$. It is therefore enough to show that$^{12}$ $\{Q_k\}_{k \ge 0}$ is a symmetric $D'$-sequence for $\mathbf{R}^{r_1+r_2-1}$, and $\{Q_k,Q_{2k}\}_{k \ge 0}$ is a $D''$-sequence for $\mathbf{R}^{r_1+r_2-1}$, which is indeed the case since $Q_k$ is an open cube in $\mathbf{R}^{r_1+r_2-1}$ whose baricenter is the origin, and every Haar measure on $\mathbf{R}^{r_1+r_2-1}$ is a positive multiple of the Lebesgue measure. $\square$

LEMMA A.5.2.14. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

(1) *Let $\{B_k\}_{k \ge 0}$ be a sequence of compact open subgroups in $\widehat{\mathcal{O}}^\times_{F,S}$ such that $B_{k+1} \subset B_k$ for every integer $k \ge 0$, and $\{B_k\}_{k \ge 0}$ is a unit-neighborhood base in $\widehat{\mathcal{O}}^\times_{F,S}$. Then the sequence $\{U_{S,k}\}_{k \ge 0}$ of subsets in $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$:*

$$
U_{S,k} := U_{S_\infty,k} \times B_k \tag{A.5.2.21}
$$

is a symmetric $D'$-sequence for $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

(2) *For each integer $k \ge 0$ and for $\overline{U}_{S,k}$ the image in $J^1_{F,S}$ of $U_{S,k}$ under the continuous quotient homomorphism $\mathrm{GL}_1(\mathbf{A}_{F,S})^1 \to J^1_{F,S}$, the sequence $\{\overline{U}_{S,k}\}_{k \ge 0}$ is a symmetric $D'$-sequence for $J^1_{F,S}$.*

PROOF. (1) holds by Lemma A.5.2.3(2), combined with Lemma A.5.2.3(1) and Lemma A.5.2.5.

(2) : Since $B^1_{F,S}$ is a fundamental domain for the continuous left-translation action of $\mathcal{O}^\times_{F,S}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, and for every integer $k \ge 0$ we have $U_{S,k} \subset B^1_{F,S}$, then (2) holds by Proposition A.5.2.6. $\square$

LEMMA A.5.2.15. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We let $\{B_k\}_{k \ge 0}$ be a choice of a sequence of compact open subgroups of $\widehat{\mathcal{O}}^\times_{F,S}$ such that $B_{k+1} \subset B_k$ for*

---
$^{10}$Why use $e^{(-1/4,1/4)}$ below rather than $(1/c,c)$ for general $c > 1$?

$^{11}$This misses $1$ (which has argument $0$)!

$^{12}$Need to define $Q_k$ somehow akin to $P_k$'s

## PDF page 577

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **577**

*every integer $k \ge 0$ such that $\{B_k\}_{k \ge 0}$ is a unit-neighborhood base in $\widehat{\mathcal{O}}^\times_{F,S}$, we let $\{U_{S,k}\}_{k \ge 0}$ be the sequence of open subsets of $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1 \times \widehat{\mathcal{O}}^\times_F$ defined in (A.5.2.21).*

*We let $\tau_S : \mathbf{R}_{>0} \to \mathrm{GL}_1(\mathbf{A}_{F,S})$ be a choice of continuous homomorphic section to the $S$-idelic norm.*

The sequence:

$$
\{U_k := \tau_S((1-1/k,1+1/k)) \cdot U_{S,k}\}_{k \ge 0} \tag{A.5.2.22}
$$

*is a symmetric open $D'$-sequence for $\mathrm{GL}_1(\mathbf{A}_{F,S})$. For $\overline{U}_k$ the image of $U_k$ in $J_{F,S}$ for each integer $k \ge 0$, $\{\overline{U}_k\}_{k \ge 0}$ is a symmetric open $D'$-sequence for $J_{F,S}$.*

PROOF. The Lemma follows upon combining Lemma A.5.2.5 with Lemma A.5.2.14. The assertions on $\{\overline{U}_k\}_{k \ge 0}$ follow from Lemma A.5.2.12(2) and Proposition A.5.2.6. $\square$

LEMMA A.5.2.16. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

(1) *Let $\{B_k\}_{k \ge 0}$ be a sequence of compact open subgroups in $\widehat{\mathcal{O}}^\times_F$ such that $B_{k+1} \subset B_k$ for every integer $k \ge 0$, and $\{B_k\}_{k \ge 0}$ is a unit-neighborhood base in $\widehat{\mathcal{O}}^\times_F$. Then the sequence $\{U_{F,k}\}_{k \ge 0}$ of subsets in $\mathrm{GL}_1(\mathbf{A}_F)^1$:*

$$
U_{F,k} := U_{S_\infty,k} \times B_k \tag{A.5.2.23}
$$

*is a symmetric $D'$-sequence for $\mathrm{GL}_1(\mathbf{A}_F)^1$ and for $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1$.*

(2) *For each integer $k \ge 0$ and for $\overline{U}_{F,k}$ the image in $C^1_F$ of $U_{F,k}$ under the continuous quotient homomorphism $\mathrm{GL}_1(\mathbf{A}_F)^1 \to C^1_F$, the sequence $\{\overline{U}_{F,k}\}_{k \ge 0}$ is a symmetric $D'$-sequence for $C^1_F$.*

(3) *For each integer $k \ge 0$ and for $\overline{U}_{F,S,k}$ the image in $C^1_{F,S}$ of $U_{F,k}$ under the continuous quotient homomorphism $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1 \to C^1_{F,S}$, the sequence $\{\overline{U}_{F,S,k}\}_{k \ge 0}$ is a symmetric $D'$-sequence for $C^1_{F,S}$.*

PROOF. (1) holds by Lemma A.5.2.3(2), combined with Lemma A.5.2.3(1) and Lemma A.5.2.5.

(2) and (3) : Since, by Lemma A.5.2.12(3), $\bigcup_{1 \le i \le h_{F,S}} g_i B^1_{F,S}$, for $\{g_1 = 1,\dots,g_{h_{F,S}}\}$ a choice of representatives in $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \prod_{v \notin S} \mathcal{O}_{F_v})^1$ of the $h_{F,S}$ ideal classes in $\mathrm{Pic}(\mathcal{O}_{F,S})$, is a fundamental domain for the continuous left-translation action of $\mathcal{O}^\times_{F,S}$ on $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \prod_{v \notin S} \mathcal{O}_{F_v})^1$, and for every integer $k \ge 0$ we have that $U_{F,k}$ is contained in it, then (2) and (3) both hold by (1) and Proposition A.5.2.6. $\square$

We conclude with the following:

LEMMA A.5.2.17. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We let $\{B_k\}_{k \ge 0}$ be a choice of a sequence of compact open subgroups of $\widehat{\mathcal{O}}^\times_F$ such that $B_{k+1} \subset B_k$ for every integer $k \ge 0$ such that $\{B_k\}_{k \ge 0}$ is a unit-neighborhood base in $\widehat{\mathcal{O}}^\times_F$, we let $\{U_{F,k}\}_{k \ge 0}$ be the sequence of open subsets of $\mathrm{GL}_1(\mathbf{A}_{F,S_\infty})^1 \times \widehat{\mathcal{O}}^\times_F$ defined in (A.5.2.23).*

*We let $\tau : \mathbf{R}_{>0} \to \mathrm{GL}_1(\mathbf{A}_F)$ be a choice of continuous homomorphic section to the idelic norm.*

(1) The sequence:

$$
\{U_k := \tau((1-1/k,1+1/k)) \cdot U_{F,k}\}_{k \ge 0} \tag{A.5.2.24}
$$

*is a symmetric open $D'$-sequence for $\mathrm{GL}_1(\mathbf{A}_F)$. For $\overline{U}_k$ the image of $U_k$ in $C_F$ for each integer $k \ge 0$, $\{\overline{U}_k\}_{k \ge 0}$ is a symmetric open $D'$-sequence for $C_F$.*

(2) *If $\tau$ factors through $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S}) \subset \mathrm{GL}_1(\mathbf{A}_F)$, then the sequence $\{U_k\}_{k \ge 0}$ is a symmetric open $D'$-sequence for $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})$. For $\overline{U}_k$ the image of $U_k$ in $C_{F,S}$ for each integer $k \ge 0$, $\{\overline{U}_k\}_{k \ge 0}$ is a symmetric open $D'$-sequence for $C_{F,S}$.*

PROOF. (1) : By Lemma A.5.2.5, the sequence in (A.5.2.24) is a symmetric $D'$-sequence for $\mathrm{GL}_1(\mathbf{A}_F) \simeq \mathbf{R}_{>0} \times \mathrm{GL}_1(\mathbf{A}_F)^1$, the isomorphism of Hausdorff locally compact abelian groups being induced by the choice

## PDF page 578

**578** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

of $\tau$, and since $\{(1-1/k,1+1/k)\}_{k \ge 0}$ and $U_{F,k}$ each satisfy all the assertions as sequences within $\mathbf{R}_{>0}$, respectively $\mathrm{GL}_1(\mathbf{A}_F)^1$, the latter by Lemma A.5.2.16(1).

The assertions on $\{\overline{U}_k\}_{k \ge 0}$ and $\{\overline{U}_k,\overline{U}_{2k}\}_{k \ge 0}$ then follow from Proposition A.5.2.6, since $\bigcup_{1 \le i \le h_F} g_i B^1_F$ is, by Lemma A.5.2.12(1), for $\{g_1 = 1,\dots,g_{h_F}\}_{1 \le i \le h_F} \subset \mathrm{GL}_1(\mathbf{A}_F)^1$ a choice of representatives for the $h_F$ ideal classes in $\mathrm{Pic}(\mathcal{O}_F)$ a fundamental domain for the continuous left-translation action of $F^\times$ on $\mathrm{GL}_1(\mathbf{A}_F)^1$. $\square$

We introduce the following terminology, for later use:

DEFINITION A.5.2.18. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

We refer to the open symmetric $D'$-sequences:

(1) $\{U_k\}_{k \ge 0}$ from (A.5.2.24) for $\mathrm{GL}_1(\mathbf{A}_F)$, respectively $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})$.

(2) $\{\overline{U}_k\}_{k \ge 0}$ from Lemma A.5.2.17, respectively Lemma A.5.2.15, for $C_F$, respectively $C_{F,S}$.

(3) $\{U_{F,k}\}_{k \ge 0}$ from (A.5.2.23) for $\mathrm{GL}_1(\mathbf{A}_F)^1$, respectively $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1$.

(4) $\{\overline{U}_{F,k}\}_{k \ge 0}$ from Lemma A.5.2.16(2), for $C^1_F$, $\{\overline{U}_{F,S,k}\}_{k \ge 0}$ from Lemma A.5.2.16(3), for $C^1_{F,S}$.

(5) $\{U_k\}_{k \ge 0}$ from (A.5.2.22) for $\mathrm{GL}_1(\mathbf{A}_{F,S})$.

(6) $\{\overline{U}_k\}_{k \ge 0}$ from Lemma A.5.2.15, for $J_{F,S}$.

(7) $\{U_{S,k}\}_{k \ge 0}$ from (A.5.2.21), for $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

(8) $\{\overline{U}_{S,k}\}_{k \ge 0}$ from Lemma A.5.2.14(2), for $J^1_{F,S}$.

as the standard $D'$-sequence for $G = \mathrm{GL}_1(\mathbf{A}_F),\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S}), C_F, C_{F,S}, \mathrm{GL}_1(\mathbf{A}_F)^1, \mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1, C^1_F, C^1_{F,S}, \mathrm{GL}_1(\mathbf{A}_{F,S}), J_{F,S}, \mathrm{GL}_1(\mathbf{A}_{F,S})^1, J^1_{F,S}$, respectively.

We will be using the notation $\{U_k\}_{k \ge 0}$ to denote the standard symmetric $D'$-sequence for $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})$, $\mathrm{GL}_1(\mathbf{A}_F)^1$, $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$, and $\{\overline{U}_k\}_{k \ge 0}$ to denote the standard symmetric $D'$-sequence for their respective class groups.

REMARK A.5.2.19. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

We observe that for the standard $D'$-sequences for $\mathrm{GL}_1(\mathbf{A}_F)^1$, $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})^1$, $C^1_F$, $C^1_{F,S}$, the structural constant $C$ from (A.5.2.1) can be chosen$^{13}$ to be $A^{r_1+r_2-1}$ for any real number $A > 2$.

For $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$ and $J^1_{F,S}$, it can be chosen to be $A^{|S|-1}$ for any real number $A > 2$.

For $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and their class groups, it is enough to multiply the above constants by $A$.

A.5.3. Hardy-Littlewood Maximal Theorem on Hausdorff locally compact abelian groups. We now know that the Hausdorff locally compact abelian groups $\mathrm{GL}_1(\mathbf{A}_F)$, $\mathrm{GL}_1(\mathbf{A}_{F,S} \times \widehat{\mathcal{O}}_{F,\Sigma_F-S})$, $\mathrm{GL}_1(\mathbf{A}_{F,S})$, their closed subgroups of norm-$1$ elements, their class groups $C_F$, $C_{F,S}$, $J_{F,S}$, and their subgroups of norm-$1$ elements, admit symmetric open $D'$-sequences.

We will now show how to construct an analog, for Hausdorff locally compact abelian groups that admit Borel $D$-sequences, and, at times, $D'$-sequences as the need arises, of the Hardy-Littlewood maximal function, and we will be discussing analogs of the Hardy-Littlewood Maximal Theorem and Lebesgue's Differentiation Theorem.

We begin with the following result from [HR-2, Ch. XI, §44]:

THEOREM A.5.3.1. *Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a Haar measure on $G$. Let $\{U_k\}_{k \ge 0}$ be a $D$-sequence for $G$. We let $\mathcal{F} \subset \mathcal{P}(G)$ be the collection of all subsets of $G$ of the form $xU_k$, for $x \in G$ and $k \ge 0$ an integer. Let $\mathcal{F}' \subset \mathcal{F}$ be a subset.*

*Let $B \subset G$ be a $\mu_G$-measurable subset such that:*

---
$^{13}$Should briefly explain calculation to get these sufficient constants.

## PDF page 579

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **579**

(1) $\mu_G(B \cdot U_0)$ is finite.$^{14}$

(2) *For each $x \in B$, there exists an integer $k \ge 0$ such that $xU_k \in \mathcal{F}'$.*

*Then there exists a finite subset $\{x_i U_{k_i}\}_{1 \le i \le N} \subset \mathcal{F}'$ such that $x_i \in B$ for all $1 \le i \le N$, the subsets $x_i U_{k_i}$ are pairwise disjoint, and:*

$$
\sum_{1 \le i \le N} \mu_G(U_{k_i}) > \frac{\mu_G(B)}{C} \tag{A.5.3.1}
$$

*where $C > 0$ is the structural constant from (A.5.2.1) associated to the $D$-sequence $\{U_k\}_{k \ge 0}$.*

REMARK A.5.3.2. The Theorem is [HR-2, Ch. XI, Thm. 44.11, p. 638], and it is a generalization of the Vitali Covering Lemma (see [StSha-III, Ch. 3, §1, Lemma.1.2, p. 102]).

We note that in [HR-2, Ch. XI, Thm.44.11, p. 638], the subset $B \subset G$, denoted by $E$, is not assumed to be measurable. The notation $\lambda(E)$ and $\lambda(E \cdot U_1)$ is to mean $\lambda^*(E)$, $\lambda^*(E \cdot U_1)$, in the sense of [Bou-I, Ch. IV, §1, No. 4, Def. 4, INT IV.10].

We will now discuss some aspects of the proofs of the main results from [HR-2, Ch. XI, §44.50], resting on [HR-2, Ch. XI, Thm. 44.13].

We will be assuming the Hausdorff locally compact abelian group $G$ under consideration is second countable, which, in light of the following Lemma, leads to promoting identities and properties valid locally almost everywhere (i.e almost everywhere within every compact subset), into assertions valid almost everywhere.

We recall that, for a Hausdorff locally compact$^{15}$ topological space $X$, and a measure $\mu$ on $X$, a subset $A \subset X$ is locally $\mu$-negligible if and only if for every $x \in X$ there exists a neighborhood $U$ of $x$ such that $A \cap U$ is $\mu$-negligible (see [Bou-I, Ch. IV, §5, No. 2, Def. 4, INT IV.61]).

LEMMA A.5.3.3. *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is second countable. Let $\mu_G$ be a choice of Haar measure on $G$.*

*Let $A \subset G$ be a subset. If $A$ is locally $\mu_G$-negligible, then $A$ is $\mu_G$ measurable and $\mu_G$-negligible.*

PROOF. Let $\{K_m\}_{m \ge 0}$ be a countable exhaustion of $G$ by compact subsets. Then $A \cap K_m$ is $\mu_G$-negligible and $A = \bigcup_{m \ge 0} (A \cap K_m)$, which gives $\mu_G(A) = 0$. In particular, $A$ is $\mu_G$-measurable. $\square$

A.5.3.1. *Hardy-Littlewood Maximal Theorems on Hausdorff locally compact abelian groups.* The following is a special case of [HR-2, Ch.XI,§44,Thm.44.13,p.640]:

THEOREM A.5.3.4 (Measure-theoretic Maximal Theorem - I). *Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a choice of Haar measure on $G$. Assume $G$ is second countable.*

*Let $\{U_k\}_{k \ge 0}$ be a Borel $D$-sequence in $G$. Let $\nu$ be a positive Radon measure on $G$. We define, for each $x \in G$:$^{16}$*

$$
(M\nu)(x) := \limsup_{k \ge 0} \frac{\nu(xU_k)}{\mu_G(U_k)}. \tag{A.5.3.2}
$$

*Let $B$ be a $\mu_G$-measurable subset of $G$ such that $\mu_G(B \cdot U_0)$ is finite.*

(1) *For any real number $\alpha > 0$, we have:*

$$
\mu_G(B \cap \{x \in G : (M\nu)(x) > \alpha\}) \le \frac{C}{\alpha} \nu((B \cap \{x \in G : (M\nu)(x) > \alpha\}) \cdot U_0) \tag{A.5.3.3}
$$

*and equality holds if and only if $B \cap \{x \in G : (M\nu)(x) > \alpha\} = \varnothing$.*

---
$^{14}$Should address why $B \cdot U_0$ is automatically measurable; maybe for this we need sufficiently small or somehow nice $U_0$?

$^{15}$no second-countable hypothesis?

$^{16}$Must address $M\nu$ being measurable. warn reader that $\nu(xU_k)$ may be infinite.

## PDF page 580

**580** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

(2) *If $\overline{U}_0$ is compact, then $M\nu$ is finite $\mu_G$-almost everywhere.*

PROOF. (1) : As in the proof of [HR-2, Ch.XI,§44,Thm.44.13,p.640], we first assume $B \cap \{x \in G : (M\nu)(x) > \alpha\}$, and the Theorem is obtained by defining $\mathcal{F}$ to be the collection of the subsets of $G$ of the form $xU_k$ for $x \in G$ and each integer $k \ge 0$, and $\mathcal{F}' \subset \mathcal{F}$ the sub-collection of those subsets $xU_k$ with $x \in B \cap \{y \in G : (M\nu)(y) > \alpha\}$ satisfying $\nu(xU_k) > \alpha \mu_G(U_k)$. Indeed, then applying Theorem A.5.3.1 to the choice $\{U_k\}_{k \ge 0}$ of $D$-sequence for $G$, and to the above choices of $\mathcal{F}$ and $\mathcal{F}'$ gives (1).

The strict inequality in (A.5.3.1) from Theorem A.5.3.1 ensures$^{17}$ that if $B \cap \{x \in G : (M\nu)(x) > \alpha\}$ is non-empty then the inequality in (A.5.3.3) holds and is strict. Equality holds if $B \cap \{x \in G : (M\nu)(x) > \alpha\}$ is empty.

(2) : We define $B_\infty \subset G$ to be the subset $\{x \in G : (M\nu)(x) = \infty\}$. By Lemma A.5.3.3 it is enough to show that for every compact subset $K \subset G$, we have $\mu_G(B_\infty \cap K) = 0$.

By assumption, $\overline{U}_0$ is compact, and hence so is $K \cdot \overline{U}_0$. Since both $\mu_G$ and $\nu$ are Radon measures, both $\mu_G(K \cdot \overline{U}_0)$ and $\nu(K \cdot \overline{U}_0)$ are finite.

For every positive real number $\alpha > 0$ we have

$$
\mu_G(K \cap B_\infty) \le \mu_G(K \cap \{x \in G : (M\nu)(x) > \alpha\}) \le \frac{C}{\alpha} \nu((K \cap \{x \in G : (M\nu)(x) > \alpha\}) \cdot U_0) \le \frac{C}{\alpha} \nu(K \cdot \overline{U}_0) \tag{A.5.3.4}
$$

(middle inequality via (1) applied to $B = K$) and since $\alpha > 0$ is arbitrary, we may let $\alpha$ tend to $+\infty$ in (A.5.3.4) and deduce $\mu_G(K \cap B_\infty) = 0$. $\square$

In the presence of a $D'$-sequence in $G$, a more precise result is available. The following is a special case of [HR-2, Ch. XI, Thm.44.14, p. 641]:

THEOREM A.5.3.5 (Measure-theoretic Maximal Theorem - II). *Let $G$ be a Hausdorff locally compact abelian group, $\mu_G$ a choice of Haar measure on $G$. Assume $G$ is second countable.*

*Let $\{U_k\}_{k \ge 0}$ be a $D'$-sequence in $G$. Let $\nu$ be a positive Radon measure on $G$. We define, for each $x \in G$:$^{18}$*

$$
(\overline{M}\nu)(x) := \limsup_{k \ge 0} \frac{\nu(xU_k)}{\mu_G(U_k)}. \tag{A.5.3.5}
$$

*Let $K \subset G$ be a compact subset. For any real number $\alpha > 0$, we have:*

$$
\mu_G(K \cap \{x \in G : (\overline{M}\nu)(x) > \alpha\}) \le \frac{C}{\alpha} \nu(K). \tag{A.5.3.6}
$$

PROOF. Let $N \ge 0$ be a nonnegative integer, and consider, as in the proof of [HR-2, Ch. XI, Thm.44.14, p. 641], the $D$-sequence in $G$ defined by $\{U_k\}_{k \ge N}$. Since $\{U_k\}_{k \ge 0}$ is a $D'$-sequence, for any compact unit-neighborhood $V$ there exists a large enough integer $k_0 \ge 0$ such that $U_{k_0}$, and hence $U_k$ for all $k \ge k_0$, is contained in $V$. This implies that the closure of each $U_k$ for every $k \ge k_0$ is compact.

We fix $N \ge k_0$. Let $K \subset G$ be a compact subset. Then $K \cdot \overline{U}_k$ is compact for every $k \ge N$, and hence $\mu_G(K \cdot U_N)$ is finite. By Theorem A.5.3.4, we have, for every real number $\alpha > 0$:

$$
\mu_G(K \cap \{x \in G : (\overline{M}\nu)(x) > \alpha\}) \le \frac{C}{\alpha} \nu(K \cdot U_N). \tag{A.5.3.7}
$$

For any open subset $V$ containing $K$, there exists a unit-neighborhood $U$ in $G$ such that $K \cdot U \subset V$. Since $\{U_k\}_{k \ge 0}$ is a $D'$-sequence, there exists a large enough integer $k_1 \ge k_0$ such that $U_{k_1} \subset U$, and hence $K \cdot U_{k_1} \subset V$.

---
$^{17}$Why? Must say more.

$^{18}$This seems the same as $(M\nu)(x)$ above, so why now denoted differently?

## PDF page 581

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **581**

Since $\nu$ is regular by [Fol, Thm. 7.8], (in fact, [Fol, Prop. 7.5] suffices), and hence

$$
\nu(K)\le \liminf_{N\to+\infty}\nu(K\cdot U_N)\le \inf\{\nu(V):K\subset V, V\text{ open}\}=\nu(K),
$$

this gives $\lim_{N\to+\infty}\nu(K\cdot U_N)=\nu(K)$. $\square$

We are ready to state and prove the following version of the Hardy-Littlewood Maximal Theorem:

THEOREM A.5.3.6 (Hardy-Littlewood Local Maximal Theorem). *Let $G$ be a Hausdorff locally compact abelian group, and $\mu_G$ a choice of Haar measure. Assume $G$ is second countable.*

*Let $\{U_k\}_{k\ge 0}$ be a $D$-sequence such that $\overline{U}_0$ is compact. Let $f\in L^1_{\mathrm{loc}}(G,\mu_G)$, and define, for every $x\in G$:*

$$
(Mf)(x):=\limsup_{k\ge 0}\left\{\frac{1}{\mu_G(U_k)}\int_{xU_k}\lvert f(y)\rvert\,\mathrm{d}\mu_G(y)\right\}. \tag{A.5.3.8}
$$

*Then $Mf$ is $\mu_G$-measurable, and if $f\log^+\lvert f\rvert\in L^1_{\mathrm{loc}}(G,\mu_G)$ then $Mf\in L^1_{\mathrm{loc}}(G,\mu_G)$, so $Mf$ is finite $\mu_G$-almost everywhere.*

*If $\{U_k\}_{k\ge 0}$ is a $D'$-sequence then*

*(1) for every $\mu_G$-measurable subset $B\subset G$ such that $B\cdot U_0$ is $\mu_G$-measurable$^{19}$ with finite $\mu_G$-measure, any real number $\alpha>0$, and any real number $\delta\in(0,1)$, we have*

$$
\mu_G(B\cap\{x\in G:(Mf)(x)>\alpha\})\le \frac{C}{(1-\delta)\alpha}\int_{(B\cdot U_0)\cap\{x\in G:(Mf)(x)>\delta\alpha\}}\lvert f(x)\rvert\,\mathrm{d}\mu_G(x). \tag{A.5.3.9}
$$

*(2) For every real number $p>1$, we have:*

$$
\int_B\lvert (Mf)(x)\rvert^p\,\mathrm{d}\mu_G(x)\le \frac{Cp^{p+1}}{(p-1)^p}\int_{B\cdot U_0}\lvert f(x)\rvert^p\,\mathrm{d}\mu_G(x). \tag{A.5.3.10}
$$

PROOF. The proof is analogous to the proof of Theorem A.5.1.1. We will be following the proof of [HR-2, Ch. XI, Thm.44.50, p. 669].

We note that both $Mf$ and, if $\{U_k\}_{k\ge 0}$ is a $D'$-sequence,$^{20}$ $\overline{M}f$, are $\mu_G$-measurable by [Ru-2, Ch. 1, Thm. 1.14, p. 14].

We note that by [Ru-2, Ch. 1, Corollaries,(b), p. 15], for $f\in L^1_{\mathrm{loc}}(G,\mu_G)$, then $\log^+\lvert f\rvert$ and hence $f\log^+\lvert f\rvert$ is $\mu_G$-measurable.

We now prove that $Mf$ is finite $\mu_G$-almost everywhere.

If $f\log^+\lvert f\rvert\in L^1_{\mathrm{loc}}(G,\mu_G)$ then for any compact subset $K\subset G$ we have, by [HR-2, Ch. XI, Thm.44.50, p. 669] (a consequence of Fubini's Theorem and [Fol, Thm.7.27]):

$$
\int_K\lvert (Mf)(x)\rvert\,\mathrm{d}\mu_G(x)\le \frac{1}{2}\mu_G(K)+\frac{C}{2}\int_{K\cdot U_0}\lvert f(x)\rvert\log^+\lvert f\rvert\,\mathrm{d}\mu_G(x) \tag{A.5.3.11}
$$

which proves that for every compact subset $K\subset G$, $(Mf)\cdot\mathrm{1}_K$ is absolutely $\mu_G$-integrable. Since $G$ is second countable, this implies that $Mf\in L^1_{\mathrm{loc}}(G,\mu_G)$ holds. In particular, $Mf$ is finite locally $\mu_G$-almost everywhere, and hence (by Lemma A.5.3.3) $\mu_G$-almost everywhere.

(1) : We fix $\alpha>0$, and $\delta\in(0,1)$. Let $F_\delta:=\lvert f\rvert\cdot\mathrm{1}_{A_{f,\delta,\alpha}}$ where $\mathrm{1}_{A_{f,\delta,\alpha}}$ is the indicator function of the set:

$$
A_{f,\delta,\alpha}:=\{x\in G:\lvert f(x)\rvert>\delta\alpha\}. \tag{A.5.3.12}
$$

Since $f\in L^1_{\mathrm{loc}}(G,\mu_G)$, the set $A_{f,\delta,\alpha}$ is $\mu_G$-measurable. The function $F_\delta$ is locally $\mu_G$-integrable, and it satisfies:

$$
Mf\le MF_\delta+\delta\alpha \tag{A.5.3.13}
$$

---
$^{19}$Is this measurability not automatically satisfied?

$^{20}$We really sequence $D'$-sequence property to ensure such measurability? Why?

## PDF page 582

**582** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

and hence:

$$
\{x\in G:(Mf)(x)>\alpha\}\subset\{x\in G:(MF_\delta)(x)>(1-\delta)\alpha\}. \tag{A.5.3.14}
$$

We define $\nu:=F_\delta\,\mu_G$. Since $F_\delta$ is locally $\mu_G$-integrable, $\nu$ is a positive Radon measure on $G$.

We first apply Theorem A.5.3.4. We obtain, from (A.5.3.14) and (A.5.3.3):

$$
\mu_G(B\cap\{x\in G:(Mf)(x)>\alpha\})\le \mu_G(B\cap\{x\in G:(MF_\delta)(x)>(1-\delta)\alpha\}) \tag{A.5.3.15}
$$

$$
\le \frac{C}{(1-\delta)\alpha}\int_{(B\cap\{x\in G:(MF_\delta)(x)>(1-\delta)\alpha\})\cdot U_0}F_\delta(x)\,\mathrm{d}\mu_G(x)
$$

$$
\le \frac{C}{(1-\delta)\alpha}\int_{B\cdot U_0}F_\delta(x)\,\mathrm{d}\mu_G(x).
$$

This proves (A.5.3.9). (2) : To prove that (A.5.3.10) holds, the argument is identical to that provided in the liminf analogue [HR-2, Ch. XI, Thm. 44.50(iii), p. 670], an application of Fubini's Theorem and [Fol, Thm. 7.27] by choosing $\delta=1-1/p$. $\square$

The following consequence of Theorem A.5.3.6 is a global version:

THEOREM A.5.3.7 (Hardy-Littlewood Global Maximal Theorem). *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is second countable.*

*Let $\{U_k\}_{k\ge 0}$ be a $D'$-sequence such that $\overline{U}_0$ is compact. Let $f\in L^1_{\mathrm{loc}}(G,\mu_G)$, and define for every $x\in G$:*

$$
(Mf)(x):=\limsup_{k\ge 0}\left\{\frac{1}{\mu_G(U_k)}\int_{xU_k}\lvert f(y)\rvert\,\mathrm{d}\mu_G(y)\right\}. \tag{A.5.3.16}
$$

*Then:*

*(1) Assume $f\in L^1(G,\mu_G)$. For every real number $\alpha>0$ we have:*

$$
\mu_G(\{x\in G:(Mf)(x)>\alpha\})\le \frac{2C}{\alpha}\lVert f\rVert_{L^1(G,\mu_G)}. \tag{A.5.3.17}
$$

*(2) For every real number $p>1$, if $f\in L^p(G,\mu_G)$ then $Mf\in L^p(G,\mu_G)$ also holds and we have:*

$$
\int_G\lvert (Mf)(x)\rvert^p\,\mathrm{d}\mu_G(x)\le \frac{Cp^{p+1}}{(p-1)^p}\lVert f\rVert^p_{L^p(G,\mu_G)}. \tag{A.5.3.18}
$$

PROOF. By Theorem A.5.3.6 with $\delta=1/2$, (1) and (2) both follow from the Theorem and an application of Dominated Convergence, noting that we may choose $B$ to range over an exhaustion of $G$ by a sequence of compact subsets. $\square$

**A.5.4. Lebesgue Differentiation on Hausdorff locally compact abelian groups.** In this subsection, we establish an analog of Lebesgue's Differentiation Theorem:

THEOREM A.5.4.1 (Lebesgue's Differentiation Theorem - Hausdorff Locally Compact Abelian Groups). *Let $G$ be a Hausdorff locally compact abelian group. Let $\mu_G$ be a Haar measure on $G$. Assume $G$ is second countable. Let $\{U_k\}_{k\ge 0}$ be a $D'$-sequence for $G$. Let $f\in L^1_{\mathrm{loc}}(G,\mu_G)$. Then:*

*(1) For each integer $k\ge 0$, the integral*

$$
A_{U_k}(f)(x):=\frac{1}{\mu_G(U_k)}\int_{xU_k}f(y)\,\mathrm{d}\mu_G(y) \tag{A.5.4.1}
$$

*is a uniformly continuous function of $x\in G$.*

*(2) The sequence $\{A_{U_k}(f)(x)\}_{k\ge 0}$ converges for $\mu_G$-almost all $x\in G$.*

*(3) Let $\mathrm{Reg}_{\{U_k\}_{k\ge 0},f}\subset G$ be the subset of those points $x\in G$ at which $\{A_{U_k}(f)(x)\}_{k\ge 0}$ converges.*

## PDF page 583

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **583**

*Then the complement of $\mathrm{Reg}_{\{U_k\}_{k\ge 0},f}$ is $\mu_G$-negligible, and the identity*

$$
f(x)=\lim_{k\to+\infty}\frac{1}{\mu_G(U_k)}\int_{xU_k}f(y)\,\mathrm{d}\mu_G(y) \tag{A.5.4.2}
$$

*holds at $\mu_G$-almost every $x\in\mathrm{Reg}_{\{U_k\}_{k\ge 0},f}$ and, in particular, $\mu_G$-almost everywhere.*

TERMINOLOGY A.5.4.1 (Smoothening). We will be referring to the function defined as the limit of the sequence in (A.5.4.1), where the defining limit exists pointwise $\mu_G$-almost everywhere by Theorem A.5.4.1(2), as the *smoothening* of $f$.

REMARK A.5.4.2. The set $\mathcal{L}_f(\{U_k\}_{k\ge 0}):=\mathrm{Reg}_{\{U_k\}_{k\ge 0},f}\cap D_f$, abbreviated $\mathcal{L}_f$, is a generalization of the Lebesgue set of a locally integrable complex-valued function on a finite-dimensional real Euclidean space. Each of the sets $\mathrm{Reg}_{\{U_k\}_{k\ge 0},f}$ and $D_f$ is allowed to be strictly larger.$^{21}$

PROOF. (1) : Let $\varepsilon>0$ be an arbitrary real number.

We analyze the following condition on $x,y\in G$:

$$
\left\lvert\int_{x_1U_k}f(y)\,\mathrm{d}\mu_G(y)-\int_{x_2U_k}f(y)\,\mathrm{d}\mu_G(y)\right\rvert<\varepsilon. \tag{A.5.4.3}
$$

We have, by invariance of the Haar measure $\mu_G$:

$$
\int_{x_iU_k}f(y)\,\mathrm{d}\mu_G(y)=\int_{U_k}f(x_iy)\,\mathrm{d}\mu_G(y) \tag{A.5.4.4}
$$

for $i=1,2$.

Since $\mu_G$ is a Radon measure on $G$, the functional $\mu_G:L^1_{\mathrm{loc}}(G,\mu_G)\to\mathbf{C}$ is continuous with respect to the Hausdorff locally convex topology on $L^1_{\mathrm{loc}}(G,\mu_G)$ defined by the countable family of seminorms $\{\lVert\cdot\rVert_{L^1(K_m,\mu_G)}\}$ for $\{K_m\}_{m\ge 0}$ an exhaustion by compact subsets of $G$ (with each $K_m$ having non-empty interior).

To see this, it is enough to show that the functional $\mu_G:L^1(K_m,\mu_G)\to\mathbf{C}$ defined by $\mu_G(\phi):=\int_{K_m}\phi(x)\,\mathrm{d}\mu_G(x)$ is norm-continuous, which is indeed the case since we have:

$$
\lvert\mu_G(\phi_1-\phi_2)\rvert\le\lVert\phi_1-\phi_2\rVert_{L^1(K_m,\mu_G)}. \tag{A.5.4.5}
$$

We note that $C_c(G)\subset L^1_{\mathrm{loc}}(G,\mu_G)$ is dense with respect to the resulting Hausdorff locally convex topology, since the image into each $L^1(K_m,\mu_G)$ is norm-dense and the topology on $L^1_{\mathrm{loc}}(G,\mu_G)$ is metrizable.

We now define $\rho_G:G\times L^1_{\mathrm{loc}}(G,\mu_G)\to L^1_{\mathrm{loc}}(G,\mu_G)$ the map $\rho_G(g,\phi)(x):=\phi(g^{-1}x)$ for $\mu_G$-almost all $x\in G$. Equivalently, we may define $\rho_G$ on $C_c(G)$ as the left-translation action by $G$ on compactly supported continuous complex-valued functions on $G$, and extend the left-translation action by continuity to $L^1_{\mathrm{loc}}(G,\mu_G)$. Such action is indeed continuous, since, for each $g\in G$, we have:

$$
\lVert\rho_G(g,\cdot)\rVert_{L^1(K_m,\mu_G)}\le\lVert\cdot\rVert_{L^1(K_0,\mu_G)}+\dots+\lVert\cdot\rVert_{L^1(K_{m_N},\mu_G)} \tag{A.5.4.6}
$$

for finitely many integers $0,\dots,m_N$ determined by $K_{m_N}$ enclosing $g'K_m$ in its interior for all $g'$ near $g$.

It follows that $\rho_G$ is uniformly continuous (see [Bou-GT, Ch. II, §2, No. 1, Def. 1, p. 174]). The adjoint action $\rho'_G$ on the strong dual $L^1_{\mathrm{loc}}(G,\mu_G)'_\beta$ is therefore also uniformly continuous, in light of (A.5.4.5).

(2) : We will be following the proof of Theorem A.5.1.3. It is enough to treat the case when $f$ is real-valued.

Let $V\subset G$ be an arbitrary open neighborhood of $x\in G$ with compact closure. Since $G$ is Hausdorff, locally compact and second-countable, by [Fol, Prop. 7.5] (a regularity property of $\mu$ in the $\sigma$-finite case, which applies since $\overline{V}$ is compact), a compact subset $K\subset V$ containing $x$ and such that $\mu_G(V-K)$ is as small as we please.

Clearly there exists an open unit-neighborhood $U\subset G$ such that $U\cdot K\subset V$, and since $\{U_k\}_{k\ge 0}$ is a $D'$-sequence, there exists a large enough integer $k_0\ge 0$ such that $U_k\subset U$ for every integer $k\ge k_0$ and each

---
$^{21}$Should make clearer to the reader why this Remark is being recorded here.

## PDF page 584

**584** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

$U_k$ has compact closure. It follows that we have:

$$
A_{U_k}(f)(x)=A_{U_k}(f\cdot\mathrm{1}_V)(x) \tag{A.5.4.7}
$$

for every $k\ge k_0$.

We define the "local oscillation" of $f$ at $x$:

$$
\omega_f(x):=\omega_{\{U_k\}_{k\ge 0},f}(x):=\left\lvert\limsup_{k\to+\infty}A_{U_k}(f)(x)-\liminf_{k\to+\infty}A_{U_k}(f)(x)\right\rvert. \tag{A.5.4.8}
$$

We note that we are assuming $f$ is real-valued, and hence the right side in (A.5.4.8) makes sense. In light of (A.5.4.7), we have:

$$
\omega_f(x)=\omega_{f\cdot\mathrm{1}_V}(x). \tag{A.5.4.9}
$$

Since $f\cdot\mathrm{1}_V\in L^1(G,\mu_G)$, all $\mu_G(E_j)$ are finite and for any $\varepsilon>0$ there exists $\varphi=\sum_{1\le j\le N}c_j\mathrm{1}_{E_j}$ for $\mu_G$-measurable subsets $E_j$ and $c_j\in\mathbf{R}$ such that $\lVert f\cdot\mathrm{1}_V-\varphi\rVert_{L^1(G,\mu_G)}<\varepsilon$. We define $F:=f\cdot\mathrm{1}_V-\varphi$, and note that we have$^{22}$

$$
\omega_{f\cdot\mathrm{1}_V}(x)\le\omega_F(x) \tag{A.5.4.10}
$$

for almost all $x$ so long as we show that we have $\omega_\varphi(x)=0$ for almost all $x\in G$. We will be granting this for the moment.

We have:

$$
\omega_{f\cdot\mathrm{1}_V}(x)\le 2(MF)(x). \tag{A.5.4.11}
$$

Now observe that by Theorem A.5.3.7(1) we have

$$
\mu_G(\{y\in G:(MF)(y)>\alpha\})\le\frac{2C}{\alpha}\lVert F\rVert_{L^1(G,\mu_G)}<\frac{2C\varepsilon}{\alpha} \tag{A.5.4.12}
$$

and from (A.5.4.11) we deduce that we have:

$$
\mu_G(\{x\in G:\omega_{f\cdot\mathrm{1}_V}(x)>\alpha\})\le\frac{4C}{\alpha}\lVert F\rVert_{L^1(G,\mu_G)}<\frac{4C\varepsilon}{\alpha} \tag{A.5.4.13}
$$

which implies (since $\varepsilon>0$ is arbitrary) that $\mu_G(\{x\in G:\omega_{f\cdot\mathrm{1}_V}(x)>\alpha\})=0$. Since this holds for every $\alpha>0$, we deduce that $\omega_{f\cdot\mathrm{1}_V}(x)=0$ for $\mu_G$-almost every $x\in G$.

This implies that the sequence $A_{U_k}(f)(x)$ converges, for $\mu_G$-almost every $x\in V$, for $V$ any open subset in $G$ with $\overline{V}$ compact, and hence locally $\mu_G$-almost everywhere. Thus, it converges $\mu_G$-almost everywhere.

We may therefore assume $f=\varphi$; i.e., $f$ is an integrable simple function whose coefficients are real. We want to show $\omega_f(x)=0$ for all $x$. By subadditivity and the identity $\omega_{cf}=\lvert c\rvert\omega_f$, it is enough to treat the case $f=\mathrm{1}_E$ for $E\subset G$ a $\mu_G$-measurable subset of finite $\mu_G$-measure. This amounts to showing that the sequence of nonnegative real numbers:

$$
\frac{\mu_G(xU_k\cap E)}{\mu_G(U_k)}
$$

converges for all $x\in G$.

By outer regularity of the Radon measure $\mu_G$ (see [Fol, Prop. 7.5]), we may replace$^{23}$ $E$ by an open subset $U\subset G$ with finite $\mu_G$-measure.

Assume $x\in U$. There exists an open unit-neighborhood $V\subset G$ such that $xV\subset U$, and since $\{U_k\}_{k\ge 0}$ is a $D'$-sequence there exists a enough integer $k_0\ge 0$ such that $U_k\subset V$ for all $k\ge k_0$ and $U_k$ has compact closure. It follows that for all integers $k\ge k_0$, we have $xU_k\subset U$, and hence $A_{U_k}(f)(x)=1$ for all $k\ge k_0$.

---
$^{22}$Be more careful: *first* should choose $V$, then $x\in V$, then $K\subset V$ containing $x$, etc.

$^{23}$Should say a bit more, not hard by comparing limsup and liminf

## PDF page 585

**A.5. IDELIC HARDY-LITTLEWOOD MAXIMAL THEOREM AND LEBESGUE DIFFERENTIATION** · **585**

Assume now $x\notin\overline{U}$. Then there exists an open neighborhood $U'$ of $x$ in $G$ entirely contained in the open complement $G-\overline{U}$, and upon repeating the above argument we deduce that there exists a large enough integer $k_0\ge 0$ such that for all integers $k\ge k_0$, we have $xU_k\subset U'$, and $xU_k$ has compact closure. It follows that we have $A_{U_k}(f)(x)=0$ for all $k\ge k_0$.

We now assume $x$ is in the boundary of $U$ in $G$. By outer regularity of $\mu_G$ (since $\mu(U)<\infty$), there exists an open subset $U'\subset G$ containing $U$ such that $\mu_G(U'-U)$ is as small as we please, which shows that we have $\mu_G(\partial U)=0$. It follows that indeed the convergence assertion holds for $\mu_G$-almost all $x$ for such $f$.

(3) : To prove that (A.5.4.2) holds for $\mu_G$-almost all $x\in G$, it is enough to assume$^{24}$ that $f$ is compactly supported, hence in $L^p(G,\mu_G)$ for every $p\ge 1$. We write:

$$
\frac{1}{\mu_G(U_k)}\int_{xU_k}f(y)\,\mathrm{d}\mu_G(y)=\frac{1}{\mu_G(U_k)}\int_G f(y)\mathrm{1}_{U_k}(yx^{-1})\,\mathrm{d}\mu_G(y)
$$

and upon defining $u_k(y):=\frac{1}{\mu_G(U_k)}\mathrm{1}_{U_k}(y^{-1})$, we have $A_{U_k}(f)=f\ast u_k$, for each integer $k\ge 0$.

For any real number $q>1$, $\lVert u_k\rVert_{L^q(G,\mu_G)}=1$. By [Fol, Thm. 2.26] there exists a sequence $\{\varphi_m\}_{m\ge 0}$ of simple functions with complex coefficients such that $\lVert f-\varphi_m\rVert_{L^p(G,\mu_G)}\to 0$ as $m\to+\infty$. We have, for $\mu_G$-almost all $x\in G$ and for $p>1$ with $1/p+1/q=1$,$^{25}$ by [HR-1, Ch.V,§20,Thm.20.16,p.295] and Hölder's Inequality:

$$
\lvert (f\ast u_k)(x)-f(x)-(\varphi_m\ast u_k)(x)+\varphi_m(x)\rvert\le\lVert f-\varphi_m\rVert_{L^p(G,\mu_G)}\lVert u_k\rVert_{L^q(G,\mu_G)}+\lvert\varphi_m(x)-f(x)\rvert
$$

and since $\varphi_m\to f$ in $L^p(G,\mu_G)$, there exists a subsequence converging $\mu_G$-almost everywhere. Thus, the result for each $\varphi_m$ yields the same for $f$.

We may therefore assume $f$ is a simple function with complex coefficients, and by linearity reduce to the case $f=\mathrm{1}_E$, which was checked throughout the proof of (2). $\square$

We discuss the following consequence of Theorem A.5.4.1:

COROLLARY A.5.4.3. *Let $G$ be a Hausdorff locally compact abelian group. Let $\mu_G$ be a choice of Haar measure on $G$. Assume $G$ is second countable. Let $\{U_k\}_{k\ge 0}$ be a $D'$-sequence for $G$. Let $f\in L^1_{\mathrm{loc}}(G,\mu_G)$. Let $\varphi\in C_c(G)$. Then the limit of the sequence:*

$$
A_{U_k}(\varphi\cdot f)(x):=\frac{1}{\mu_G(U_k)}\int_{xU_k}(\varphi\cdot f)(y)\,\mathrm{d}\mu_G(y) \tag{A.5.4.14}
$$

*exists at all the points $x\in G$ at which the limit of the sequence $\{A_{U_k}(f)(x)\}_{k\ge 0}$ exists. Its value is*

$$
\lim_{k\to+\infty}A_{U_k}(\varphi\cdot f)(x)=\varphi(x)\cdot\lim_{k\to+\infty}A_{U_k}(f)(x). \tag{A.5.4.15}
$$

PROOF. Since $\{U_k\}_{k\ge 0}$ is a $D'$-sequence, there exists an integer $k_0\ge 0$, such that for every integer $k\ge k_0$, $U_k$ has compact closure.

We consider the sequence:

$$
\lvert A_{U_k}(\varphi\cdot f)(x)-\varphi(x)\cdot A_{U_k}(f)(x)\rvert\le\frac{1}{\mu_G(U_k)}\int_{xU_k}\lvert(\varphi(y)-\varphi(x))f(y)\rvert\,\mathrm{d}\mu_G(y)\le\sup_{y\in xU_k}\lvert\varphi(y)-\varphi(x)\rvert\cdot\lVert f\rVert_{L^1(xU_k,\mu_G)} \tag{A.5.4.16}
$$

for all $k\ge k_0$.

Since $xU_k\subset xU_{k_0}$ for every integer $k\ge k_0$, we deduce the inequality:

$$
\lvert A_{U_k}(\varphi\cdot f)(x)-\varphi(x)\cdot A_{U_k}(f)(x)\rvert\le\sup_{y\in xU_k}\lvert\varphi(y)-\varphi(x)\rvert\cdot\lVert f\rVert_{L^1(xU_{k_0},\mu_G)} \tag{A.5.4.17}
$$

for all $k\ge k_0$.

---
$^{24}$Should briefly explain, using $\mu_G(\partial U)$ for open $U$ with $\overline{U}$ compact

$^{25}$Why not just use $p=q=2$?

## PDF page 586

**586** · **CHAPTER A. PREPARATIONS FROM ALGEBRAIC NUMBER THEORY**

Since $\varphi$ is continuous, for every real number $\varepsilon>0$ there exists an open neighborhood $V$ of $x\in G$ such that $\lvert\varphi(y)-\varphi(x)\rvert<\varepsilon$ for all $y\in V$. There exists an open unit-neighborhood $V'\subset G$ such that $xV'\subset V$, and there exists an integer $k_1\ge k_0$ such that $U_k\subset V'$ for all integers $k\ge k_1$.

In particular, $\sup_{y\in xU_k}\lvert\varphi(y)-\varphi(x)\rvert<\varepsilon$ for all $k\ge k_1$. In light of (A.5.4.17), the sequence

$$
\{A_{U_k}(\varphi\cdot f)(x)\}_{k\ge 0}
$$

converges if and only if $\{A_{U_k}(f)(x)\}_{k\ge 0}$ does. Its limit at such $x$ is therefore $\varphi(x)\cdot\lim_{k\to+\infty}A_{U_k}(f)(x)$, by letting $k$ tend to $+\infty$ within the left side of (A.5.4.17). $\square$
