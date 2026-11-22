## PDF page 655

APPENDIX C

**Preparations on locally convex topological vector spaces**

C.1. Locally convex topological vector spaces 657

C.1.1. References on basic concepts 657

C.1.1.1. Basic constructions 658

C.1.2. On the topology of locally convex topological vector spaces 658

C.1.2.1. Local convexity and fundamental families of continuous seminorms 658

C.1.3. Convergence and completeness 658

C.1.4. Boundedness and quasi-completeness 660

C.1.5. Inductive limits and detection of limit subspaces 663

C.1.5.1. Acyclicity and limit subspaces of LF-spaces 666

C.1.6. Duality and inductive limits 669

C.2. Complements on mapping spaces, topological tensor products, and nuclearity 670

C.2.1. Mapping spaces 670

C.2.2. Topologies of a duality and the equicontinuous compactology 673

C.2.2.1. Generation of polar topologies: bornologies and topologies of a duality 673

C.2.2.2. Consistent topologies 674

C.2.2.3. Uniform convergence on the weakly closed convex and circled equicontinuous subsets of $E'$ 675

C.2.3. Topological tensor products 675

C.2.3.1. Injective tensor products by bi-equicontinuous convergence 676

C.2.3.2. Projective tensor products 679

C.2.3.3. Metrizability, and separately continuous and continuous bi-linear forms 681

C.2.3.4. Inductive tensor products 682

C.2.3.5. Linear topological embeddings and injective tensor products in the presence of nuclearity 683

C.2.4. Nuclear spaces 685

C.2.4.1. Characterizations of nuclearity 685

C.2.4.2. Continuous dual of $E \otimes_{\varepsilon} F$ 686

C.2.4.3. Integral mappings and characterizations of nuclearity 688

C.2.4.4. Permanence properties 689

C.2.4.5. Approximation Property 689

C.2.4.6. Kernel Theorems 690

C.2.5. Complements on the finest locally convex topology 691

C.3. Nuclear operators 693

C.3.1. Preparations 693

C.3.2. Nuclear operators picking up their nuclear trace from a subspace 694

C.3.3. Topologies on the endomorphism algebra of a Hilbert space 696

C.3.4. Trace-class operators on Hilbert spaces 697

C.3.4.1. Trace-class operators: definitions and basic properties 697

C.3.5. Convergence properties of nuclear operators on Hilbert spaces 699

655

## PDF page 656

**656** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

C.3.5.1. Lemmas on singular values 699

C.3.6. Schatten-von Neumann classes of index $p = 1, 2$ 703

C.3.6.1. Nuclear, Hilbert-Schmidt and compact operators as topological tensor products 705

C.3.6.2. Closure properties of Schatten-von Neumann classes 705

C.3.7. Integral kernels 707

C.4. Integration in the sense of Pettis 708

C.4.1. Weak completion 709

C.4.2. Vector-valued measurable and integrable functions 710

C.4.3. Integrability criteria and permanence properties 711

C.4.3.1. Vector-valued Mean Value Theorems 711

C.4.3.2. Stability properties of vector-valued integrals and integrability criteria 713

C.4.3.3. Continuity criterion 716

C.4.4. Fubini's Theorem and Weil's Integral Formula 717

C.5. Meromorphic functions valued in a quasi-complete locally convex tvs 719

C.5.1. Vector-valued continuous and differentiable functions 720

C.5.1.1. Properties of the spaces of continuous compactly supported $E$-valued functions 721

C.5.1.2. Vector-valued differentiability 723

C.5.1.3. Permanence properties of vector-valued differentiation. 726

C.5.1.4. Vector-valued differentiability criterion. 731

C.5.1.5. Spaces of smooth vector-valued functions. 735

C.5.2. Holomorphic vector-valued functions 737

C.5.2.1. Grothendieck's criterion for holomorphy 737

C.5.3. Meromorphic vector-valued functions 739

C.5.3.1. Vector-valued residues 740

C.5.4. Vector-valued Residue Theorem 740

C.5.4.1. Vector-valued Identity Theorem 741

## PDF page 657

**C.1. LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES** · **657**

**C.1. Locally convex topological vector spaces**

Throughout this first section we provide initial guidance through the vast literature on locally convex topological vector spaces, highlighting the concepts and results that will be used throughout this work, indicating where to find them, and introducing the conventions that will be regularly in force. Later sections give an overview of more advanced notions, such as topologies on duals and tensor products, nuclearity (of spaces and of linear maps), integration valued in locally convex spaces satisfying a completeness condition (this goes far beyond the more familiar Banach case, and is a generality we require crucially), and holomorphicity/meromorphicity for functions valued in suitable locally convex spaces.

Fourier theory for tempered distributions on Hausdorff locally compact abelian groups $G$, and topological properties of the Schwartz-Bruhat space $\mathcal{S}(G)$ as a locally convex topological vector space, will be a primary focus (with a view towards the intended applications) in Appendix D building upon the present Appendix.

**C.1.1. References on basic concepts.** A vector space $E$ is a *topological vector space* if and only if it is a topological space over a topological field, and the operations defining the linear structure are continuous. The notation *tvs* is an abbreviation for *topological vector space*. The class of topological vector spaces we will be working with is that of *locally convex* topological vector spaces over $\mathbf{C}$.

We recall the basic terminology below, in the form of a roadmap to the literature, to facilitate the reader's access to it. The references [Bou-TVS, Ch. I], [Scha, Ch. I], [Jar, Ch. 2], [Kothe-I, Ch. 3, §15], and [NB, Ch. 4] provide basic general background on topological vector spaces over $\mathbf{C}$. Similar and simpler concepts for topological $\mathbf{R}$-vector spaces can be found in [Bou-TVS, Ch. II], and indication of how to adapt the results there to the case of $\mathbf{C}$-vector spaces is given in [Bou-TVS, Ch. II, §8].

Here are some basic concepts to keep in mind for a tvs $E$ over $\mathbf{C}$ and a subset $C \subset E$:

(1) We say $C$ is *convex* if for all $x, y \in C$, the line segment $\{tx + (1 - t)y : t \in [0, 1]\}$ joining $x$ and $y$ is contained in $C$. See [Scha, Ch. II, §1] for basic stability properties of convex subsets.

The intersection of all convex subsets of $E$ containing a subset $A \subset E$ is called the *convex hull* of $A$. We will denote it $\mathrm{Ch}(A)$. A direct description of $\mathrm{Ch}(A)$ is as the set of all *finite* $\mathbf{R}$-linear combinations $\sum_{k \ge 1} \lambda_k x_k$ of elements $x_k$ of $A$, subject to the constraint that $\lambda_k \ge 0$ for every $k$ and $\sum_{k \ge 1} \lambda_k = 1$.

(2) We say $C$ is *circled* if $\lambda C \subset C$ for all $\lambda$ in the closed unit disc $D \subset \mathbf{C}$. The smallest circled subset of $E$ containing a subset $A \subset E$ is called the *circled hull* of $A$, denoted $\mathrm{ch}(A)$.

(3) We say $C$ is *absolutely convex* if it is both convex and circled. This is a way to define the concept of a "disc" (or "ball") in a $\mathbf{C}$-vector space without having a normed structure: the absolutely convex subsets are regarded as the "discs" in $E$.

The *absolutely convex hull*, also called the *convex circled hull*, of a subset $A \subset E$ is the convex hull of the circled hull; it is denoted $\mathrm{cch}(A)$ (in [Scha, p. 39] and [Kothe-I, p. 173] it is denoted $\Gamma(A)$). We use the terminology "convex circled" rather than "absolutely convex".

We refer the reader to [NB, Def. 4.2.7, Thm. 4.2.8] for a simple criterion for $C$ to be its own convex circled hull in $E$; see also [Jar, §6.1, Prop. 1] (for $r = 1$) and [NB, Thm. 4.2.11].

(4) We say $C$ is *absorbing* if for every $x \in E$ there exists $\varepsilon > 0$ such that for all $\lambda \in \mathbf{C}$ with $|\lambda| \le \varepsilon$, $\lambda x \in C$. In other words, each point of $E$ is carried into $C$ ("absorbed" by $C$) by *all* sufficiently small scaling factors. Absorbing subsets are also called *radial* (see [Scha, p. 11] and [NB, Def. 4.1.2(b)]).

Remark C.1.1.1. In some references the concept of circled subset is referred to as "balanced" (e.g., see [Tre, Def. 3.2] and [NB, Def. 4.1.2(a)]), and the term "circled" is sometimes reserved for those subsets $C$ of a topological $\mathbf{C}$-vector space $E$ such that $\lambda C \subset C$ for $\lambda \in \mathbf{C}$ with $|\lambda| = 1$ (i.e., $C$ is preserved under "rotations"). We will avoid this latter concept altogether; "circled" and "balanced" are synonymous for us.

A topological vector space $E$ is called *locally convex* if it has a neighborhood base at $0$ consisting of convex subsets. Due to the linear structure being continuous in a topological vector space, every point $x$ of $E$ then

## PDF page 658

**658** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

has a neighborhood base given by $x$-translates of convex circled subsets. We further refer the reader to [Scha, Ch. I, §1 §6; Ch. II, §1, §4] for the basic generalities on the construction of linear topologies and locally convex topologies.

C.1.1.1. *Basic constructions.* For a subset $A \subset E$ of a topological vector space, we can form closures of the hulls discussed in the foregoing. These are:

(1) the closure $\overline{\mathrm{Ch}}(A)$ of the convex hull of $A$, called the *closed convex hull*;

(2) the closure $\overline{\mathrm{ch}}(A)$ of the circled hull of $A$, called the *closed circled hull*;

(3) the closure $\overline{\mathrm{cch}}(A)$ of the convex circled hull of $A$, called the *closed convex circled hull*.

Remark C.1.1.2. The closure of a circled hull and the circled hull of a closure are not interchangeable. An example over $\mathbf{R}$ is the hyperbola $A = \{xy = 1\} \subset \mathbf{R}^2$ as noted just after the proof of [Jar, §2.2, Prop. 1] (the circled hull $\mathrm{ch}(A) = \mathrm{ch}(\overline{A})$ is the region $\{0 < xy \le 1\} \cup \{(0, 0)\}$, and its closure is $\{0 \le xy \le 1\}$).

**C.1.2. On the topology of locally convex topological vector spaces.** We recall some basic facts about the topology of a topological $\mathbf{C}$-vector space, then specializing to the locally convex case. Every topological vector space $E$ has a neighborhood base at $0$ consisting of closed circled subsets, as well as open circled subsets (since $\mathrm{int}(A)$ is circled when $A$ is). Via convex hull, these can be taken to be convex too when $E$ is locally convex [Scha, Ch. I, Cor. to 1.3]. The *convexity* assumption on the members of a neighborhood base of $0$ is what distinguishes locally convex topological vector spaces from arbitrary topological vector spaces.

Remark C.1.2.1. A useful structure with which any tvs is endowed (but we won't need) is that of a *canonical uniformity*. We refer to [Bou-GT, Ch. II, §1.1, Def. 1] for the definition of uniform structure and the topology associated to such a structure, and [Scha, Ch. I, 1.4] for relating the topology on a topological vector space to a unique translation-invariant uniform structure. We further refer the reader to [Kothe-I, Ch. 1, §5], [Bou-TVS, Ch. I, §1.4] for more on uniform structures and the canonical uniformity of a topological vector space. For our purposes, the concept of uniformity can be avoided since (as we shall discuss) *completion* for Hausdorff topological vector spaces can be made using Cauchy nets rather than going through the theory of completion for uniform spaces.

C.1.2.1. *Local convexity and fundamental families of continuous seminorms.* An equivalent way to describe the topology on locally convex topological vector spaces is through continuous seminorms (as developed in [Scha, Ch. II, §1, §4], [Bou-TVS, Ch. II, §1, §4], [NB, Ch. 5]).

The linear span of every absorbing convex circled subset $A \subset E$ is equipped with a real-valued function

(C.1.2.1)
$$
p_A(x) := \inf_{x \in \lambda A, \lambda \in \mathbf{R}_{> 0}} \lambda
$$

called its *Minkowski functional* (or gauge functional). Under the above assumptions on $A$, $p_A$ is a seminorm [Scha, Ch. II, 1.4]. The Minkowski functional can be used to translate the datum of a neighborhood base at $0$ of open, or closed, circled convex subsets into a family of seminorms, and conversely [Scha, Ch. II, 1.5-1.6, §4]. For instance, continuity of a seminorm $p$ is equivalent to $\{p < 1\}$ being a neighborhood of $0$.

Given a collection of seminorms $\{p_i\}$ on $E$, if we define

$$
U_i := \{x \in E : p_i(x) \le 1\}
$$

then the collection of subsets $\{n^{-1}U\}$ as $n$ varies over all the positive integers and $U$ varies over all finite intersections $U_{i_1} \cap \cdots \cap U_{i_m}$ is a neighborhood base at $0$ for a unique locally convex topology, and every locally convex topology on $E$ arises in this way. The topology is Hausdorff exactly when the only $x \in E$ such that $p_i(x) = 0$ for all $i \in I$ is $x = 0$; we then say $\{p_i\}_{i \in I}$ is *separating*.

**C.1.3. Convergence and completeness.** A Hausdorff topological vector space $E$ is metrizable if and only if it has a countable base of $0$-neighborhoods, in which case there is a translation-invariant metric [Scha,

## PDF page 659

**C.1. LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES** · **659**

Ch. I, 6.1] (this provides a pseudo-norm $|\cdot| : E \to \mathbf{R}_{\ge 0}$ such that the metric $d(x, y) = |x - y|$ induces the topology). However, examples of much importance in number theory and in this work are non-metrizable, such as Schwartz spaces of non-archimedean local fields and Schwartz spaces of adele rings and of idele class groups of number fields. Nonetheless, even in the absence of a metric, there are good notions of completion and completeness as we shall now discuss.

In [Bou-GT, Ch. II, §3.3, Def. 3], the notion of completeness (for uniform spaces) is defined through the convergence of Cauchy filters. For the concept of filter and its use to define convergence in topological spaces, we refer to [Bou-GT, Ch. I, 6, 7]. We will use *nets* instead of filters (to be discussed below). For the correspondence between nets and filters (and their equivalent encoding of convergence) we refer the interested reader to [Sm] and to [Cl, §6] (where the results of [Sm], building on work of Bartle in [Ba], are further spelled out and the two convergence concepts are related in [Cl, §6. Thm. 6.4]), and to [NB, Ch. 1, §1.1.2], with emphasis on [NB, Thms. 1.1.8, 1.1.9].

Definition C.1.3.1. Let $E$ be a topological vector space.

(1) A *net* in $E$ is a map $f : J \to E$ from a directed set $J$ (also denoted $\{f_j\}_{j \in J}$).

(2) A net $f : J \to E$ *converges* in $E$ if there exists $x \in E$ such that for every $0$-neighborhood $U \subset E$ there exists $j_0$ so that $x - f_j \in U$ for all $j \ge j_0$ (this $x$ is unique when $E$ is Hausdorff).

(3) A net $\{f_j\}_{j \in J}$ in $E$ is called *Cauchy* if and only if for every $0$-neighborhood $U \subset E$ there exists a $j_0 \in J$ such that for all $j, j' \ge j_0$ we have $f_j - f_{j'} \in U$. Two Cauchy nets $\{x_j\}_{j \in J}$ and $\{y_{j'}\}_{j' \in J'}$ in $E$ are *equivalent* if and only if the net $\{x_j - y_{j'}\}_{(j, j') \in J \times J'}$ converges to $0$; equivalently, for every $0$-neighborhood $U \subset E$ there exist $j_0 \in J$ and $j'_0 \in J'$ such that $x_j - y_{j'} \in U$ for all $j \ge j_0$, $j' \ge j'_0$ (this is clearly an equivalence relation).

(4) A subset $A \subset E$ is called *complete* when it is Hausdorff and every Cauchy net in $E$ valued in $A$ converges in $A$.

(5) The topological vector space $E$ is called *Fréchet* when it is locally convex, complete, and metrizable.

In the metrizable case, completeness in the classical sense of Cauchy *sequences* guarantees completeness in the broader sense of nets because there is a countable base of $0$-neighborhoods. Indeed, if $\{x_j\}_{j \in J}$ is a Cauchy net in a metrizable $E$, say with $|\cdot| : E \to \mathbf{R}_{\ge 0}$ a pseudo-norm for which the metric $|x - y|$ induces the topology [Scha, Ch. I, 6.1], then for all $n \ge 1$ there exists $j_n \in J$ with $|x_j - x_{j'}| < 1/n$ for all $j, j' \ge j_n$. We can arrange that $j_{n+1} \ge j_n$ for all $n$, so $\{y_n := x_{j_n}\}$ is a Cauchy sequence in $E$ such that $|x_j - y_n| < 1/n$ for all $j \ge j_n$. Thus, if the limit $\ell := \lim_{n \to \infty} y_n \in E$ exists then we see that $x_j \to \ell$.

For any Hausdorff topological vector space $E$, there is an initial object $(\widehat{E}, i)$ among complete Hausdorff topological vector spaces equipped with a continuous linear map from $E$, with the canonical map $i : E \to \widehat{E}$ a topological embedding (in particular, injective) and a base of closed $0$-neighborhoods in $\widehat{E}$ given by closures in $\widehat{E}$ of $0$-neighborhoods in $E$. We call $(\widehat{E}, i)$ the *completion* of $E$. The construction of completion for metric spaces via equivalence classes of Cauchy sequences can be adapted to Cauchy nets to build $(\widehat{E}, i)$, as is done in [?]. The universal mapping property, topological embedding property of $i$, and $0$-neighborhood base description in $\widehat{E}$ are all seen from that construction.

Remark C.1.3.2. The main technical difficulty in the construction (in contrast with the metric setting) is that the directed set $J$ can vary a lot (especially when it is uncountable); e.g., in the definition of Cauchy net $\{f_j\}_{j \in J}$ there is no constraint on the cardinality of $J$ and so there is no "set of all nets valued in $E$". But all we need is a set of all *equivalence classes* of nets valued of $E$, and this does exist because we claim every net $f : J \to E$ is equivalent to a net $x : J' \to E$ where $J'$ has cardinality bounded in term of $E$.

Such set-theoretic control is not addressed in [?], and it can be handled as follows. For each $j \in J$, let $F_j \subset E$ be the subset of points $f_i$ for all $i \ge j$; this throws away the indexing information on points provided by $f : J \to E$. Each $F_j$ is a non-empty subset of $E$ and any two contain a third, so the set $\mathscr{F}$ of subsets

## PDF page 660

**660** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

$F_j \subset E$ is directed by reverse inclusion; beware that a containment $F_j \subset F_{j'}$ (and even an equality) does not imply $j, j' \in J$ are comparable (nor equal when $F_j = F_{j'}$). The Cauchy hypothesis implies that for every $0$-neighborhood $U \subset E$ there exists $F \in \mathscr{F}$ so that any two points in $F$ have difference contained in $U$. Thus, if we define a net $x : \mathscr{F} \to E$ by letting $x_F \in F$ be a choice of point for each $F \in \mathscr{F}$ then $\{x_F\}_{F \in \mathscr{F}}$ is Cauchy and equivalent to the given Cauchy net $\{f_j\}_{j \in J}$: for a choice of $0$-neighborhood $U \subset E$ there exists $j_0 \in J$ so that $f_j - f_{j'} \in U$ for all $j, j' \ge j_0$, so if $F_0 := F_{j_0}$ then $x_F - f_j \in U$ for all $F \subset F_0$ and all $j \ge j_0$. Since $\mathscr{F}$ has cardinality bounded by that of the power set of $E$, we have the desired set-theoretic control.

In most other references (e.g., [Tre, Ch. 5]), arguments based on Cauchy filters are used to construct $\widehat{E}$. The relation between completeness by Cauchy-net convergence and completeness by Cauchy-filter convergence is discussed in [NB, Thm. 3.1.6] (in the wider setting of commutative topological groups). Another approach is given in [NB, §3.7, §4.8], which uses a notion of completeness that makes sense for non-Hausdorff $E$ (in which case completions can fail to be unique even up to linear topological isomorphism [NB, Ex. 3.7.3]).

Remark C.1.3.3. We have opted in favor of nets over filters because for our purposes arguments via nets foster reasoning by analogy with sequential convergence in corresponding classical situations. Since the topology of locally convex vector spaces is generated by a family of seminorms, nets are convenient for studying the convergence of vector-valued integrals (often valued in *non-normable* complete locally convex topological vector spaces) and other settings that shall arise in this work.

The role of nets rather than just sequences is crucial, because many Hausdorff locally convex spaces of importance in this work do *not* have a countable base of $0$-neighborhoods (equivalently are not metrizable [Scha, Ch. I, 6.1]). This happens for the Schwartz-Bruhat space $\mathcal{S}(G)$ where $G$ is the adele ring $\mathbf{A}_F$ and idele class group $C_F$ of a number field $F$ as well as a non-archimedean local field $L$ (even though $\mathcal{S}(L)$ has countable $\mathbf{C}$-dimension); such spaces $\mathcal{S}(G)$ are studied in depth in Appendix D.

To explain this non-metrizability, we first note that §C.1.5 will discuss a natural Hausdorff locally convex topology on direct limits $E = \varinjlim E_n$ where the $E_n$'s are Hausdorff locally convex topological vector spaces and the continuous linear transition maps $E_n \to E_{n+1}$ are topological embeddings (this is generally strictly coarser than the "inductive limit topology" as in general topology: the continuous bijection from the topological inductive limit to the locally convex inductive limit is usually not a homeomorphism). When the $E_n$'s are all complete then such $E$ is complete [Scha, Ch. II, 6.6] but if the $E_n$'s are all Fréchet and $E_n \ne E_{n+1}$ for all $n$ then $E$ cannot be metrizable because otherwise it would be Fréchet (by completeness) and so Lemma C.1.5.4 below applied to the identity map $E \to \varinjlim E_n$ would force $E = E_n$ for all sufficiently large $n$, a contradiction. The topology on $\mathcal{S}(G)$ for the number-theoretic examples $G$ mentioned above is always of such type $\varinjlim E_n$ that we have just seen is never metrizable.

Remark C.1.3.4. Much as the quotient of a Banach space by a closed subspace is again Banach (using an associated "residue norm"), the quotient $E/M$ of a Fréchet space $E$ modulo a closed subspace $M$ is Fréchet: it inherits local convexity from $E$, and by [Scha, Ch. I, 6.3] it is complete and metrizable. However, beyond the metrizable setting the quotient of a complete Hausdorff locally convex $E$ modulo a closed subspace can fail to be complete; examples are given in [Scha, Exer. 11, p. 192].

**C.1.4. Boundedness and quasi-completeness.** For a topological vector space $E$, a subset $A \subset E$ is called *bounded* if for every neighborhood $U$ of $0$ in $E$ there exists $\lambda \in \mathbf{C}^{\times}$ such that $\lambda A \subset U$ (equivalently, $A \subset \mu U$ for some $\mu \in \mathbf{C}$). Observe that this notion is intrinsic to the topological vector space structure and is generally *not* the same as metric-boundedness when $E$ is metrizable (since one can always find a bounded metric giving the same topology), but it is the same as norm-boundedness when $E$ is normable. Boundedness is an important notion in this work.

In the absence of a norm it may seem difficult to verify boundedness in examples, so it is useful to have a some criteria for boundedness. In a Hausdorff locally convex vector space $E$ whose topology is generated by a

## PDF page 661

**C.1. LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES** · **661**

family of seminorms $\{p_i\}_{i \in I}$, a subset $B \subset E$ is bounded if and only if either of the following (equivalent) conditions holds:

(1) $p_i(B) \subset \mathbf{R}$ is bounded for every $i \in I$ (this restates the definition of boundedness since the $p_i$'s define the topology of $E$),

(2) for any *sequence* $\{b_k\}_{k \ge 1} \subset B$ and sequence $\{\lambda_k\}_{k \ge 1}$ in $\mathbf{C}$ tending toward $0$, $\lambda_k b_k \to 0$ [Scha, Ch. I, 5.3].

A useful alternative criteria from [Scha, Ch. IV, 3.3] identifies boundedness with "weak boundedness":

Proposition C.1.4.1. *Let $E$ be a Hausdorff locally convex topological vector space. A subset $B \subset E$ is bounded if and only if the image $\ell(B) \subset \mathbf{C}$ is bounded for every continuous linear functional $\ell : E \to \mathbf{C}$.*

Definition C.1.4.2. A subset $A$ of a Hausdorff topological vector space $E$ is called *relatively compact* if its closure in $E$ is compact, and it called *pre-compact* if its closure in the completion $\widehat{E}$ is compact (i.e., pre-compactness means relative compactness in $\widehat{E}$).

Relatively compact subsets of $E$ are pre-compact since a compact subset of $E$ is certainly also closed in $\widehat{E}$. By [Tre, Prop. 6.9] (whose proof uses self-contained arguments with filters, ultrafilters, and Cauchy filters, the latter of which can be used to make Cauchy nets by picking a point in each member of the filter), pre-compactness for a subset $A \subset E$ is equivalent to *total boundedness* of $A$ in $E$: $A$ is covered by finitely many translates of each $0$-neighborhood $V \subset E$. Totally bounded subsets $A \subset E$ are bounded (in particular, pre-compact subsets of $E$ are bounded), but the converse is false; e.g., the closed unit ball in any infinite-dimensional Hilbert space is bounded but non-compact and so is not pre-compact, hence not totally bounded.

Remark C.1.4.3. We caution the reader that pre-compactness is defined differently in various references. For example, total boundedness in $E$ is taken as the definition of pre-compactness in [NB, Def. 3.3.1], in which case the work shifts to proving total boundedness in $\widehat{E}$ implies relative compactness. In [Scha, p. 8] pre-compactness for a subset $A \subset E$ is defined as compactness for the completion of $A$ in the sense of uniform structures, but it is noted in [Scha, p. 25] that this is equivalent to compactness of the closure in $\widehat{E}$ and to total boundedness (these equivalences are sufficient for all use of pre-compactness in [Scha]). For the purpose of our literature citations related to pre-compactness, the equivalence of total boundedness of $A \subset E$ and compactness of the closure of $A$ in $\widehat{E}$ [Tre, Prop. 6.9] is sufficient.

Many locally convex topological vector spaces, some of interest to this work, *are not complete*. Here are two related examples arising from any infinite-dimensional Hilbert space $H$.

Example C.1.4.4. The locally convex weak topology $\sigma(H, H')$ on $H$ of convergence under continuous functionals (i.e., a base of $0$-neighborhoods is given by $\{|\langle \cdot, x_1 \rangle| < \varepsilon, \ldots, |\langle \cdot, x_n \rangle| < \varepsilon\} \subset H$ for $x_1, \ldots, x_n \in H$ and $\varepsilon > 0$) is not complete. Indeed, if $\ell \in H^*$ is a discontinuous linear functional on $H$ then for each finite-dimensional subspace $V \subset H$ we can use the Hahn-Banach Theorem to build a continuous $\ell_V = \langle \cdot, x_V \rangle \in H' \simeq H$ extending $\ell|_V$ [Scha, Ch. II, 4.2]. Ordering the set of such $V$'s via inclusion, we see that $\{x_V\}_V$ is a Cauchy net in $H$ (since for any $y_1, \ldots, y_n \in H$ we have $\langle x_V - x_W, y_i \rangle = 0$ when $V, W$ contain all $y_i$'s), but $\{x_V\}$ has no limit $x \in H$ for the weak topology. Indeed, if $x_V \to x$ weakly then $\langle y, x \rangle = \lim \langle y, x_V \rangle = \lim \ell_V(y) = \ell(y)$ for all $y \in H$, which is to say $\ell = \langle \cdot, x \rangle$, contradicting that $\ell$ is discontinuous.

Example C.1.4.5. Equip the space $\mathscr{B}(H)$ of bounded linear operators on $H$ with the locally convex strong operator topology of pointwise convergence (rather than the operator-norm topology). A discontinuous linear functional on $H$ can be used (similarly to Example C.1.4.4) to construct a Cauchy net in $\mathscr{B}_{\mathrm{SOT}}(H)$ that is not bounded (in contrast with Cauchy sequences, which are bounded in any topological vector space); this implies $\mathscr{B}_{\mathrm{SOT}}(H)$ is not complete. See Remark C.4.3.4 for details on the construction.

## PDF page 662

**662** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

In both of the preceding examples, the failure of completeness has a salvage: those spaces are *quasi-complete*: closed bounded subsets are complete (in the sense of convergence of Cauchy nets). Some references call this *bounded completeness*. It is immediate from the definitions that any complete $E$ is quasi-complete.

Since all Cauchy nets in a compact subset of a Hausdorff topological vector space clearly converge, quasi-completeness of $H_{\sigma(H, H')}$ in Example C.1.4.4 is a consequence of two facts: (i) Proposition C.1.4.1 and (ii) all bounded subsets of such a Hausdorff locally convex topological vector space $E$ are pre-compact relative to the weak topology $\sigma(E, E')$ (essentially Alaoglu's theorem: [Scha, Ch. IV, Cor. 2 to 5.5]). Quasi-completeness of $\mathscr{B}_{\mathrm{SOT}}(H)$ in Example C.1.4.5 is deduced from the Uniform Boundedness Principle for Banach spaces: see Lemma C.2.1.7 (applied with $E = F = H$ and $\mathfrak{S}$ the set of finite subsets of $H$).

Quasi-completeness is a consequential concept throughout this work, insofar as there is a good integration theory for functions valued in quasi-complete Hausdorff locally convex topological complex vector spaces. This goes far beyond the Banach-valued theory of Bochner that is inapplicable for our purposes (since we need to work with infinite-dimensional nuclear Fréchet spaces, and those are never normable [Tre, Cor. 2 to Prop. 50.2]). The key stability property of quasi-completeness that enables integration theory to take off is [Scha, Ch. II, Cor. to 4.3]: the closed convex circled hull of a pre-compact subset of a quasi-complete Hausdorff locally convex topological $\mathbf{C}$-vector space is compact. More on quasi-completeness and its role will be discussed in §C.4 on integration in the sense of Pettis and §C.5 on holomorphy and meromorphy for vector-valued functions on a Riemann surface (such as the surface $\Omega(C_F)$ of quasi-characters of the idele class group $C_F$ of a number field $F$).

Example C.1.4.6. Of main interest to this work are the following classes of locally convex spaces:

(1) separable Hilbert spaces: they are locally convex since their topology is even normed, and are complete (so quasi-complete).

(2) Banach spaces: specifically, the Banach space of bounded linear operators on a Hilbert space equipped with the operator-norm topology. By completeness, they are quasi-complete too.

(3) The spaces $\mathcal{S}(G)$ of Schwartz-Bruhat functions on second-countable locally compact abelian groups $G$, especially those $G$ of arithmetic origin such as the adele ring of a number field, the idele class group of a number field, and their local analogs. As was discussed in Remark C.1.3.3, these have natural locally convex topologies that are often non-metrizable but complete.

Much deeper is that such spaces $\mathcal{S}(G)$ are nuclear (a concept reviewed in §C.2.4) and Montel (this means compactness of closed bounded subsets and reflexivty in the sense that the continuous double-duality map $E \to (E'_{\beta})'_{\beta}$ for the strong-dual topologies [Scha, pp. 144-5] is a topological isomorphism). These further properties are established in Theorem D.1.5.7.

(4) LF-spaces: As will be discussed in §C.1.5, for any inductive system $\{E_{\alpha}\}$ of locally convex topological vector spaces there is a natural locally convex topology on $\varinjlim E_{\alpha}$ making it have the expected universal mapping property [Scha, Ch. II, p. 54]. By construction the natural continuous linear map $\oplus E_{\alpha} \to \varinjlim E_{\alpha}$ is a topological quotient map, so a base for the topology in such inductive limits is given by the image of a base for the topology in the corresponding locally convex direct sum $\oplus E_{\alpha}$; one such base for the latter is given in (C.1.5.1) below.

The most important cases of interest are *Hausdorff* locally convex *countable* inductive limits $E = \varinjlim E_n$ of Fréchet spaces $E_n$, which are called *LF-spaces* as in [Gro-f, Def. 4 p. 146]. We call such $E$ a *strict LF-space* when we can choose the transition maps $E_n \to E_{n+1}$ to be topological embeddings, in which case it is automatic (i.e., does not need to be imposed as an additional requirement) that $E$ is Hausdorff and $E_n \to E$ is a topological embedding for all $n$ [Scha, Ch. II, 6.4]. The strictness hypothesis is assumed for all work with inductive limits in [Scha] (after the initial construction) and in [Tre] (see [Tre, p. 126]).

There is a powerful Open Mapping Theorem for LF-spaces without a strictness assumption (see Theorem C.1.5.5 below); its proof ultimately bootstraps from the more familiar Fréchet case. This result is

## PDF page 663

**C.1. LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES** · **663**

often used in the present work to deduce that an LF-space not yet known to be strict is actually so. From the definitions one sees that any quotient of an LF-space is an LF-space, but beware that a quotient of a strict LF-space can fail to be strict. Indeed, since $E = \varinjlim E_n$ is always a topological quotient of $\oplus_{n \ge 1} E_n$ that is itself strict (as $\varinjlim F_N$ for $F_N = \oplus_{1 \le n \le N} E_n$ with the evident transition maps), any non-strict LF-space provides such an example and [SN, §2, Ex. 2] gives a class of such examples.

Remark C.1.4.7. The vast majority of the Hausdorff locally convex topological vector spaces of interest to this work are nuclear Montel LF-spaces. In fact, they will generally arise for us as a strict countable locally convex inductive limit of nuclear Fréchet spaces (such inductive limits are always nuclear and Montel by [Scha, Ch. II, 6.6, Cor. to 7.2; Ch. III, Cor. to 7.4] and [Tre, Cor. 3 to Prop. 50.2]), but sometimes the verification of strictness rests on the Open Mapping Theorem for general LF-spaces. Good properties of strict inductive limits are provided throughout [Scha], which is our main reference on the matter (but again, we emphasize the power of Open Mapping Theorem for LF-spaces without a strictness hypothesis).

We will provide guidance on where to find the required foundational results on locally convex topological vector spaces as the need arises. Our main references are [Scha, Ch. I–IV] (especially for duality and some basic aspects of nuclearity) and [Tre] (especially for topological tensor products and deeper aspects of nuclearity), along with [Gro-b] for Grothendieck's work on topological tensor products and nuclear spaces (particularly the inductive tensor product topology that we need rather crucially and does not seem to be systematically treated apart from [Gro-b]). Some other useful references are [Bou-TVS, Ch. II, IV], [Jar, Ch. 2, 6, 8], [Cnw-a, Ch. IV], and [NB, Ch. 4, 5, 8],

**C.1.5. Inductive limits and detection of limit subspaces.** In this subsection we discuss some complements around inductive limits in the category of locally convex topological vector spaces (over $\mathbf{C}$), with a focus on the special case of a sequence $\{E_k\}_{k \ge 0}$ of Hausdorff locally convex topological $\mathbf{C}$-vector spaces equipped with continuous injective linear maps $f_k : E_k \to E_{k+1}$ for each $k \ge 0$.

If $\{E_{\alpha}, f_{\alpha\beta}\}$ is an inductive system of locally convex topological vector spaces over $\mathbf{C}$, we can put a locally convex topology on $E := \varinjlim E_{\alpha}$ having the desired universal property (namely, a linear map $g : E \to F$ to a locally convex topological vector space $F$ is continuous if and only if the composite linear maps $E_{\alpha} \to E \to F$ are all continuous) provided that this can be done for the direct sum $\oplus E_{\alpha}$. Indeed, if direct sums can be equipped with such a locally convex topology then the quotient topology on $E$ from the direct sum via the usual algebraic construction of $E$ will do the job for $E$ due to the universal property of the quotient topology on $V/W$ for any locally convex $V$ and linear subspace $W$ (since the topology on $V/W$ is also locally convex).

For an arbitrary algebraic direct sum $E = \oplus E_{\alpha}$ of locally convex $E_{\alpha}$'s, a locally convex topology on $E$ having the categorical mapping property for a direct sum is the one with a base of $0$-neighborhoods given by the sets

(C.1.5.1)
$$
U = \left\{ \sum \lambda_{\alpha} x_{\alpha} : x_{\alpha} \in U_{\alpha}, \sum |\lambda_{\alpha}| \le 1 \right\}
$$

where $U_{\alpha}$ is a convex circled $0$-neighborhood in $E_{\alpha}$ (in each sum $\sum \lambda_{\alpha} x_{\alpha}$ all but finitely many $x_{\alpha}$'s vanish and so only the corresponding $\lambda_{\alpha}$'s matter; i.e., $\sum |\lambda_{\alpha}|$ may be assumed to have only finitely many non-zero terms). Since each $U_{\alpha}$ is circled, it is equivalent to require the $\lambda_{\alpha}$'s to be real numbers in $[0, 1]$, which is to say $U$ is the convex hull of choices of convex circled $0$-neighborhoods $U_{\alpha} \subset E_{\alpha}$ over all $\alpha$. Note that each $E_{\alpha_0} \to \oplus E_{\alpha}$ is a topological embedding.

In the special case of a locally convex countably infinite direct sum $E$ of *normed* spaces $E_k$ ($k \ge 1$), we can scale each member of a *countably infinite* collection of $0$-neighborhoods in $E$ so the rescaled $0$-neighborhoods all contain a common $0$-neighborhood, as recorded below. This will be useful in our later discussion of how countable locally convex inductive limits interact with the "projective" tensor product topology.

## PDF page 664

**664** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

Proposition C.1.5.1. *Let $E$ be the locally convex topological vector space $\bigoplus_{k\ge 1}E_k$ for a sequence of normed vector spaces $E_1,E_2,\dots$ over $\mathbf C$. For any sequence of $0$-neighborhoods $V_1,V_2,\dots\subset E$ there are scalars $\rho_i\in\mathbf R_{>0}$ such that $\bigcap_{i\ge 1}\rho_iV_i$ is a $0$-neighborhood.*

Proof. It is harmless to shrink each $V_i$, so via (C.1.5.1) we can assume $V_i$ is the convex circled hull of $\bigoplus_{k\ge 1}U_{ik}$ for $0$-neighborhoods $U_{ik}\subset E_k$ for all $k\ge 1$:

$$
V_i=\left\{\sum_{k\ge 1}\lambda_ku_{ik}:u_{ik}\in U_{ik},\sum|\lambda_k|\le 1\right\}.
$$

Since each $E_k$ is normed, we can further shrink each $U_{ik}$ to be bounded in $E_k$. Letting $\rho_1=1$, we recursively pick $\rho_n$ for all $n\ge 1$ by requiring

$$
\rho_nU_{nk}\supset\rho_iU_{ik}\ \text{inside }E_k\ \text{for all }1\le k\le n,\ 1\le i<n
$$

(as we may do each each $U_{ik}\subset E_k$ is a bounded $0$-neighborhood).

By design, for all $k\ge 1$ and $i>k$ we have $\rho_iU_{ik}\supset\rho_kU_{kk}$. Thus, for all $k\ge 1$ we have

$$
\bigcap_{i\ge 1}\rho_iU_{ik}\supset\bigcap_{1\le i\le k}\rho_iU_{ik}=:W_k
$$

(since for $i>k$ the $i$th term in the intersection on the left contains $\rho_kU_{kk}$). Since $W_k$ is an intersection of finitely many $0$-neighborhoods in $E_k$, it is also a $0$-neighborhood in $E_k$. By design, for each $i\ge 1$ and all $k\ge 1$ we have $\rho_iU_{ik}\supset W_k$, so

$$
\rho_iV_i\supset\left\{\sum\lambda_kw_k:w_k\in W_k,\sum|\lambda_k|\le 1\right\}=:W
$$

for all $i$. This says that the $0$-neighborhood $W$ in $E$ is contained in every $\rho_iV_i$, so $\bigcap_{i\ge 1}\rho_iV_i$ is a $0$-neighborhood in $E$ as desired. $\square$

Let us now focus on the special case that $E$ is Hausdorff and is the locally convex inductive limit of a countable inductive system $\{(E_k,f_k)\}_{k\ge 0}$ for which the transition maps $f_k:E_k\to E_{k+1}$ are injective. The best-behaved situation is when each $f_k$ is moreover a topological embedding and the $E_k$'s are all Hausdorff; such cases are called *strict*. In the strict case (as we noted in Example C.1.4.6(4)), automatically such an inductive limit $E$ is Hausdorff and each $E_k\to E$ is a topological embedding. (Beware that in [Scha] the terminology "locally convex topological vector space" includes a Hausdorff hypothesis but the terminology "locally convex topology" does not). The following is given in [Gro-f, p. 146].

Definition C.1.5.2. A locally convex topological vector space $E$ is called an *LF-space* if it is Hausdorff and $E=\varinjlim E_k$ for a sequence of continuous linear maps $f_k:E_k\to E_{k+1}$ between Fréchet spaces.

Letting $i_k:E_k\to E$ be the natural continuous linear map, by the universal property of $E$ we see that for the formation of $E$ it is harmless to replace each $E_k$ with $E_k/\ker(i_k)$ (which is also Fréchet since $\ker(i_k)$ is closed due to continuity of $i_k$ and the Hausdorff hypothesis on $E$; see Remark C.1.3.4). In other words, we lose no generality in Definition C.1.5.2 by assuming the $f_k$'s are injective. The following description of boundedness in the strict case under a closedness hypothesis on the maps $E_k\to E_{k+1}$ (as holds when all $E_k$'s are complete, for example) is [Scha, Ch. II, 6.5] and is very useful:

Proposition C.1.5.3. *If $E=\varinjlim E_k$ is strict with each $E_k\to E_{k+1}$ a closed embedding, a subset $B\subset E$ is bounded if and only if $B$ is a bounded subset of some $E_k$.*

Remarkably, if $E=\varinjlim E_k$ with each $E_k\to E_{k+1}$ injective between Fréchet spaces and *without* assuming such maps are topological embeddings (or equivalently that each $i_k:E_k\to E$ is a topological embedding), the Open Mapping Theorem for Fréchet spaces yields a continuous factorization property through the $E_k$'s:

## PDF page 665

**C.1. LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES** · **665**

Lemma C.1.5.4. *Let $E$ be a Hausdorff topological vector space equipped with continuous linear injections $i_k:E_k\to E$ from Fréchet spaces for $k\ge 1$ such that $i_k(E_k)\subset i_{k+1}(E_{k+1})$ for all $k$ and $E=\bigcup_k i_k(E_k)$. Any continuous linear map $u:F\to E$ from a Fréchet space $F$ factors continuously through some $i_k:E_k\to E$.*

Proof. This result is [Gro-f, Thm. 1, p. 147], and for the convenience of the reader we provide the proof. Let $H_k=\{(x,y)\in F\times E_k:u(x)=i_k(y)\}$, a subspace of the Fréchet $F\times E_k$ that is closed since $E$ is Hausdorff (as the diagonal of $E$ is then closed in $E\times E$), so $H_k$ is Fréchet. The linear projection $p_k:H_k\to F$ to the first factor is injective since $i_k$ is injective, with $p_k(H_k)\subset p_{k+1}(H_{k+1})$ for all $k$. By hypothesis $F$ is the union of the rising countable sequence of linear subspaces $p_k(H_k)$ (since each $u(x)\in E$ lies in some $i_k(E_k)$), so the Fréchet property of $F$ implies via the Baire category theorem that one of the linear subspaces $p_{k_0}(H_{k_0})$ has closure in $F$ with non-empty interior, so that closure is equal to $F$. In other words, the continuous linear injection $p_{k_0}:H_{k_0}\to F$ has dense image for some $k_0$.

We claim $p_{k_0}$ is surjective. Since $H_{k_0}$ is a complete metric space, by [Gro-f, Lemma, p. 39] a sufficient criterion for surjectivity is that the closure $\overline{p_{k_0}(U)}\subset F$ is a $0$-neighborhood for every $0$-neighborhood $U\subset H_{k_0}$. Pick any $0$-neighborhood $U\subset H_{k_0}$, and then choose a $0$-neighborhood $V\subset H_{k_0}$ so that $V-V\subset U$. Closures in $F$ are obtained via sequential limits since $F$ is metrizable, so $\overline{p_{k_0}(V)}-\overline{p_{k_0}(V)}\subset\overline{p_{k_0}(V-V)}\subset\overline{p_{k_0}(U)}$. Thus, it suffices to show that differences among $\overline{p_{k_0}(V)}$ exhaust a $0$-neighborhood in $F$.

Since $\bigcup_{n\ge 1}nV=H_{k_0}$, the countable collection $np_{k_0}(V)$ of subsets of $F$ has union $p_{k_0}(H_{k_0})$ that is dense in $F$. Thus, by the Baire category theorem some $n_0p_{k_0}(V)$ has closure in $F$ with non-empty interior. Hence, $p_{k_0}(V)$ has closure in $F$ with non-empty interior. Differences among pairs from any non-empty open subset of $F$ exhaust a $0$-neighborhood, so $\overline{p_{k_0}(V)}-\overline{p_{k_0}(V)}$ is a $0$-neighborhood in $F$ as desired.

By the Open Mapping Theorem for complete metrizable topological vector spaces (see [KG, pp. 53-54], where the existence of a translation-invariant metric [Scha, Ch. I, Thm. 6.1(iv)] is used near the end of the proof), the continuous linear bijection $p_{k_0}$ is a topological isomorphism and so its continuous inverse $F\to H_{k_0}$ followed by the continuous projection $H_{k_0}\to E_{k_0}$ defines a *continuous* linear map $v:F\to E_{k_0}$ such that $i_{k_0}\circ v=u$. $\square$

The preceding lemma is used in the proof of the Open Mapping Theorem for LF-spaces which does not require strictness. One even gets a more general result:

Theorem C.1.5.5 (Open Mapping Theorem). *Let $q:F\to E$ be a surjective continuous linear map between Hausdorff topological vector spaces with $E$ an LF-space and $F$ exhausted by a rising sequence of images of continuous linear maps $u_n:F_n\to F$ with Fréchet $F_n$'s (e.g., $F$ also an LF-space). Then $q$ is open, or equivalently $F/\ker(q)\to E$ is a topological isomorphism.*

*In particular, a continuous linear surjection between LF-spaces is open.*

Although there is no strictness hypothesis, it is assumed each of $E$ and $F$ is Hausdorff. This result is a special case of [Gro-f, Thm. 2(1), p. 148], which works with a wider class of spaces $E$ that Grothendieck called "strictly bornological" [Gro-f, p. 148] (later called "ultrabornological": see [NB, Def. 13.2.3(b), Ex. 13.2.8(d), Thm. 13.2.11]). For the reader's convenience, we give Grothendieck's proof specialized to the context as stated in Theorem C.1.5.5 that suffices for our needs.

Proof. We write $E=\varinjlim E_k$ for an inductive system $\{E_k\}$ of Fréchet spaces, and since $E$ is Hausdorff each $f_k:E_k\to E$ has closed kernel. The quotient $E'_k$ of $E_k$ by $\ker(f_k)$ is therefore also Fréchet, and by consideration of the universal property of $\varinjlim E_k$ we see that the natural map $\varinjlim E'_k\to E$ is an isomorphism. Thus, we may and do replace $E_k$ with $E'_k$ so that each continuous linear map $f_k:E_k\to E$ is injective. We can likewise replace $F$ by the Hausdorff $F/\ker(q)$ (note that $\ker(q)$ is closed since $E$ is Hausdorff), so $q$ is now a linear bijection, and we can then replace each $F_n$ by $F_n/\ker(u_n)$ so that each $u_n$ is injective (beware that

## PDF page 666

**666** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

the resulting continuous linear bijection $\varinjlim F_n\to F$ might not be a homeomorphism; we don't even know if the locally convex topology on $\varinjlim F_n$ is Hausdorff).

Our aim is to show that the linear inverse of the continuous linear bijection $q:F\to E=\varinjlim E_k$ is continuous. By the universal property of such a locally convex inductive limit, we just have to show that each linear map $E_k\to E \overset{q^{-1}}{\simeq} F$ is continuous. Since $E$ is exhausted by the rising sequence of subspaces $q(F_n)$ with $q:F_n\to E$ a continuous linear injection with Fréchet $F_n$, by Lemma C.1.5.4 each $E_k\to E$ factors continuously through some $F_{n_k}\to E$. In other words, $q(F_{n_k})\supset E_k$ with the resulting linear map $E_k\to F_{n_k}$ continuous. But then the composite map $E_k\to F_{n_k}\xrightarrow{u_{n_k}}F$ is continuous, and this is exactly $q^{-1}|_{E_k}$. $\square$

$^1$

C.1.5.1. *Acyclicity and limit subspaces of LF-spaces.* A technically important but rather subtle aspect of LF-spaces is centered around the following concept:

Definition C.1.5.6. Let $E$ be an LF-space, and let $f_k:E_k\to E_{k+1}$ be a sequence of injective linear maps (not necessarily a topological embedding) between Fréchet spaces such that $E\simeq\varinjlim E_k$. A closed subspace $F\subset E$ is called a *limit subspace* if for $F_k=F\cap E_k$ equipped with with the subspace topology from $E_k$, the continuous linear bijection $\varinjlim F_k\to F$ a topological isomorphism.

The preceding concept is independent of the choice of defining sequence $\{E_k\}$ for $E$. Indeed, if $\{E'_k\}$ is a second such defining sequence then $E_k\to E$ factors continuously through some $E'_{k'}\to E$ by Lemma C.1.5.4 and likewise each $E'_{k'}\to E$ factors continuously through some $E_k\to E$. This ensures that for $F_k=F\cap E_k$ and $F'_{k'}=F\cap E'_{k'}$ the natural linear bijection between the countable inductive limits $\varinjlim F_k$ and $\varinjlim F'_{k'}$ (via their identifications with $F$) is a topological isomorphism.

Closed subspaces $F\subset E$ in LF-spaces are not generally limit subspaces, by they are under some favorable conditions. We provide a sufficient criterion below, recorded here for ease of access. This rests on the concept of *acyclicity* that was developed by Palamodov [Pa, §7, p. 38] (resting on homological techniques) and Retakh [Ret], and further studied by Vogt (see [Vogt-1, §2], and specifically [Vogt-1, §2, Thm. 2.10, p. 67], where Retakh's characterization of acyclic LF-spaces is reproved avoiding homological methods).

Strict LF-spaces are acyclic, as we will be discussing below, and we will see in Theorem C.1.5.11 that if each of the members $E_k$ of a defining countable strict inductive system is nuclear then any closed subspace $F\subset E$ for which $q:E\to E/F$ lifts bounded subsets (i.e., each bounded $B\subset E/F$ has the form $q(B')$ for bounded $B'\subset E$) is a limit subspace and so is itself a strict LF-space. These conditions will always be fulfilled for the applications discussed throughout this work.

For the following example due to Grothendieck, we refer the reader to the discussion in the second half of [Gro-e, §II.3, p. 98]. It provides an example of a closed subspace $F$ of a strict locally convex inductive limit $E$ of an increasing sequence of Fréchet spaces $E_k$ such that $F$ is not an LF-space.

Example C.1.5.7 (A closed subspace of a strict LF-space which is not a limit subspace). There exists a countable locally convex direct sum $E$ of Banach spaces and a closed subspace $F\subset E$ such that $F$ is not an LF-space with respect to the subspace topology. In particular, $F$ is not a limit subspace. This answers a question of Dieudonné and Schwartz from 1954 [DS, §15, no. 2, p. 97].

To be specific, pick $1<p,q<\infty$ with $1/p+1/q=1$ and let $E=\bigoplus_{n\ge 1}\ell^q(\mathbf N)$, so the topological dual $E'$ of $E$ is identified as a vector space with $\prod_{n\ge 1}\ell^p(\mathbf N)$. By [Scha, Ch. IV, 3.4, 4.3(2)], the locally convex Mackey topology $\tau(E',E)$ on $E'$ is the product topology. There is a closed subspace $F'\subset E'$ that is a Köthe sequence

---

$^1$Adjust cross-references all throughout the document to refer to Theorem C.1.5.5 as opposed to the literature, for the Open Mapping Theorem for LF-spaces. Say somewhere appropriate what Köthe exactly proved, as opposed to Grothendieck's version.

## PDF page 667

**C.1. LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES** · **667**

space$^2$ such that the two natural strong topologies$^3$ on the closed subspace $F:=F'^{\perp}\subset E$ are distinct. The subspace topology on $F$ is not an LF-space.$^4$

Definition C.1.5.8. A countable inductive system $\{E_k\}_{k\ge 0}$ of Hausdorff locally convex topological $\mathbf C$-vector spaces with transition maps $f_k:E_k\to E_{k+1}$ is called *acyclic* if and only if the natural algebraically short exact sequence of $\mathbf C$-linear maps

$$
0\to\bigoplus_{k\ge 0}E_k \xrightarrow{\sigma} \bigoplus_{k\ge 0}E_k \xrightarrow{q} E:=\varinjlim E_k\to 0 \tag{C.1.5.2}
$$

(with $q$ topologically a quotient map) has $\sigma$ a closed topological embedding, where $\sigma$ is the $\mathbf C$-linear map defined by

$$
\sigma((x_k)_{k\ge 0}):=(x_k-x_{k-1})_{k\ge 0},\ x_{-1}:=0 \tag{C.1.5.3}
$$

(also writing $x_k$ also for the image of $x_{k-1}$ into $E_k$ under $f_{k-1}$, where $f_{-1}:=0$).

In the setup of Definition C.1.5.8, $q$ is the linear map $q:(x_k)_{k\ge 0}\mapsto\sum_{k\ge 0}x_k$ (where the sum is finite) and $\sigma$ admits a linear algebraic inverse $\sigma^{-1}:\ker(q)\to\bigoplus_{k\ge 0}E_k$ defined by

$$
\sigma^{-1}((x_k)_{k\ge 0}):=(y_k)_{k\ge 0} \tag{C.1.5.4}
$$

where $y_k:=\sum_{0\le j\le k}x_k$ is the $k$th partial sum of the finite sum $\sum_{k\ge 0}x_k$. Indeed,

$$
\sigma(\sigma^{-1}((x_k)_{k\ge 0}))=(\sum_{0\le j\le k}x_j-\sum_{0\le j\le k-1}x_j)_{k\ge 0}=(x_k)_{k\ge 0}
$$

and $\sigma^{-1}(\sigma((x_k)_{k\ge 0}))=\sigma((x_k-x_{k-1})_{k\ge 0})$ with $x_{-1}:=0$, which reads $\sigma^{-1}(\sigma((x_k)_{k\ge 0}))=(x_k)_{k\ge 0}$. Acyclicity of $\{(E_k,f_k)\}_{k\ge 0}$ is therefore equivalent to $\sigma^{-1}$ being continuous.

By [Vogt-1, Cor. 1.3], which rests on Grothendieck's Factorization Theorem (Lemma C.1.5.4) and the Open Mapping Theorem for LF-spaces (Theorem C.1.5.5), Definition C.1.5.8 with Fréchet $E_k$'s depends only on the Hausdorff inductive limit LF-space $E=\varinjlim E_k$: it is independent of the chosen defining sequence of Fréchet spaces with Hausdorff inductive limit $E$. Moreover, as a special case of [Vogt-1, Thm. 2.10], a *strict* LF-space is always acyclic.$^5$

The acyclicity of all strict LF-spaces leads to a useful sufficient condition stated in Theorem C.1.5.11 below to recognize limit subspaces within strict locally convex countable inductive limits of *nuclear* Fréchet spaces. Before we state the condition, we introduce some general concepts:

Definition C.1.5.9. For a continuous linear map $f:E\to F$ between Hausdorff locally convex topological $\mathbf C$-vector spaces, we say a bounded subset $B\subset F$ can be *$f$-lifted* if and only if there exists a bounded subset $B'\subset E$ such that $B\subset f(B')$ (it is clearly equivalent to require $f(B')=B$). If this condition holds for all bounded subsets in $F$ then we say $f$ *lifts bounded subsets* or satisfies the *bounded lifting property*.

A class of locally convex spaces $E$ for which the bounded lifting property is satisfied by every quotient map $q:E\to E/F$ modulo a closed subspace was identified by Grothendieck in [Gro-e, II.4, Thm. 12, p. 119]: the Fréchet spaces $E$ that are also *Schwartz*, a concept introduced in [Gro-e, II.4, Def. 5, p. 117]. (The result is more precise: every bounded subset of $E/F$ is contained in $q(C)$ for a compact subset $C\subset E$.)

One of the equivalent definitions of being Schwartz (for a locally convex topological vector space $E$) is that for every closed convex circled $0$-neighborhood $U\subset E$ there exists a $0$-neighborhood $V\subset E$ with pre-compact

---

$^2$should say more: what *exactly* is $F'$? Calling it simply "a Köthe sequence space" is not helpful to a reader.

$^3$What are these? Does $F'=\prod_{n\ge 1}F'_n$ for some closed $F'_n\subset\ell^q(\mathbf N)$ and $F=\oplus F_n$ for $F_n=(F'_n)^{\perp}\subset\ell^p(\mathbf N)$? And is this just saying the subspace topology on $F\subset E$ is not the locally convex direct sum topology that is LF?

$^4$Give reference for why $F$ as subspace is not LF.

$^5$The array of references originally given was incomprehensible; e.g., [Vogt-1, Lemma 2.4, p. 163]. Admittedly the reference now given is no better if one looks under the hood.

## PDF page 668

**668** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

image in the normed space $E_U$ (the maximal Hausdorff quotient of $E$ defined by the semi-norm associated to the gauge $p_U:E\to\mathbf R_{\ge 0}$ of $U$); i.e., the image of $V$ in the Banach space completion $\widehat{E_U}$ has compact closure. For our purposes, nuclear spaces are the key source of locally convex spaces that are Schwartz:

Example C.1.5.10. If a locally convex topological vector space $E$ is a nuclear then we claim it is Schwartz. By [Scha, Ch. III, 7.2], for every convex circled $0$-neighborhood $U\subset E$ (in particular, such $U$ that are closed) there exists a convex circled $0$-neighborhood $V\subset U$ such that the natural map of Banach spaces $T:\widehat{E_V}\to\widehat{E_U}$ is nuclear. But any nuclear map between Banach spaces is a norm-topology limit of finite-rank operators [Scha, p. 98] and hence is compact. Since $V$ maps into the closed unit ball of $\widehat{E_V}$, its image under $T$ has compact closure. Taking $U$ to be closed, such $V$ fulfills the requirement in the definition of $E$ to be Schwartz.

The examples of the bounded lifting property that arise throughout this work are quotient maps $q:E\twoheadrightarrow G$ where $G$ is Hausdorff and $E$ is a strict countable inductive limit of nuclear Fréchet spaces (it is not apparent yet that all such $q$ satisfy the bounded lifting property since such an $E$ is generally not Fréchet, but in Corollary C.1.5.13 we will see that they all do). Note that any such $E$ is nuclear, hence Schwartz, and $G=E/F$ for the subspace $F=\ker(q)\subset E$ that is closed since $G$ is Hausdorff. Such quotients arise in the following result.

Theorem C.1.5.11 (Recognizing limit subspaces of strict LF-spaces). *Let $E$ be a strict countable inductive limit of nuclear Fréchet spaces. For any closed subspace $F\subset E$, the following are equivalent:*

*(1) $F$ is a limit subspace; i.e., for $\{E_m\}_{m\ge 0}$ a strict defining increasing sequence of nuclear Fréchet spaces, the subspace topology on $F$ equals the locally convex inductive limit topology of the inductive system $\{F\cap E_m\}_{m\ge 0}$ where each $F\cap E_m$ is given the subspace topology from $E_m$;*

*(2) the quotient map $q:E\to E/F$ satisfies the bounded lifting property; i.e., for every bounded subset $B\subset E/F$, there exists a bounded subset $B'\subset E$ such that $B\subset q(B')$.*

The result is actually true more broadly, when $F$ is merely assumed to be *step-wise closed*: $F\cap E_m$ is closed in $E_m$ for every integer $m\ge 0$. This is wider generality because there are examples of non-closed linear subspaces of strict LF-spaces that are step-wise closed: the discussion at the end of [Gro-e, §II.3, p. 98] gives a strict LF-space $E$ and a non-closed subspace $F\subset E$ such that the intersection of $F$ with each Fréchet subspace $E_0\subset E$ is closed in $E_0$. The equivalence in Theorem C.1.5.11 with $F$ merely assumed to be step-wise closed is [Wngr-2, §3, Cor. 3.4, p. 254], where each Fréchet $E_m$ is assumed merely to be Schwartz (which implies nuclearity by Example C.1.5.10).

Remark C.1.5.12. If $E$ is a strict countable inductive limit of nuclear Fréchet spaces $E_m$ as in Theorem C.1.5.11(1) then *every* strict defining sequence $\{E'_m\}$ for $E$ has all terms $E'_m$ nuclear since (i) each $E'_m\to E$ is a topological embedding by strictness, (ii) nuclearity is inherited by both strict countable inductive limits (so $E$ is nuclear) and subspaces (such as $E'_m\subset E$) by [Scha, Ch. III, 7.4].

Corollary C.1.5.13. *Let $E$ be a strict countable inductive limit of nuclear Fréchet spaces, and $F\subset E$ a closed subspace. Assume $E/F$ (with the quotient topology) is also a strict countable inductive limit of a countable sequence of nuclear Fréchet spaces.*

*The quotient map $q:E\to E/F$ lifts bounded subsets, so the closed subspace $\ker(q)\subset E$ is a limit subspace and hence $\ker(q)$ is a strict countable inductive limit of nuclear Fréchet spaces.*

The proof of [FlM, §5.5, Corollary, p. 110] inspires the argument given below.

Proof. Once it is shown that $q$ satisfies the bounded lifting property, the rest follows from Theorem C.1.5.11. By hypothesis, the Hausdorff quotient $E/F$ is the locally convex inductive limit of an increasing sequence of nuclear Fréchet subspaces $\{Q_m\}_{m\ge 0}$, and $E$ is the locally convex inductive limit of an increasing sequence of nuclear Fréchet spaces $\{E_m\}_{m\ge 0}$. Define $P_m:=E_m/(\ker(q)\cap E_m)$ equipped with the quotient topology inherited from $E_m$.

## PDF page 669

**C.1. LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES** · **669**

We do not (yet) know if the continuous linear injections $P_m\to P_{m+1}$ are topological embeddings, and in the absence of such strictness for $\{P_m\}$ we don't (yet) know the locally convex topological vector space $P:=\varinjlim P_m$ is Hausdorff (a property that is required in the definition of "LF-space"). But we can directly verify the Hausdorff property: the natural linear bijection $f:P\to E/F$ is continuous and has Hausdorff target, so $f^{-1}(0)=\{0\}$ is closed in $P$, ensuring the topological group $P$ is Hausdorff. Thus, $P$ is an LF-space, so the Open Mapping Theorem for LF-spaces (namely Theorem C.1.5.5) can be applied to conclude that $f$ is a topological isomorphism. Hence, for each $k\ge 0$ we can apply Grothendieck's Factorization Theorem (namely Lemma C.1.5.4) to $Q_k\hookrightarrow E/F\simeq P$ to conclude that it factors continuously through $P_{m(k)}\to P\simeq E/F$ for some $m(k)\ge 0$.

Let $B\subset E/F$ be a bounded subset. Since $E/F$ is the strict inductive limit of the complete $Q_k$'s (with each topological embedding $Q_k\to Q_{k+1}$ closed due to completeness of the Fréchet spaces $Q_k$), for sufficiently large $k$ we have $B\subset Q_k$ with $B$ is bounded in $Q_k$ [Scha, Ch. II, 6.5]. The image of $B$ under the continuous $Q_k\to P_{m(k)}$ (which we also denote as $B$) is therefore bounded in $P_{m(k)}$. Since nuclear spaces are Schwartz (Example C.1.5.10), such as the Fréchet $E_m$'s, by [Gro-e, II.4, Thm. 12, p. 119] for any closed subspace $M\subset E_{m(k)}$ the quotient map $E_{m(k)}\to E_{m(k)}/M$ lifts bounded subsets. Applying this to $M=\ker(q)\cap E_{m(k)}=F\cap E_{m(k)}$ (closed in $E_{m(k)}$ since $F\to E$ is a closed embedding and each $E_m\to E$ is a topological embedding by strictness of $\{E_m\}$), there exists a bounded subset $B'\subset E_{m(k)}$ whose image in $E_{m(k)}/M=P_{m(k)}$ contains $B$. The image of $B'$ under the continuous map $E_{m(k)}\to E$ is bounded, and that bounded subset of $E$ clearly has image in $E/F$ containing the bounded $B\subset E/F$, so we are done. $\square$

**C.1.6. Duality and inductive limits.** We record here for later use throughout this work a basic fact concerning the topological dual of certain inductive limits:

Lemma C.1.6.1 (Topological duals of inductive limits). *Let $\{j_{m,m'}:E_m\to E_{m'}\}$ be a countable inductive system of Hausdorff locally convex topological $\mathbf C$-vector spaces, with locally convex inductive limit $E$ and each $j_{m,m'}$ injective. Assume $E$ is Hausdorff (as is automatic when the given inductive system is strict; i.e., the maps $j_{m,m'}$ are topological embeddings).*

*(1) The natural linear map $q:E'\to\varprojlim_{m\ge 0}(E_m)'$ is a linear topological isomorphism with respect to the weak topology $\sigma(E',E)$ on the source, and the projective limit topology of the weak topologies $\sigma(E'_m,E_m)$ on the target.*

*(2) If for every bounded subset $B\subset E$ there exists an integer $m\ge 0$ such that $B\subset E_m$ inside $E$ and $B$ is bounded inside $E_m$ (so the same then holds for all $m'\ge m$) then $q$ in (1) is a linear topological isomorphism when using the strong dual topologies.*

The hypothesis in (2) holds whenever $\{E_m\}$ is strict with each $E_m\to E_{m+1}$ a closed embedding (such as happens when each $E_m$ is complete), by [Scha, Ch. II, 6.5]. By definition, the strong topology $\beta(F',F)$ on the topological dual $F'$ of a Hausdorff locally convex topological vector space is uniform convergence on bounded subsets of $F$.

Proof. (1) : The bijectivity of $q$ is immediate from the universal mapping property of locally convex inductive limits, and $q$ is continuous by the universal property of locally convex projective limits and the functoriality of $\sigma(F',F)$ in Hausdorff locally convex topological vector spaces $F$. To show $q$ is a homeomorphism, by the Hausdorff condition on source and target it suffices to show that $q$ identifies convergent nets on both sides (a subset $U$ of a Hausdorff topological space $T$ is open if and only if for every convergent net $\{t_i\}$ in $T$ with limit in $U$ there exists $i_0$ such that $t_i\in U$ for all $i\ge i_0$).

More specifically, if $\{\ell_i\}$ is a net in $E'$ whose image under $q$ converges for the projective limit of weak topologies on the duals $E'_m$ then we want to show $\{\ell_i\}$ converges in $E'$ with respect to $\sigma(E',E)$. Letting $\ell\in E'$ correspond to that limit, we can pass to $\ell_i-\ell$ so that $\ell_i|_{E_m}\to 0$ weakly in $E'_m$ for all $m$ and we want

## PDF page 670

**670** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

to conclude that $\ell_i\to 0$ weakly in $E'$. In other words, for each $x\in E$ we want $\ell_i(x)\to 0$. But $x\in E_{m_0}$ for some $m_0$, so since $\ell_i|_{E_{m_0}}\to 0$ we are done.

(2) : Functoriality of the strong topology ensures that the linear bijection $q:E'_{\beta}\to\varprojlim (E'_m)_{\beta}$ is continuous. Exactly as we handled the weak topology in the proof of (1) using that each point in $E$ occurs inside some $E_m$, the hypothesis that every bounded subset of $E$ arises from a bounded subset of some $E_m$ allows us to use the same argument as in (1) to conclude (the role of the choice of $x\in E$ is replaced by the choice of a bounded subset $B\subset E$). $\square$

Remark C.1.6.2. If in Lemma C.1.6.1(2) the inductive system were to satisfy the weaker condition that each bounded subset $B\subset E$ is contained in the closure of a bounded subset of some $E_m$ then the conclusion still holds (the same proof goes through), and conversely the conclusion implies that this weaker condition on bounded subsets of $E$ must hold: see [BKMcK, §2, Theorem, p. 190].

**C.2. Complements on mapping spaces, topological tensor products, and nuclearity**

Topological tensor products and topologized spaces of continuous linear maps are used to build many constructions of interest, so we discuss many results and concepts related to such ideas in this section for use in the main text.

**C.2.1. Mapping spaces.** We fix topological $\mathbf C$-vector spaces $E$ and $F$. For any set $X$, we denote by $F^X$ the set-theoretic product

$$
F^X:=\prod_{u\in X}F=\mathrm{Map}(X,F)
$$

where $\mathrm{Map}(X,F)$ denotes the set of all set-functions $X\to F$. We will ultimately be most interested in the subset of $F^E$ consisting of continuous linear mappings $E\to F$, but the generality of $F^X$ is convenient at the outset.

As in [Scha, Ch. III, §3] we denote by $\mathfrak S$ a collection of subsets of $E$ that is cofiltered under upwards inclusion. For any $T\in\mathfrak S$ and subset $V\subset F$, define

$$
U(T,V):=\{f\in F^E:f(T)\subset V\}. \tag{C.2.1.1}
$$

As explained in [Scha, Ch.III, §3, p. 79,(\*)], if $\mathfrak B$ is neighborhood base at $0$ for $F$ then the collection

$$
\mathcal U(\mathfrak S,\mathfrak B):=\{U(T,V)\}_{(T,V)\in\mathfrak S\times\mathfrak B} \tag{C.2.1.2}
$$

is a neighborhood base at $0$ for a unique topology on $F^E$ that moreover makes translation by each element of $F$ is continuous, and this topology is independent of the choice of $\mathfrak B$. This is called the $\mathfrak S$-*topology* on $F^E$, or the *topology of uniform convergence on members of* $\mathfrak S$.

The $\mathfrak S$-topology on $F^E$ is clearly unaffected by passage to a co-final subcollection within $\mathfrak S$. By [Scha, Ch.III, 3.1], the $\mathfrak S$-*topology* on $F^E$ promotes a vector subspace $L\subset F^E$ to a topological vector space if and only if the image $f(T)\subset F$ is bounded for every $f\in L$ and every $T\in\mathfrak S$. The following result is [Scha, Ch.III, 3.2], recalling that “locally convex topological vector space” in [Scha] is always assumed to be Hausdorff by definition (see [Scha, Ch.II, §4].

Lemma C.2.1.1. *Let $F$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $X$ a topological space, and $\mathfrak S$ a cofiltered family of subsets of $X$ whose union is dense in $X$. If a linear subspace $L\subset F^X$ satisfies*

*(1) every $f\in L$ is continuous as a function $f:X\to F$,*

*(2) for every $T\in\mathfrak S$, $f(T)$ is bounded in $F$ (equivalently, $L$ is a topological vector space for the natural $F$-invariant topology on $F^X$)*

*then $L$ is a Hausdorff locally convex topological $\mathbf C$-vector space.*

The following special case is [Scha, Ch.III, Cor. to 3.2].

## PDF page 671

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **671**

Lemma C.2.1.2. *Let $E$ and $F$ be Hausdorff topological $\mathbf C$-vector spaces with $F$ locally convex, and let $\mathfrak S$ a family of bounded subsets of $E$ whose union linearly generates a dense subspace of $E$. The $\mathfrak S$-topology on the $\mathbf C$-vector space $\mathscr L(E,F)$ of continuous linear maps from $E$ to $F$ is a Hausdorff locally convex $\mathbf C$-vector space.*

We denote by

$$
\mathscr L_{\mathfrak S}(E,F) \tag{C.2.1.3}
$$

the $\mathbf C$-linear space $\mathscr L(E,F)$ topologized with the $\mathfrak S$-topology. Its local convexity is made explicit as follows: if $\{\nu_i\}_{i\in I}$ is a family of seminorms generating the Hausdorff locally convex topology on $F$ then the family of seminorms on $\mathscr L(E,F)$ defined by

$$
q_{T,i}(f):=\sup_{x\in T}\nu_i(f(x)) \tag{C.2.1.4}
$$

for $(T,i)\in\mathfrak S\times I$ generates the $\mathfrak S$-topology on $\mathscr L(E,F)$: see [Scha, Ch.III, p. 81]. Note in particular that (in contrast with the theory of Banach spaces) there is no *preferred topology* on $\mathscr L(E,F)$, not even when $F=\mathbf C$.

Example C.2.1.3. Topologies on continuous linear mapping spaces of the form discussed above are ubiquitous and underlie duality theory in locally convex topological $\mathbf C$-vector spaces.

Definition C.2.1.4. For a Hausdorff locally convex topological $\mathbf C$-vector space $E$, the space $\mathscr L(E,\mathbf C)$ endowed with the $\mathfrak S$-topology for a cofiltered collection $\mathfrak S$ of bounded subsets of $E$ linearly generating a dense subspace of $E$ is denoted $E'_{\mathfrak S}$ and is often called the $\mathfrak S$-*dual* of $E$. For instance:

- If $\mathfrak S$ is the collection of all finite subsets of $E$ then $E'_{\mathfrak S}$ is the dual space $E'$ equipped with the weak topology $\sigma(E',E)$ and is denoted $E'_{\sigma}$; this is called the *weak dual* of $E$.
- If $\mathfrak S$ is the collection of all pre-compact subsets of $E$ (those with compact closure in $\widehat{E}$) then $E'_{\mathfrak S}$ is denoted $E'_{\gamma}$.
- $\mathfrak S$ is the collection of all bounded subsets of $E$ then $E'_{\mathfrak S}$ is denoted $E'_{\beta}$, called the *strong dual* of $E$.

Strong duals are ubiquitous in the theory of distributions.

A very useful fact is that the weak closure and the topological closure of any convex subset of $E$ coincide [Scha, Ch. IV, 3.1] More generally, we record below some terminology and notation.

Definition C.2.1.5. Let $E,F$ be Hausdorff locally convex topological $\mathbf C$-vector spaces, and $\mathfrak S$ a family of bounded subsets of $E$ whose union linearly generates a dense subset of $E$. We denote by $\mathscr L_{\mathfrak S}(E,F)$ the $\mathbf C$-vector space $\mathscr L(E,F)$ of continuous linear maps equipped with the $\mathfrak S$-topology. As special cases:

(1) $\mathscr L_{\sigma}(E,F)$ if $\mathfrak S$ is the collection of all finite subsets of $E$. The $\mathfrak S$-topology on $\mathscr L_{\sigma}(E,F)$ is called the topology of *simple* (or *pointwise*) *convergence.*

(2) $\mathscr L_{\gamma}(E,F)$ if $\mathfrak S$ is the collection of all pre-compact subsets of $E$. The $\mathfrak S$-topology on $\mathscr L_{\gamma}(E,F)$ is called the topology of *pre-compact convergence.*

(3) $\mathscr L_{\beta}(E,F)$ if $\mathfrak S$ is the collection of all bounded subsets of $E$. The $\mathfrak S$-topology on $\mathscr L_{\beta}(E,F)$ is called the topology of *bounded convergence.*

Case (2) is relevant to traces for nuclear operators between Hausdorff locally convex spaces, as discussed in §C.2.4.5.

Remark C.2.1.6. If $E$ and $F$ are normed spaces then the norm

$$
\|f\|:=\sup_{\|u\|_E\le 1}\|f(u)\|_F<\infty
$$

generates the topology of bounded convergence on $\mathscr L_{\beta}(E,F)$. When $\mathfrak S$ is chosen to be the collection of all finite subsets of $E$ then the $\mathfrak S$-topology of pointwise convergence on $\mathscr L(E,F)$ is the locally convex topology

## PDF page 672

**672** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

generated by the subfamily of the seminorms from (C.2.1.4) given by $q_{\{u\},i}$ for $u\in E$ and $\{\nu_i\}_{i\in I}$ a family of seminorms generating the locally convex topology on $F$. If $E=F$ is a Hilbert space then this is called the *strong operator topology* on $\mathscr B(E)$. In other words,

$$
\mathscr L_{\sigma}(E):=\mathscr L_{\sigma}(E,E)=\mathscr B_{\mathrm{SOT}}(E)
$$

when $E$ is a Hilbert space.

An important property of $\mathfrak S$-topologies is that a subset of $\mathscr L(E,F)$ that is bounded with respect to the topology of pointwise convergence is bounded with respect to any $\mathfrak S$-topology on $\mathscr L(E,F)$ so long as $E$ is quasi-complete and $\mathfrak S$ is a cofiltered collection of bounded subsets of $E$ whose union is $E$ (i.e. not merely linearly generating a dense subspace): see [Scha, Ch.III, Cor. to 3.4]. The following result (see [Scha, Ch.III, Cor. to 4.4]) is important for later use.$^6$

Lemma C.2.1.7 (Quasi-completeness of mapping spaces). *Let $E,F$ be Hausdorff locally convex topological $\mathbf C$-vector spaces. Assume:*

*(1) $E$ is barreled.*

*(2) $F$ is quasi-complete.*

*(3) $\mathfrak S$ is a cofiltered collection of bounded subsets of $E$ whose union is $E$.*

*Then $\mathscr L_{\mathfrak S}(E,F)$ is quasi-complete.*

Remark C.2.1.8. If $E=F=H$ is a Hilbert space and $\mathfrak S$ is the collection of all finite subsets of $H$ respectively the collection of all bounded subsets of $H$ then Lemma C.2.1.7 implies quasi-completeness of $\mathscr B_{\mathrm{SOT}}(H)$ respectively $\mathscr B_{\mathrm{NT}}(H)$ (operator-norm topology). Indeed, every Hilbert space (and even every Fréchet space) is barrelled [Scha, Ch.II, Cor. to 7.1]) and complete. Of course, as is well-known, $\mathscr B_{\mathrm{NT}}(H)$ is even complete.

Let $E,F$ be two Hausdorff locally convex topological $\mathbf C$-vector spaces. On $\mathscr L(E,F)$, the topology of uniform convergence on the bounded subsets of $E$ will be of particular importance, because it is a flexible topology to define distributions. Specifically, $E$ will be chosen to be a “familiar” locally convex topological linear space (of functions), and $F$ will be chosen to be an operator algebra with topologies of varying degrees of strength; $\mathscr L_{\beta}(E,F)$ will be a space of “$F$-valued distributions”.

In order to study continuous linear mapping spaces topologized with a suitable $\mathfrak S$-topology, we need two topologies on tensor products of Hausdorff locally convex topological $\mathbf C$-vector spaces. In order to discuss the first, we now recall some terminology on equicontinuity. A subset $H\subset\mathscr L(E,F)$ is called *equicontinuous* if and only if for every 0-neighborhood $V\subset F$ there exists a 0-neighborhood $U\subset E$ such that $f(U)\subset V$ for every $f\in H$. We refer the reader to [Scha, Ch. III, §4] for more on equicontinuity and the Uniform Boundedness Principle. Important properties of equicontinuous subsets in $\mathscr L(E,F)$ are the following (see [Scha, Ch. III, Cor. to 4.1, 4.5]):

Lemma C.2.1.9. *Let $E,F$ be Hausdorff locally convex topological $\mathbf C$-vector spaces, $H\subset\mathscr L(E,F)$ an equicontinuous subset.*

*(1) $H$ is bounded in $\mathscr L_{\mathfrak S}(E,F)$ for $\mathfrak S$ any collection of bounded subsets of $E$ whose union linearly generates a dense subspace of $E$.*

*(2) The subspace topologies on $H$ inherited from either $\mathscr L_{\sigma}(E,F)$ or $\mathscr L_{\gamma}(E,F)$ are the same.*

---

$^6$Give some brief indications of where or how it is “important”: for some Pettis integration or some weak-compactness result or what?

## PDF page 673

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **673**

**C.2.2. Topologies of a duality and the equicontinuous compactology.** We will say a few words on bornologies and on topologies associated to certain bilinear pairings (in effect, convergence conditions via linear functionals), explaining the role that the main results on them serve throughout our work.

C.2.2.1. *Generation of polar topologies: bornologies and topologies of a duality.* Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. A *bornology* on $E$ is a non-empty collection of subsets of $E$, cofiltered by upward-inclusion, such that each of its members is bounded with respect to the $\sigma(E,E')$-topology. Note that boundedness in the given topology on $E$ and in the $\sigma(E,E')$-topology are the same [Scha, Ch. IV, 3.3]. The defining condition of a bornology on $E$ is that for each $B\in\mathfrak S$ and $\lambda\in\mathbf C^{\times}$ there exists $C\in\mathfrak S$ such that $\lambda B\subset C$. All the $\mathfrak S$-topologies defined in Definition C.2.1.5 are induced by bornologies.

As in [Scha, Ch. IV, §1], we now consider a bi-linear pairing

$$
\langle\cdot,\cdot\rangle:E\times F\to\mathbf C \tag{C.2.2.1}
$$

with $E,F$ two Hausdorff locally convex topological $\mathbf C$-vector spaces. We assume that the pairing $\langle\cdot,\cdot\rangle$ is *separating*: if $x\in E$ and $\langle x,\cdot\rangle=0$ as a linear functional on $F$ then $x=0$, and similarly for $\langle\cdot,y\rangle$ as a linear functional on $E$. The notation $\langle E,F\rangle$ refers to the datum $(E,F,\langle\cdot,\cdot\rangle)$.

The datum of a separating bi-linear pairing $g:E\times F\to\mathbf C$ leads to the definition of the weak topology $\sigma(E,F)$ on $E$ and the weak topology $\sigma(F,E)$ on $F$, respectively defined as the topology of pointwise convergence with respect to the family of linear maps $\{g(\cdot,y):y\in F\}$ on $E$ and $\{g(x,\cdot):x\in E\}$ on $F$ respectively. This leads to the concepts of weak boundedness and weak compactness in $E,F$, which underlie other topologies associated to $\langle E,F\rangle$ via the following construction.

For $A\subset F$ a subset, we define its *polar set* in $E$ with respect to the duality $\langle E,F\rangle$ to be

$$
A^{\circ}:=\{x\in E:|\langle x,y\rangle_{E,F}|\le 1,\text{ for all }y\in A\}\subset E \tag{C.2.2.2}
$$

(this is called the *absolute polar* of $A$ in [Scha, Ch. IV, p. 125], where *polar* is defined using $\mathrm{Re}(\langle x,y\rangle)$ as is also done in [Bou-TVS, Ch. II, §8, No. 4, Def. 1, p. II.64]; the two concepts agree when $A$ is circled), and similarly for any subset $A\subset E$ we define its *polar set* in $F$ with respect to the duality $\langle E,F\rangle$ to be

$$
A^{\circ}:=\{y\in F:|\langle x,y\rangle_{E,F}|\le 1,\text{ for all }x\in A\}\subset F. \tag{C.2.2.3}
$$

Polars provide a general recipe to produce 0-neighborhoods in either one of the two linear spaces $E,F$ in a duality $\langle E,F\rangle$. Note that if $V\subset E$ a vector subspace, the subset $V^{\circ}\subset F$ is the orthogonal (annihilator) $V^{\perp}=\mathrm{ann}_F(V)$. The reader may want to compare the construction and use of polars with that of orthogonals/annihilators from the structure theory of Hausdorff locally compact abelian groups, which is used in Appendix D to construct and study Schwartz-Bruhat spaces of functions on Hausdorff locally compact abelian groups. When taking $F$ to be the algebraic dual $E^*$ of $E$ we denote by $A^{\bullet}$ the polar sets in either direction with respect to the pairing $\langle\cdot,\cdot\rangle_{E,E^*}$.

We can use polars in $E^*$ of 0-neighborhoods of $E$ to identify the continuous dual of $E$ within $E^*$:

$$
E'=\bigcup_{U\in\mathcal U_0(E)}U^{\bullet}\subset E^* \tag{C.2.2.4}
$$

where $\mathcal U_0(E)$ is a 0-neighborhood base in $E$. The meaning of (C.2.2.4) is that a linear functional on $E$ is continuous if and only if it is bounded on a 0-neighborhood in $E$.

The datum of a duality $\langle E,F\rangle$ leads to an axiomatization of the robust theory of Banach spaces and their duals, with generalization of the main concepts (such as reflexivity) to the case of general Hausdorff locally convex topological $\mathbf C$-vector spaces. A key basic result is:

Theorem C.2.2.1 (Bi-polar Theorem). *Let $\langle E,F\rangle$ be a duality. Let $A\subset E$ be a subset. Then:*

$$
(A^{\circ})^{\circ}=\overline{\mathrm{cch}}(A\cup\{0\}) \tag{C.2.2.5}
$$

## PDF page 674

**674** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

*where the right side of (C.2.2.5) is the $\sigma(E,F)$-closure of the convex circled hull of $A$ in $E$.*

Our convention has been to define *polar* of $A\subset E$ to be $\{y\in F:|\langle x,y\rangle|\le 1\text{ for all }x\in A\}$ which some references call the *absolute polar*, in contrast with *real polar* $\{y\in F:\mathrm{Re}|\langle x,y\rangle\le 1\text{ for all }x\in A\}$. Since the absolute polar $A^{\circ}$ agrees with the real polar of the circled $A_b=D\cdot A$ for $D\subset\mathbf C$ the closed unit disk, Theorem C.2.2.1 for real polars as in [Scha, Ch. IV, 1.5] yields the result for absolute polars as stated above.

An efficient account of the basic properties of polars is given in [Scha, Ch. IV, §1] and [NB, Thms. 8.3.6, 8.3.7]. From the definition one sees that the polar set $A^{\circ}\subset F$ of a subset $A\subset E$ is always convex, circled and $\sigma(F,E)$-closed, and is absorbing (i.e. radial) if and only if $A$ is $\sigma(E,F)$-bounded. This paves the way to defining 0-neighborhood bases within $E$ respectively $F$ via polars of subsets of $F$ respectively $E$, and then using the Bi-polar Theorem as a dictionary to establish basic properties of such “polar” topologies.

To a directed collection of $\sigma(F,E)$-bounded subsets of $F$, we assign the corresponding collection of polars in $E$. The idea is to think of a $\sigma(F,E)$-bounded subset $B\subset F$ as a replacement for the unit ball in the normed dual of a normed space, and define the function:

$$
p_B(x):=\sup_{y\in B}|\langle x,y\rangle_{E,F}|
$$

a seminorm on $E$. The “unit ball” with respect to $p_B$ is exactly the polar set $U:=B^{\circ}$, and so long as the chosen class of $\sigma(F,E)$-bounded subsets of $F$ satisfies basic stability properties, this construction leads to a 0-neighborhood base of a linear topology on $E$, with the polar sets $B^{\circ}$ playing the role of unit-balls. Polar topologies are therefore defined by using *polarity* to indicate which subsets are supposed to serve as unit-balls. This is the origin of the concept of bornology, whose definition we recalled at the beginning of this subsection.

C.2.2.2. *Consistent topologies.* We conclude this account of the main elements of the construction of polar topologies by highlighting a great advantage of the local convexity assumption on linear topologies of topological vector spaces. It affords flexibility on the concepts of boundedness, closure, and denseness in terms of refining the polar topology on $E$ induced by a duality $\langle E,F\rangle$.

Specifically, certain properties of subsets of $E$ defined in terms of a polar topology using $F$ are independent of the choice of such topology so long as the polar topology is *consistent* with $\langle E,F\rangle$ in the sense that the space of continuous linear functionals on $E$ with respect to that topology is exactly $F$. For example, the weak topology $\sigma(E,F)$ on $E$ is always consistent with a given separating duality $g:E\times F\to\mathbf C$ (as is a given Hausdorff locally convex topology on $E$ when $F=E'$ is the topological dual and $g$ is the evaluation pairing).

A first important example of this phenomenon is the equivalence of boundedness and weak boundedness, as well as formation of closure, respectively weakly closure for convex sets in any Hausdorff locally convex topological $\mathbf C$-vector space: see [Scha, Ch. IV, 3.1, 3.3].

Although consistency is defined on all linear topologies on $E$, for Hausdorff locally convex topologies the extremes of such consistent topologies are known. This is the content of the Mackey-Arens Theorem [Scha, Ch. IV, 3.2-3.3]. It rests crucially on the local convexity assumption and ultimately on separations theorems [Scha, Ch. II, §9] relying upon the Hahn-Banach Theorem. The statement of the result is that such topologies are precisely those which are finer than $\sigma(E,F)$ and coarser than the *Mackey topology* $\tau(E,F)$ that is the $\mathfrak S$-topology on $E$ for the collection $\mathfrak S$ of all subsets of $F$ that are convex, circled and $\sigma(F,E)$-compact. (In [Jar], this topology is denoted using the letter $\mu$ rather than $\tau$.)

In the absence of local convexity, control on polar topologies is lost: we refer the reader to the example of $\ell^p(\mathbf N)$ for $0<p<1$ (see [Voigt, Ch. 5, Ex. 5.5(a), p. 38]). Most notable among the polar topologies that are not necessarily consistent is the strong topology $\beta(E,F)$ that is always stronger than the Mackey topology. By [Scha, Ch. IV, 5.2], the condition under which the strong-dual topology $\beta(E',E)$ agrees with the Mackey topology $\tau(E',E)$ is barreledness of $E$ [Scha, Ch. II, §7]: this means that the barrels of $E$ (closed, convex, circled and absorbing subsets, examples of which are provided by the polars of weakly bounded subsets) are

## PDF page 675

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **675**

0-neighborhoods in $E$. Under such an additional condition, a tighter relation between equicontinuous and bounded subsets is attained in the form of a general version of the Uniform Boundedness Principle (see [Scha, Ch. III, 4.2-4.3]).

Further classes of Hausdorff locally convex topological $\mathbf C$-vector spaces will be discussed as the need arises.

C.2.2.3. *Uniform convergence on the weakly closed convex and circled equicontinuous subsets of $E'$.* With an eye towards the discussion of $\varepsilon$-tensor products, and the proofs of several “kernel theorems” in Appendix D, we record the following result for which we refer the reader to [Scha, Ch. IV, Cor. 3 to 1.5] for a proof.

Lemma C.2.2.2 (Topology of uniform convergence on the equicontinuous subsets of $E'$). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, and $\mathcal E$ the collection of all equicontinuous subsets of $E'$ that are convex, circled, and closed with respect to the $\sigma(E',E)$-topology on $E'$. Then the family of subsets of $E$*

$$
\mathcal U:=\{U^{\circ}:U\in\mathcal E\} \tag{C.2.2.6}
$$

*(where $U^{\circ}$ is the polar of $U$ in $E$ with respect to the duality $\langle E,E'\rangle$) is a 0-neighborhood base for the given topology on $E$.*

The collection $\mathcal E$ from Lemma C.2.2.2 is usually referred to as the *equicontinuous compactology* on $E'$. The weak-closedness and convexity assumptions on $U$ considered in (C.2.2.6) are harmless because every subset $U\subset E$ satisfies $U^{\circ}=U^{\circ\circ\circ}$ by [Scha, Ch. IV, Cor. 1 to 1.5] with $U^{\circ\circ}$ weakly closed and convex as described by the Bi-Polar Theorem.

The collection $\mathcal E$ will underlie the definition of the injective tensor product topology $\otimes_{\varepsilon}$ in §C.2.3.1 but via Lemma C.2.2.2 it also leads to a tool underpinning proofs of “kernel theorems” in use throughout this work (these are results which say that certain function spaces on $X\times Y$ coincide with a suitably completed tensor product of corresponding function spaces on $X$ and on $Y$) and comparisons among multiple topologies on tensor products. In the presence of favorable conditions (such as nuclearity of at least one of the tensor factors) this includes criteria under which there is equality between the injective tensor product topology $\otimes_{\varepsilon}$ and the projective tensor product topology $\otimes_{\pi}$ (see §C.2.3.1 and §C.2.3.2). Such equality is a powerful feature because the injective topology is well-behaved for topological embeddings and the projective topology is well-behaved for quotient maps.

A prototypical such application occurs in the proof of the kernel theorem for the Schwartz space of Euclidean spaces: that the continuous linear map $\mathcal S(\mathbf R^n)\otimes_{\pi}\mathcal S(\mathbf R^m)\to\mathcal S(\mathbf R^n\times\mathbf R^m)$ extends to a linear topological isomorphism $\mathcal S(\mathbf R^n)\widehat{\otimes}_{\pi}\mathcal S(\mathbf R^m)\to\mathcal S(\mathbf R^n\times\mathbf R^m)$. Nuclearity of the Schwartz spaces identifies injective and projective topologies on the tensor product, and then Lemma C.2.2.2 is the additional ingredient used to show that a net in $\mathcal S(\mathbf R^n)\otimes_{\pi}\mathcal S(\mathbf R^m)$ converges in $\mathcal S(\mathbf R^n\times\mathbf R^m)$ only if it converges in $\mathcal S(\mathbf R^n)\otimes_{\pi}\mathcal S(\mathbf R^m)$.

Among the advantages of the local convexity condition (most of which rest on the separation theorems which constitute forms of the Hahn-Banach Theorem) is the stability of important concepts and properties of subsets of Hausdorff locally convex topological $\mathbf C$-vector spaces with respect to change of topology compatibly with a duality in the presence of local convexity (the bounds on such topologies being described by the Mackey-Arens Theorem). Another is the description of locally convex topologies by means of fundamental families of seminorms (see the discussion in §C.1.2), and the characterization of the given topology as the topology of uniform convergence on the closed convex circled equicontinuous subsets of the continuous dual.

**C.2.3. Topological tensor products.** Throughout this subsection, we provide an overview about three Hausdorff locally convex topologies on $E\otimes F$ for any two Hausdorff locally convex topological $\mathbf C$-vector spaces $E$ and $F$. These are the injective tensor product (also called the “$\varepsilon$-tensor product”), the projective tensor product (also called the “$\pi$-tensor product”), and the inductive tensor product. When $E\otimes F$ is equipped with such topologies, we denote the resulting locally convex topological vector space as $E\otimes_{\varepsilon}F$, $E\otimes_{\pi}F$, and

## PDF page 676

**676** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

$E\otimes_{\iota}F$ respectively. The corresponding completions are denoted $E\widehat{\otimes}_{\varepsilon}F$, $E\widehat{\otimes}_{\pi}F$, and $E\overline{\otimes}F$ respectively. The inductive tensor product is the least-encountered in the published literature, but it serves an important role in our work.

C.2.3.1. *Injective tensor products by bi-equicontinuous convergence.* We start with the $\varepsilon$-topology, also called the “injective tensor product” because it interacts well with subspace inclusions [Tre, Prop. 43.7] (as we shall discuss). For Hausdorff locally convex topological vector spaces $E_1$ and $E_2$, we write $B(E_1,E_2)$ for the space of continuous bilinear forms $E_1\times E_2\to\mathbf C$ and $\mathscr B(E_1,E_2)$ for the space of separately continuous bilinear forms $E_1\times E_2\to\mathbf C$ (i.e., continuous in each entry when the other is fixed). By [Tre, Prop. 42.4], the canonical linear map

$$
\rho:E\otimes F\to B(E'_{\sigma},F'_{\sigma}) \tag{C.2.3.1}
$$

uniquely determined on elementary tensors $x\otimes y$ by

$$
\rho(x\otimes y):(\varphi_E,\varphi_F)\mapsto\varphi_E(x)\varphi_F(y) \tag{C.2.3.2}
$$

is a linear isomorphism.

Let $E'=\mathscr L(E,\mathbf C)$ denote the topological dual of a Hausdorff locally convex topological vector space $E$, on which we have the Mackey topology $\tau=\tau(E',E)$ of uniform convergence on convex, circled, weakly-compact subsets of $E$.

Remark C.2.3.1. The Mackey topology on $E'$ can be described in another way in an important class of examples. If $E$ has the Heine-Borel property that all closed bounded subsets are compact (conversely, compact subsets in any Hausdorff topological vector space are always closed and bounded) then $E'_{\tau}$ clearly agrees with the topology $E'_{\gamma}$ of pre-compact convergence. The most interesting class of $E$ with the Heine-Borel property are Montel spaces [Scha, Ch. IV, p. 147], which (as is explained in Appendix D) includes many function spaces of interest to us, such as Schwartz spaces on the adelic ring and idele class group of a number field. All barreled quasi-complete nuclear spaces are Montel (by [Tre, Cor. 1 to Prop. 50.4] and [Scha, Ch. IV, 5.6]; nuclearity will be reviewed in §C.2.4).

For general Hausdorff locally convex topological $\mathbf C$-vector spaces $E,F$, we have a linear identification

$$
\mathscr L(E'_{\tau},F)=\mathscr B(E'_{\sigma},F'_{\sigma}) \tag{C.2.3.3}
$$

via the inverse operations

$$
f\mapsto((x',y')\mapsto y'(f(x'))),\quad B\mapsto(x'\mapsto B(x',\cdot)\in(F'_{\sigma})'=F)
$$

(that the second of these yields a continuous linear map $E'_{\tau}\to F$ is seen by considering the inclusion $E\otimes F\simeq B(E'_{\sigma},F'_{\sigma})\hookrightarrow\mathscr B(E'_{\sigma},F'_{\sigma})$). We endow the right side of (C.2.3.3) with the topology of uniform convergence on the products of equi-continuous subsets of $E'_{\sigma}$ and $F'_{\sigma}$, and [Tre, Prop. 42.2] directly describes the corresponding topology on the left side (which it also identifies with $\mathscr L(E'_{\sigma},F_{\sigma})$); this topological vector space is denoted $\mathscr L_{\varepsilon}(E'_{\tau},F)$. We call this topology on either side of (C.2.3.3) the topology of *bi-equicontinuous convergence*, and denote the space $\mathscr B(E'_{\sigma},F'_{\sigma})$ equipped with that topology as $\mathscr B_{\varepsilon}(E'_{\sigma},F'_{\sigma})$.

Following [Tre, Def. 43.1], we define

$$
E\otimes_{\varepsilon}F \tag{C.2.3.4}
$$

to be the $\mathbf C$-vector space $E\otimes F$ topologized with the subspace topology via $E\otimes F \overset{\rho}{\simeq} B(E'_{\sigma},F'_{\sigma})\subset\mathscr B_{\varepsilon}(E'_{\sigma},F'_{\sigma})$. The topological vector space $E\otimes_{\varepsilon}F$ is Hausdorff and locally convex by [Scha, Ch. III, Cor. to 3.2] applied to $\mathscr L_{\varepsilon}(E'_{\tau},F)$. We denote by $E\widehat{\otimes}_{\varepsilon}F$ the completion of $E\otimes_{\varepsilon}F$.

## PDF page 677

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **677**

Remark C.2.3.2. $^7$ An alternative but equivalent way to define the $\varepsilon$-topology is used in [Jar, §16.3, pp. 343-4], so we discuss that here since for some results$^8$ on the $\varepsilon$-topology we refer to proofs in [Jar]. Let $\mu$ be the topology on $E'$ given by uniform convergence on compact subsets of the completion $\widehat{E}$. If $E$ is complete then $\mu$ is the topology $\gamma$ of pre-compact convergence on $E'$. Thus, when $E$ is complete and metrizable then by the Banach-Dieudonné Theorem [Scha, Ch. IV, 16.3] the topology $\mu$ on $E'$ is the finest locally convex topology on $E'$ which agrees with $\sigma(E',E)$ on all equicontinuous subsets.

We endow the space of continuous linear maps $\mathscr L(E'_{\mu},F)$ with the $\mathcal E$-topology where $\mathcal E$ is the collection of equicontinuous subsets of $E'$ that are weakly-closed, convex and circled (the same $\mathcal E$ that features in Lemma C.2.2.2: the polar sets of whose members generate the initial topology on $E$). The canonical linear map

$$
\rho_0:E\otimes F\to\mathscr L_{\mathcal E}(E'_{\mu},F) \tag{C.2.3.5}
$$

uniquely determined on elementary tensors $x\otimes y$ by the assignment

$$
\rho_0(x\otimes y)(\varphi):=\langle x,\varphi\rangle_{E,E'}\cdot y \tag{C.2.3.6}
$$

is a linear injection and realizes $E\otimes F$ as the subspace of $\mathscr L(E'_{\mu},F)$ of all finite-rank operators that are continuous with respect to the $\mu$-topology on the source, and the $\sigma(F,F')$-topology on the target. This injection defines $E\otimes_{\varepsilon}F$ as the subspace topology in [Jar, 16.3].

Remark C.2.3.3 (On the equicontinuous weak-$*$ topology). The topology $\mu$ from Remark C.2.3.2 is referred to as the *equicontinuous weak-$*$ topology*, and it enables the general treatment of those Hausdorff locally convex topological $\mathbf C$-vector spaces $E$ whose weak dual $E'_{\sigma}$ has its closed subsets characterized exactly as for the convex subsets of the weak dual of a Fréchet space in the Krein-Smulian Theorem [Scha, Ch. IV, 6.4]), leading to the class of Ptak (or $B$-complete) spaces ([Scha, Ch, IV, §8], [Jar, §9.5]). There is an Open Mapping Theorem for $B$-complete spaces [Scha, Ch. IV, Cor. 1 to 8.3].

We now describe the Hausdorff locally convex topology on $E\otimes_{\varepsilon}F$ in a more direct way, using the interpretation of equicontinuous subsets of $E'$ in terms of polars $U^{\circ}$ for $U$ varying through a 0-neighborhood base in $E$ and similarly for $F'$ and $F$. Let $\mathcal U,\mathcal V$ be 0-neighborhood bases in $E,F$, respectively. We may and do assume the members of $\mathcal U$ and $\mathcal V$ are closed convex and circled. For any $U\in\mathcal U$, $V\in\mathcal V$, we use (C.2.3.1) to define the following family of seminorms on the algebraic tensor product $E\otimes F$:

$$
\varepsilon_{U,V}(f):=\sup\{|\rho(f)(\varphi,\psi)|:\varphi\in U^{\circ}\subset E',\psi\in V^{\circ}\subset F'\}<\infty \tag{C.2.3.7}
$$

(finite since $\rho(f)\in B(E'_{\sigma},F'_{\sigma})$ with $U^{\circ}$ and $V^{\circ}$ each weakly bounded by design). By the definition of the $\varepsilon$-topology, the collection $\{\varepsilon_{U,V}\}$ as $(U,V)$ varies over $\mathcal U\times\mathcal V$ is a family of seminorms on $E\otimes F$ generating the locally convex topology on $E\otimes_{\varepsilon}F$.

Example C.2.3.4. Assume $E$ and $F$ are normed spaces, with norms $\|\cdot\|_E$ and $\|\cdot\|_F$. The linear inclusion

$$
E\otimes F\simeq B(E'_{\sigma},F'_{\sigma})\subset\mathscr B(E'_{\sigma},F'_{\sigma})\simeq\mathscr L(E'_{\tau},F) \tag{C.2.3.8}
$$

is $x\otimes y\mapsto(\varphi\mapsto\varphi(x)y)$. For the closed unit balls $U=B_E$ and $V=B_F$, $\varepsilon_{U,V}$ is the norm induced on $E\otimes F$ under (C.2.3.8) by the operator norm on $\mathscr L(E'_{\tau},F)$ (it is finite on members of this space of linear mappings since the strong-dual topology is finer than the Mackey topology). This norm on $E\otimes F$ therefore defines the topology on $E\otimes_{\varepsilon}F$.

We now collect some properties of the injective tensor product for later use. By (C.2.3.7) (or [Tre, Prop. 43.6]), if $E_1,E_2$ and $F_1,F_2$ are pairs of Hausdorff locally convex topological $\mathbf C$-vector spaces and $T_1:E_1\to F_1$ and $T_2:E_2\to F_2$ are continuous linear maps, then linear map $T_1\otimes T_2$ is continuous with respect

---

$^7$This and the next Remark should ideally be removed, much too heavy on a reader. The purpose, if retained, must be much more clear.

$^8$Really so necessary?

## PDF page 678

**678** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

to the injective tensor product topology on source and target. We denote this continuous linear map whose underlying algebraic linear map is $T_1\otimes T_2$ by

$$
T_1\otimes_{\varepsilon}T_2, \tag{C.2.3.9}
$$

and denote by $T_1\widehat{\otimes}_{\varepsilon}T_2$ the unique continuous linear extension of $T_1\otimes_{\varepsilon}T_2$ to the completions:

$$
T_1\widehat{\otimes}_{\varepsilon}T_2:E_1\widehat{\otimes}_{\varepsilon}E_2\to F_1\widehat{\otimes}_{\varepsilon}F_2. \tag{C.2.3.10}
$$

Lemma C.2.3.5. *Let $E_1,E_2$ and $F_1,F_2$ be Hausdorff locally convex topological $\mathbf C$-vector spaces and let $T_1:E_1\to F_1$ and $T_2:E_2\to F_2$ be continuous linear maps.*

*(1) If $T_1$ and $T_2$ are topological embeddings then so are $T_1\otimes_{\varepsilon}T_2$ and $T_1\widehat{\otimes}_{\varepsilon}T_2$. In particular, if $E_1,E_2,F_1$ and $F_2$ are normed and $T_1,T_2$ are isometric embeddings then so are $T_1\otimes_{\varepsilon}T_2$ and $T_1\widehat{\otimes}_{\varepsilon}T_2$.*

*(2) If $T_1,T_2$ are topological embeddings with dense range then so is $T_1\otimes_{\varepsilon}T_2$. In particular, the canonical continuous linear map*

$$
E_1\widehat{\otimes}_{\varepsilon}E_2\to\widehat{E}_1\widehat{\otimes}_{\varepsilon}\widehat{E}_2 \tag{C.2.3.11}
$$

*is a topological linear isomorphism.*

*(3) The formation of injective tensor products is topologically associative.*

Proof. For (1) it suffices to treat the case of completed tensor products, which is [Tre, Prop. 43.7]. The assertion in (3) is seen via the seminorm description in (C.2.3.7).

For (2), first observe that by (1) and Hahn-Banach, it suffices to check that a continuous linear form $\varphi$ on $F_1\widehat{\otimes}_{\varepsilon}F_2$ that vanishes on $E_1\widehat{\otimes}_{\varepsilon}E_2$ must be $0$. By continuity of $\varphi$ and density of the image of any Hausdorff locally convex topological vector space in its completion, it suffices to prove the same on the uncompleted tensor product spaces. To carry out the latter, we note that for Hausdorff topological vector spaces $E$ and $F$, it is explained at the start of [Tre, Ch. 49] that $(E\otimes_{\varepsilon}F)'$ is naturally a linear subspace of the space $B(E,F)$ of continuous bilinear forms $E\times F\to\mathbf C$. We want to show that any continuous linear $\ell:F_1\otimes_{\varepsilon}F_2\to\mathbf C$ vanishing on $E_1\otimes E_2$ must be $0$, and the bilinear $B:F_1\times F_2\to\mathbf C$ corresponding to $\ell$ is continuous yet vanishes on $E_1\times E_2$, so clearly $B=0$. $\square$

Lemma C.2.3.6. *Let $I,J$ be sets, $E_i$ for $i\in I$, $F_j$ for $j\in J$, Hausdorff locally convex topological $\mathbf C$-vector spaces. Then*

*(1) If $I$ and $J$ are finite then the canonical continuous linear map*

$$
\left(\prod_{i\in I}E_i\right)\otimes_{\varepsilon}\left(\prod_{j\in J}F_j\right)\to\prod_{(i,j)\in I\times J}E_i\otimes_{\varepsilon}F_j \tag{C.2.3.12}
$$

*is a linear topological isomorphism.*

*(2) The canonical continuous linear map*

$$
\left(\prod_{i\in I}E_i\right)\widehat{\otimes}_{\varepsilon}\left(\prod_{j\in J}F_j\right)\to\prod_{(i,j)\in I\times J}E_i\widehat{\otimes}_{\varepsilon}F_j \tag{C.2.3.13}
$$

*is a linear topological isomorphism.*

Proof. The assertion in (1) is immediate from the definition of $\otimes_{\varepsilon}$ and the passage of finite products through weak-duals and spaces of separately continuous bilinear forms. For (2), see [Jar, §16.3, Thm.1].$^9$ $\square$

---

$^9$The proof of this looks short; can a proof be given here to save the reader from [Jar]?

## PDF page 679

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **679**

C.2.3.2. *Projective tensor products.* Another topology on tensor products of Hausdorff locally convex topological $\mathbf C$-vector spaces we need is the projective tensor product topology, also called the $\pi$-topology. For $E,F$ two Hausdorff locally convex complex vector spaces, there exists on the algebraic tensor product $E\otimes F$ a unique locally convex topology such that for any locally convex complex vector space $G$, continuous linear maps $E\otimes F\to G$ correspond bijectively to *continuous* (i.e. not merely separately continuous) bilinear maps $E\times F\to G$. This topology is referred to as the *projective* tensor product topology on $E\otimes F$, and when $E\otimes F$ is equipped with this topology it is denoted

$$
E\otimes_{\pi}F. \tag{C.2.3.14}
$$

The space of $B(E,F)$ of continuous bilinear forms on $E\times F$ is linearly identified with the continuous dual of $E\otimes_{\pi}F$.

By [Tre, Ch. 43] (or [Scha, Ch. III, pp. 93-94]), a fundamental system of neighborhoods of $0$ for this topology on $E\otimes F$ is given by the convex circled hulls of the sets of the form

$$
U_i\otimes V_j=\{u_i\otimes v_j:u_i\in U_i,v_j\in V_j\} \tag{C.2.3.15}
$$

where $U_i$ and $V_j$ vary through fundamental systems of neighborhoods of $0$ in $E$, respectively $F$. This description of a base of 0-neighborhoods clearly implies the associativity of the $\pi$-topology for tensor products of finitely many Hausdorff locally convex spaces.

The projective tensor product of two Hausdorff locally convex topological $\mathbf C$-vector spaces is Hausdorff [Tre, Prop. 43.3]. The completion of $E\otimes F$ with respect to the projective topology is denoted $E\widehat{\otimes}_{\pi}F$. Its formation is compatible with completion of the factors by [Tre, Prop. 43.9] and the universal property of completion.

The analog of Lemma C.2.3.5 for projective tensor products holds by [Jar, §15.4, Thm. 1, p. 332]).$^{10}$

By [Scha, Ch. III, 6.4], in the special case when the tensor factors $E,F$ of the projective tensor product $E\widehat{\otimes}_{\pi}F$ are Fréchet spaces, the general element of $E\widehat{\otimes}_{\pi}F$ can be written in the form

$$
\sum_{k\ge 1}\lambda_k x_k\otimes y_k \tag{C.2.3.16}
$$

where $\{\lambda_k\}$ is an absolutely summable sequence in $\mathbf C$ and $\{x_k\}_{k\ge 1}$, $\{y_k\}_{k\ge 1}$ are sequences in $E,F$ respectively that converge to $0$ (it is readily checked that conversely all such infinite series converge within $E\widehat{\otimes}_{\pi}F$). This result due to Grothendieck is extremely useful when carrying out calculations, as we shall see (for example) in Appendix D.

Of great importance is the good behavior of $\otimes_{\pi}$ with respect to quotient maps. If $T_1:E_1\to F_1$ and $T_2:E_2\to F_2$ are quotient maps between Hausdorff locally convex topological vector spaces then $T_1\otimes_{\pi}T_2$ is clearly a quotient map by (C.2.3.15), but the analogue for the completions is more subtle [Tre, Prop. 43.9]:

Proposition C.2.3.7. *If $T_1:E_1\to F_1$ and $T_2:E_2\to F_2$ are quotient maps between Hausdorff locally convex topological vector spaces then $T_1\widehat{\otimes}_{\pi}T_2$ is a quotient map onto its image (given the subspace topology), and it is surjective when $E_1$ and $E_2$ are metrizable.*

The surjectivity of $T_1\widehat{\otimes}_{\pi}T_2$ can fail more generally (when it is not assumed that $E_1$ and $E_2$ are metrizable). The projective tensor product topology is finer than the injective tensor product topology: the identity map $\rho:E\otimes_{\pi}F\to E\otimes_{\varepsilon}F$ on $E\otimes F$ is continuous [Tre, Prop. 43.5]. When one of $E$ or $F$ is nuclear (a topic to be discussed in §C.2.4) then the linear bijection $\rho:E\otimes_{\pi}F\to E\otimes_{\varepsilon}F$ is a homeomorphism, so in such cases $E\widehat{\otimes}_{\pi}F$ inherits the good properties of $E\widehat{\otimes}_{\varepsilon}F$ with respect to subspace inclusions in $F$.

Remark C.2.3.8 (On the equicontinuous subsets of $(E\otimes_{\varepsilon}F)'$). We now record a useful observation from the paragraph following [Tre, Def. 49.1, p.500] that provides a description of equicontinuous subsets of the

---

$^{10}$Is this sentence really necessary? If so, why? If not, remove.

## PDF page 680

**680** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

topological dual of $E\otimes_{\varepsilon}F$ for Hausdorff locally convex topological $\mathbf C$-vector spaces $E$ and $F$. By definition, a 0-neighborhood base of $E\otimes_{\varepsilon}F$ is given by polars $(A'\otimes B')^{\circ}$ for $A'\otimes B':=\{a'\otimes b':a'\in A',b'\in B'\}$ with equicontinuous subsets $A'\subset E'_{\sigma}$ and $B'\subset F'_{\sigma}$. An equicontinuous subset of $(E\otimes_{\varepsilon}F)'$ is therefore exactly a subset of the bipolar $(A'\otimes B')^{\circ\circ}$ for equicontinuous $A'\subset E'_{\sigma}$ and $B'\subset F'_{\sigma}$.

This description of the equicontinuous subsets of $(E\otimes_{\varepsilon}F)'$ will be used when proving “kernel theorems” in Appendix D. (By Lemma C.2.2.2, the given topology on a Hausdorff locally convex topological $\mathbf C$-vector space is the same as the topology of uniform convergence on the weakly closed convex circled equicontinuous subsets of the topological dual. When applied to $E\otimes_{\varepsilon}F$ that gives us nothing new via the preceding bipolar description since $M^{\circ\circ\circ}=M^{\circ}$ for any subset $M$ of a Hausdorff locally convex topological vector space [Scha, Ch IV, Cor. 1 to 1.5].)

The proofs of Lemma D.1.3.7, Lemma D.2.2.2, and [Tre, Thm. 51.6(51.3), p. 530] are typical arguments resting on the preceding description. It is particularly useful when $E$ or $F$ is nuclear because the resulting topological equality $E\otimes_{\pi}F=E\otimes_{\varepsilon}F$ in such cases (as noted above, and to be discussed further in §C.2.4) then relates the projective tensor product topology to a function space on a product.

Before we continue on and discuss a third (and final) tensor topology – the inductive topology – for which the only reference we are aware of in the literature is Grothendieck's AMS memoir [Gro-b] (see [Gro-b, Ch. I, §3, No. 1, p. 73]), we record an important result on the interaction of projective tensor products with inductive limits in one tensor factor provided the other tensor factor is normable.

Proposition C.2.3.9 (Normability and preservation of inductive limits under projective tensor products). *Let $I$ be a set, $\{E_i\}_{i\in I}$ an $I$-indexed family of Hausdorff locally convex topological $\mathbf C$-vector spaces, $F$ a Hausdorff locally convex topological $\mathbf C$-vector space. Assume $F$ is normable. Then*

*(1) the canonical continuous linear bijection*

$$
\bigoplus_{i\in I}(E_i\otimes_{\pi}F)\to\left(\bigoplus_{i\in I}E_i\right)\otimes_{\pi}F \tag{C.2.3.17}
$$

*is a linear topological isomorphism. In particular, it extends to a linear topological isomorphism*

$$
\bigoplus_{i\in I}(E_i\widehat{\otimes}_{\pi}F)\to\left(\bigoplus_{i\in I}E_i\right)\widehat{\otimes}_{\pi}F. \tag{C.2.3.18}
$$

*(2) If $I$ is filtered then the canonical continuous linear bijection*

$$
\varinjlim_{i\in I}(E_i\otimes_{\pi}F)\to\left(\varinjlim_{i\in I}E_i\right)\otimes_{\pi}F \tag{C.2.3.19}
$$

*is a linear topological isomorphism.*

The second assertion in (1) follows from the first by passage to completions since an arbitrary locally convex direct sum of complete spaces is complete [Scha, Ch. II, 6.2]. The assertion in (2) is immediate from the first assertion in (1) via the construction of locally convex inductive limits as quotients of locally convex direct sums. The first assertion in (1) is [Jar, §15.5, Cor. 4(a), p. 334], and earlier [Gro-b, Ch. I, §3, No. 1, Cor. p. 47]. It rests on [Gro-b, Ch. I, §1, No. 3, Prop. 6(2), p. 46], the proof of which is a simple verification that the continuous duals of $\bigoplus_{i\in I}(E_i\otimes_{\pi}F)$ and $(\bigoplus_{i\in I}E_i)\otimes_{\pi}F$ have the same equicontinuous parts. This in turn comes down to the explicit description of a 0-neighborhood base for locally convex direct sums as given in [Scha, Ch. II, p. 55] (combined with the fact that since $F$ is normable, the unit ball $B$ is a bounded 0-neighborhood): that description enables proving that an $I$-indexed product of equicontinuous parts of continuous bi-linear forms on the $E_i\times F$'s is equicontinuous in the continuous dual of $(\bigoplus_{i\in I}E_i)\otimes_{\pi}F$ as well (by testing it on the closed convex circled hull of the union of $\{V_i\otimes B\}$ in $(\bigoplus_{i\in I}E_i)\otimes_{\pi}F$, with $V_i$ a 0-neighborhood in $E_i$).

## PDF page 681

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **681**

We will encounter throughout this work examples where even if $F$ is nuclear Fréchet of infinite dimension (so never normable [Tre, Cor. 2 to Prop. 50.2]) and $I=\mathbf N$ with each $E_i$ nuclear Fréchet and the transition maps are linear topological embeddings (hence with closed range), the continuous linear bijection (C.2.3.19) is not a topological isomorphism. This is a primary reason we will need to discuss the inductive tensor topology that is better-behaved with respect to inductive limits.

In the presence of normability, projective tensor products do behave well with respect to countable inductive limits:$^{11}$

Proposition C.2.3.10 (Countable inductive systems of normable tensor factors). *Let $\{E_k\}_{k\ge 0}$ and $\{F_k\}_{k\ge 0}$ be sequences of normable Hausdorff locally convex topological $\mathbf C$-vector spaces. Let $E$ and $F$ be their respective locally convex inductive limits. The canonical continuous linear bijection*

$$
\varinjlim_{(k,k')\ge (0,0)} E_k\otimes_\pi F_{k'}\to E\otimes_\pi F \tag{C.2.3.20}
$$

*(with $\mathbf N\times\mathbf N$ partially ordered via component-wise comparison) is a linear topological isomorphism.*

For the convenience of the reader, we provide a direct argument below to bypass additional technical concepts that arise in various proofs one finds in the literature. It rests on a simple construction with $0$-neighborhoods in locally convex direct sums that we gave in Lemma C.1.5.1.

Proof of Proposition C.2.3.10. Since $\otimes_\pi$ takes quotient maps to quotient maps, in view of the construction of locally convex inductive limits as quotients of the corresponding direct sums it suffices to prove the analogous result for countable direct sums. By symmetry between the $E_k$'s and $F_{k'}$'s in the normability hypotheses, it suffices to show that projective tensor product against $F:=\bigoplus_{k\ge 0}F_k$ passes through countable locally convex direct sums of normable spaces.

In other words, we want to show that the inverse of the natural continuous linear bijection

$$
\bigoplus_{k\ge 0}(E_k\otimes_\pi F)\to E\otimes_\pi F
$$

is continuous. It is enough to show that members of a base of $0$-neighborhoods of the source have images that are $0$-neighborhoods in the target. We use the base of $0$-neighborhoods $W=\mathrm{cch}(\bigcup_{k\ge 0}(U_k\otimes V_k))$ for $0$-neighborhoods $U_k\subset E_k$ and $V_k\subset F$ for each $k\ge 0$. By Proposition C.1.5.1 applied to the $V_k$'s in $F$, we can rewrite each $U_k\otimes V_k$ as $(1/\rho_k)U_k\otimes(\rho_k V_k)$ for suitable $\rho_k>0$ so that all $\rho_k V_k$'s contain a common $0$-neighborhood $V$ in $F$. Thus, for $U'_k:=(1/\rho_k)U_k$ we see that $W$ contains $\mathrm{cch}(U'\otimes V)$ for the $0$-neighborhood $U=\mathrm{cch}(\cup_{k\ge 0}U'_k)\subset E$, so we are done. $\square$

C.2.3.3. *Metrizability, and separately continuous and continuous bi-linear forms.* We next record a criterion to determine when a separately sequentially continuous bilinear map $E\times F\to G$ between Hausdorff locally convex topological $\mathbf C$-vector spaces $E,F,G$ is sequentially continuous. When sequences are sufficient to probe the topologies of $E$ and $F$, this will provide a mechanism for sometimes verifying that a given separately continuous bilinear mapping is continuous. For example, sometimes this can be used to show continuity of linear maps from projective tensor products, in view of the universal mapping property of projective tensor products. We refer the reader to the proof of [Bou-TVS, Ch. III, §5, no. 2, Prop. 2, p. III.29; Cor. 1, p. III.30] for similar arguments resting on the Uniform Boundedness Principle.

Proposition C.2.3.11 (Sequential continuity of separately sequentially continuous bi-linear mappings). *Let $E,F,G$ be Hausdorff locally convex topological $\mathbf C$-vector spaces. Let:*

$$
A:E\times F\to G \tag{C.2.3.21}
$$

---

$^{11}$Why is this result recorded, since it is never cited anywhere? Is it implicit somewhere else?

## PDF page 682

**682** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

*be a separately sequentially continuous bi-linear mapping. If $E$ is Fréchet then $A$ is sequentially continuous.*

Proof. Let $\{u_m\}_{m\ge 0}\subset E$ be a null-sequence in $E$ (i.e., converging to $0$), and $\{v_m\}_{m\ge 0}\subset F$ a convergent sequence in $F$. It suffices to show $A(u_m,v_m)\to 0$. By separate sequential continuity of $A$ and $E$ being a metric space, the linear operators $A(\cdot,v_m):E\to G$ are continuous. Moreover, for every $u\in E$, the subset $\{A(u,v_m)\}_{m\ge 0}\subset G$ is bounded since $A(u,\cdot):F\to G$ is continuous.

Thus, the sequence $\{A(\cdot,v_m)\}_{m\ge 0}\subset\mathscr L(E,G)$ is pointwise bouinded, so since $E$ is Baire (as it is Fréchet), we see by [Scha, Ch. III, 4.2] that $\{A(\cdot,v_m)\}_{m\ge 0}\subset\mathscr L(E,G)$ is equicontinuous. Let $U\subset G$ be any $0$-neighborhood. There therefore exists a $0$-neighborhood $U_0\subset E$ such that $A(U_0,v_m)\subset U$ for every integer $m\ge 0$. Being $\{u_m\}_{m\ge 0}$ a null-sequence, there exists $m_0\ge 0$ such that for every integer $m\ge m_0$, we have $u_m\in U_0$. It follows that for every $m\ge m_0$, $A(u_m,v_m)\in U$, and hence $\lim_{m\to +\infty}A(u_m,v_m)=0$. $\square$

C.2.3.4. *Inductive tensor products.* One more locally convex topology on algebraic tensor products of Hausdorff locally convex topological $\mathbf C$-vector spaces features throughout this work: the inductive tensor product topology. As literature references, we mention [Scha, Ch. III, p. 96] and [Gro-b, Ch. I, §3, No. 1, Def. 3, p. 74].

For $E,F$ two Hausdorff locally convex topological $\mathbf C$-vector spaces, we define on $E\otimes F$ the locally convex topology that is finest among those such that for any Hausdorff locally convex topological $\mathbf C$-vector space $G$, the bilinear maps

$$
E\times F\to G
$$

that are separately continuous make the corresponding linear map $E\otimes F\to G$ be continuous. That such a Hausdorff locally convex topology on $E\otimes F$ indeed does exist is the content of [Gro-b, Ch. I, §3, No. 1, Prop. 13, p. 73].$^{12}$ We denote by

$$
E\otimes_\iota F \tag{C.2.3.22}
$$

the algebraic tensor product topologized in this manner, and refer to it as the *inductive tensor product* of $E$ and $F$.

We claim $E\otimes_\iota F$ is Hausdorff. It suffices to show $0$ is a closed point. The identity map on $E\otimes F$ is continuous as a bijective map of topological groups $E\otimes_\iota F\to E\otimes_\pi F$ because the continuous bilinear pairing $E\times F\to E\otimes_\pi F$ is separately continuous. Thus, the Hausdorff property of $E\otimes_\pi F$ gives the desired closedness of $\{0\}$ in $E\otimes_\iota F$. With the Hausdorff property established, there is a good notion of completion for $E\otimes_\iota F$, which we denote as

$$
E\overline{\otimes}F. \tag{C.2.3.23}
$$

As a consequence of Proposition C.2.3.11 and universal mapping properties of the inductive and projective tensor product topologies, we have the following:

Corollary C.2.3.12. *Let $E,F$ be two Fréchet spaces. Then the canonical continuous linear map*

$$
E\otimes_\iota F\to E\otimes_\pi F \tag{C.2.3.24}
$$

*is a linear topological isomorphism. In particular, the induced continuous linear map $E\overline{\otimes}F\to E\widehat{\otimes}_\pi F$ between completions is a topological isomorphism.*

We collect properties of inductive tensor products into the following:

Proposition C.2.3.13 (Permanence properties of inductive tensor products). *Formation of inductive tensor products satisfies the following properties:*

---

$^{12}$Maybe can insert a more readable explanation than Grothendieck gives?

## PDF page 683

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **683**

*(1) Let $I,J$ be sets, $E_i$ for $i\in I$, $F_j$ for $j\in J$, Hausdorff locally convex topological $\mathbf C$-vector spaces. Assume that $F$ is a Fréchet space. Then the canonical continuous linear map*

$$
\left(\prod_{i\in I}E_i\right)\overline{\otimes}F\to\prod_{i\in I}(E_i\overline{\otimes}F) \tag{C.2.3.25}
$$

*is a linear topological isomorphism.*

*(2) If $I$ and $J$ are filtered sets, and $\{E_i\}_{i\in I}$ and $\{F_i\}_{i\in J}$ two directed families of Hausdorff locally convex topological $\mathbf C$-vector spaces. We define $E:=\varinjlim_{i\in I}E_i$ and $F:=\varinjlim_{j\in J}F_j$ endowed with their locally convex inductive limit topologies, which we assume are Hausdorff.$^{13}$*

*The canonical continuous linear map*

$$
\varinjlim_{(i,j)\in I\times J}E_i\otimes_\iota F_j\to E\otimes_\iota F \tag{C.2.3.26}
$$

*is a linear topological isomorphism. The subspace topology inherited from $E\overline{\otimes}F$ by the linear subspace linearly generated by the images of each $E_i\overline{\otimes}F_j$ into $E\overline{\otimes}F$ is the locally convex inductive limit of the $E_i\overline{\otimes}F_j$'s. In other words, the canonical continuous linear map*

$$
\varinjlim_{(i,j)\in I\times J}E_i\overline{\otimes}F_j\to E\overline{\otimes}F \tag{C.2.3.27}
$$

*is a topological embedding (with dense image via (C.2.3.25)).*

*If $I,J$ are countable and totally ordered, $E_i,F_j$ are nuclear Fréchet spaces, and the resulting inductive systems are strict, then (C.2.3.27) is a linear topological isomorphism.*

*(3) For Hausdorff locally convex topological $\mathbf C$-vector spaces $E$ and $F$, if they are barrelled respectively bornological then so is $E\overline{\otimes}F$.*

Nuclearity will be discussed in §C.2.4.

Proof. Assertion (1) and all but the final assertion in (2) are [Gro-b, Ch. I, §3, No. 1, Prop. 14, p. 76]. For the last assertion in (2), we first note that since the topological embedding (C.2.3.27) has dense image, it suffices to check that the countable inductive limit on left side is complete. Since a countable strict inductive limit of complete Hausdorff locally convex spaces is Hausdorff and complete [Scha, Ch. II, 6.6], it suffices for the final assertion in (2) to verify that the countable inductive system $\{E_i\overline{\otimes}F_j\}$ is strict. By Corollary C.2.3.12 it agrees with the countable inductive system $E_i\widehat{\otimes}_\pi F_j$, and the nuclearity hypothesis ensures (by [Tre, Thm. 50.1(a)$\Leftrightarrow$(f)]) that this agrees with the inductive system $E_i\widehat{\otimes}_\varepsilon F_j$. The latter is strict by Lemma C.2.3.5(1).

The proof of (3) is a consequence of the definitions (see also [Gro-b, Ch. I, §3, No. 2, p. 78]).$^{14}$ $\square$

C.2.3.5. *Linear topological embeddings and injective tensor products in the presence of nuclearity.* The following result provides a sufficient condition for completed inductive tensor products to commute with linear topological embeddings (the analogous assertion for completed injective tensor products is Lemma C.2.3.5(1), which then gives the same for completed projective tensor products when one of the tensor factors is nuclear because in such cases $\widehat{\otimes}_\varepsilon=\widehat{\otimes}_\pi$ by [Tre, Thm. 50.1(a)$\Leftrightarrow$(f)] (nuclearity will be reviewed at length in §C.2.4; this aspect of nuclearity is all we will need about it before then, in addition to the fact that nuclearity is inherited by Hausdorff quotients [Scha, Ch. III, 7.4]).

---

$^{13}$Inserted hypothesis here that $E$ and $F$ are Hausdorff, which should be harmless in practice, right?

$^{14}$Must say more about an actual proof; not clear how it follows from “the definitions”, and the reference to [Gro-b] merely says it is obvious.

## PDF page 684

**684** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

Proposition C.2.3.14 (Inductive tensor products and linear topological embeddings). *Let $E_1,E_2,F$ be Hausdorff locally convex topological $\mathbf C$-vector spaces, and $E_1\to E_2$ a linear topological embedding. Assume:*

*(1) $E_1,E_2$ are nuclear Fréchet spaces (so the given topological embedding $E_1\to E_2$ is closed),*

*(2) $F$ is a strict locally convex countable inductive limit of nuclear Fréchet spaces $F_k$.*

*Then the continuous linear map*

$$
E_1\overline{\otimes}F\to E_2\overline{\otimes}F \tag{C.2.3.28}
$$

*is a linear topological embedding.*

Beware that the result for the $F_k$'s in place of $F$ doesn't formally imply the result for $F$ via passage to a locally convex inductive limit via the final assertion in Proposition C.2.3.13(2) because passage to locally convex inductive limits doesn't generally preserve the property of maps being topological embeddings (even when the given maps are closed embeddings at each layer). Such failure underlies the phenomenon of closed subspaces of LF-spaces that are not limit subspaces, as discussed in Example C.1.5.7. Thus, the proof has to use features specific to the given circumstances.

Proof. We let $\{F_k\}_{k\ge 0}$ be a defining sequence of nuclear Fréchet spaces, with $F_k\subset F_{k+1}$ inclusions and linear topological embeddings for each integer $k\ge 0$, such that $\varinjlim_{k\ge 0}F_k=F$ linearly and topologically. Each $E_i\overline{\otimes}F_k$ is a nuclear Fréchet space by Corollary C.2.3.12 combined with [Tre, (50.17)] and [Scha, Ch. III, 7.5; Ch. I, 6.1; Ch. IV, 5.2; Ch. II, Cor. to 7.1]. By the end of Proposition C.2.3.13(2) applied to $I=\{*\}$, $J=\mathbf N$, with $E_*=E_1,E_2$ respectively, we see that $E_i\overline{\otimes}F=\varinjlim_k(E_i\overline{\otimes}F_k)$ as a strict countable inductive limit of nuclear Fréchet spaces.

Each map $E_1\overline{\otimes}F_k\to E_2\overline{\otimes}F$ is a topological embedding because it is a composition

$$
E_1\overline{\otimes}F_k\simeq E_1\widehat{\otimes}_\pi F_k\simeq E_1\widehat{\otimes}_\varepsilon F_k\hookrightarrow E_2\widehat{\otimes}_\varepsilon F_k=E_2\overline{\otimes}F_k\hookrightarrow E_2\overline{\otimes}F
$$

(first isomorphism using Corollary C.2.3.12, the second using nuclearity of $E_1$, the middle embedding using Lemma C.2.3.5(1), and the final embedding as a general feature of strict countable locally convex inductive limits [Scha, Ch. II, 6.4]). We need to show that the continuous linear inclusion of the strict countable inductive limit of the terms on the left side into the right side is also a topological embedding.

For every integer $k\ge 0$, the complex of $\mathbf C$-linear spaces

$$
0\to E_1\widehat{\otimes}_\pi F_k\xrightarrow{j_k}E_2\widehat{\otimes}_\pi F_k\xrightarrow{q_k}(E_2/E_1)\widehat{\otimes}_\pi F_k\to 0 \tag{C.2.3.29}
$$

is topologically exact:

- the continuous linear map $j_k$ is a topological embedding due to nuclearity of $F_k$ identifying both $\widehat{\otimes}_\pi$'s with $\widehat{\otimes}_\varepsilon$'s (to which Lemma C.2.3.5(1) may be applied), and $j_k$ has closed range by completeness of $E_1\widehat{\otimes}_\pi F_k$,
- the continuous linear map $q_k$ is a surjective quotient map by Proposition C.2.3.7 since $E_2/E_1$ is metrizable and even Fréchet [Scha, Ch. I, 6.3] (and $F_k$ is metrizable by hypothesis),
- the middle exactness follows from the Hahn-Banach theorem and mapping properties of completions and the projective tensor product (if the closed subspace $(\ker q)/(E_1\widehat{\otimes}_\pi F_k)\subset (E_2\widehat{\otimes}_\pi F_k)/(E_1\widehat{\otimes}_\pi F_k)$ is nonzero then some nonzero continuous linear functional $\ell$ on $E_2\widehat{\otimes}_\pi F_k$ vanishes on $E_1\widehat{\otimes}_\pi F_k$ and does not factor through $(E_2/E_1)\widehat{\otimes}_\pi F_k$, and this corresponds to a continuous bilinear form $B:E_2\times F_k\to\mathbf C$ that vanishes on $E_1\times F_k$ yet doesn't factor through $(E_2/E_1)\times F_k$, an absurdity).

Passing to the inductive limit on the $j_k$'s, we see that the continuous linear map $E_1\overline{\otimes}F\to E_2\overline{\otimes}F$ is injective (not yet known to be a topological embedding).

Just as we showed strictness for each $\{E_i\widehat{\otimes}_\pi F_k\}_{k\ge 0}$, the inductive system $\{(E_2/E_1)\widehat{\otimes}_\pi F_k\}_{k\ge 0}$ is strict (as the Fréchet $E_2/E_1$ is nuclear too). The description of a base of $0$-neighborhoods for the locally convex topology

## PDF page 685

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **685**

of an inductive limit via the corresponding direct sum as in (C.1.5.1) shows that for a compatible system of linear quotient maps $f_i:V_i\to\overline{V}_i$ the resulting map $\varinjlim V_i\to\varinjlim\overline{V}_i$ is also a quotient map. Thus, $\mathrm{coker}(j:E_1\overline{\otimes}F\to E_2\overline{\otimes}F)$ equipped with its quotient topology from $E_2\overline{\otimes}F$ is linearly and topologically identified with the strict locally convex inductive limit $(E_2/E_1)\overline{\otimes}F$ of the nuclear Fréchet spaces $(E_2/E_1)\widehat{\otimes}_\pi F_k$.

We deduce that the continuous linear map $q:E_2\overline{\otimes}F\to (E_2/E_1)\overline{\otimes}F$ between strict LF-space spaces is a quotient map whose closed kernel $\ker(q)$ received a continuous linear bijection from $E_1\overline{\otimes}F$. Since the source and target of $q$ are strict inductive limits of nuclear Fréchet spaces, Corollary C.1.5.13 (whose proof ultimately rests on the Open Mapping Theorem for LF-spaces) tells us that the closed subspace $\ker(q)$ is a limit subspace of $E_2\overline{\otimes}F$. More specifically, since $\ker(q)$ meets each layer $E_2\overline{\otimes}F_k=E_2\widehat{\otimes}_\pi F_k$ of $E_2\overline{\otimes}F$ in exactly $E_1\overline{\otimes}F_k=E_1\widehat{\otimes}F_k$, Corollary C.1.5.13 gives that $\varinjlim_k E_1\overline{\otimes}F_k\to\ker(q)$ is a topological isomorphism. This latter inductive limit is topologically $E_1\overline{\otimes}F$, so the continuous injective linear map (C.2.3.28) is a topological embedding as desired. $\square$

C.2.4. **Nuclear spaces.** The two topological tensor products $\otimes_\pi$ and $\otimes_\varepsilon$ of Hausdorff locally convex topological $\mathbf C$-vector spaces $E,F$ are related: the projective topology $\otimes_\pi$ on $E\otimes F$ is finer than the injective topology $\otimes_\varepsilon$, which is to say the identity map

$$
E\otimes_\pi F\to E\otimes_\varepsilon F \tag{C.2.4.1}
$$

is continuous. This is deduced from their respective universal properties (see [Tre, Prop. 43.5]).

We are interested in two aspects relating to these two locally convex topologies on $E\otimes F$:

(1) to discuss when (C.2.4.1) is a topological isomorphism;

(2) to illustrate when the natural map $E'\otimes F\to\mathscr L_{\mathfrak S}(E,F)$ has dense image with respect to suitable $\mathfrak S$-topologies, and which such topologies qualify.

These questions were the subject of a significant portion of Grothendieck's doctoral dissertation, and we refer the reader particularly to [Gro-b, Ch. I, §5; Ch. II, §3].

C.2.4.1. *Characterizations of nuclearity.* The first of the two questions at hand, namely when the continuous linear bijection $E\otimes_\pi F\to E\otimes_\varepsilon F$ is a homeomorphism for Hausdorff locally convex topological $\mathbf C$-vector spaces $E,F$, is best phrased as asking when for a fixed Hausdorff locally convex topological $\mathbf C$-vector space $E$ the natural transformation $E\otimes_\pi(\cdot)\to E\otimes_\varepsilon(\cdot)$ of functors from Hausdorff locally convex topological $\mathbf C$-vector spaces to Hausdorff locally convex topological $\mathbf C$-vector spaces is an isomorphism; i.e., when is (C.2.4.1) a topological isomorphism for all $F$?

The second part of Grothendieck's doctoral dissertation is devoted to answering and studying this question, leading to the definition of nuclear spaces. The following is [Gro-b, Ch. II, §2.1, Def. 4].

Definition C.2.4.1 (Nuclear Hausdorff locally convex topological $\mathbf C$-vector spaces). Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. We say $E$ is nuclear if and only if the identity map $E\otimes_\pi F\to E\otimes_\varepsilon F$ is a linear topological isomorphism for every Hausdorff locally convex topological $\mathbf C$-vector space $F$.

It is equivalent to work with the completed tensor products in this definition, since the uncompleted versions are Hausdorff (and so topologically embed into their completions). There is a different definition of nuclearity given in [Scha, Ch. III, p. 100], but this is equivalent to the above definition by combining [Scha, Ch. III, 7.2] with a long list of equivalents to Definition C.2.4.1 given in [Tre, Thm. 50.1].

As simple as Definition C.2.4.1 appears, the theory of nuclearity cannot take off the ground without concrete and usable characterizations. These all rest on the concept of nuclear operator between Banach spaces, which we will be recalling throughout §C.3. We briefly recall for now a concrete characterization (which however is not the definition) (see [Scha, Ch. III, Rem. to 7.1]): for $E,F$ Banach spaces, a continuous linear operator $T:E\to F$ is nuclear if and only if there exists an absolutely summable sequence $\{\lambda_k\}_{k\ge 0}$ in $\mathbf C$,

## PDF page 686

**686** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

a sequence $\{f_k\}_{k\ge 0}\subset E'$ converging to $0$ (in the usual Banach-dual topology), and $\{x_k\}_{k\ge 0}\subset F$ converging to $0$ such that

$$
T=\sum_{k\ge 0}\lambda_k(\langle\cdot,f_k\rangle_{E,E'})x_k \tag{C.2.4.2}
$$

where any such sum always converges pointwise on $E$. In particular, finite-rank linear maps are nuclear.

With this concept in mind, nuclearity of a Hausdorff locally convex topological $\mathbf C$-vector space $E$ is characterized as follows (see [Scha, Ch. III, 7.2(b)$\Leftrightarrow$(c)] and [Tre, Thm.50.1] for the proof):

Theorem C.2.4.2 (Characterizations of nuclearity - I). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. The following conditions are equivalent:*

*(1) $E$ is nuclear.*

*(2) For any convex circled $0$-neighborhood $U\subset E$, there exists a convex circled $0$-neighborhood $V\subset U$ such that the canonical continuous linear map $\widehat{E}_V\to\widehat{E}_U$ is nuclear, where $\widehat{E}_U$ is the completion of $E$ for the gauge semi-norm $p_U$ associated to $U$ as in (C.1.2.1) and likewise for $V$.*

*(3) For any Banach space $F$, the canonical continuous linear map $E\widehat{\otimes}_\pi F\to E\widehat{\otimes}_\varepsilon F$ is a topological isomorphism.*

*(4) For any Hausdorff locally convex topological vector space $F$, the canonical continuous linear map $E\widehat{\otimes}_\pi F\to E\widehat{\otimes}_\varepsilon F$ is topological isomorphism.*

Upon defining the general concept of nuclear maps (not only for continuous linear maps between Banach spaces), nuclearity for $E$ as in the preceding theorem is further characterized by the following property of $E$: for any Banach space $F$, any continuous linear map $E\to F$ is nuclear. For more characterizations of nuclearity of spaces, see [Tre, Thm. 50.1].

C.2.4.2. *Continuous dual of $E\otimes_\varepsilon F$.* The proof of equivalences of the many characterizations of nuclearity in [Tre, Thm.50.1] rests on a description of the continuous dual of $E\otimes_\varepsilon F$ (the uncompleted injective tensor product of two Hausdorff locally convex topological $\mathbf C$-vector spaces) provided in the fundamental [Tre, Prop.49.1] in terms of integral bilinear forms on $E\times F$ that we now review.

Integral bilinear forms and their use in describing the continuous dual of $E\otimes_\varepsilon F$ also underlie further characterizations of nuclearity we will not need, such as combinatorial control over the equicontinuous subsets of the continuous dual of a nuclear space resting on integration over compact (or weakly compact) Choquet simplices, which turns out to characterize nuclearity and for which we refer the reader to [Jar, §21.4, Thm. 3, p. 490].

The description of the continuous dual of $E\otimes_\varepsilon F$, which we will be recalling from [Tre, Prop.49.1] shortly rests on the following construction that we wish to further explain before referring the reader to [Tre, Ch. 49, p. 501] and the discussion contained therein. Recall that for any Hausdorff locally convex topological $\mathbf C$-vector space $E$ and any convex circled and absorbing subset $U$ (not necessarily a $0$-neighborhood), we topologize the linear subspace $E_U:=\bigcup_{m\in\mathbf N}mU\subset E$ by the Minkowski functional $p_U$ as in (C.1.2.1), a seminorm on $E_U$. The separated completion $\widehat{E}_U$ of the semi-normed space $(E_U,p_U)$ is a Banach space which we refer to as the *local Banach space* of $E$ at $U$. By [Scha, Ch. II, 1.5], $\widehat{E}_U$ only depends on the closure of $U$.

Remark C.2.4.3. The local Banach spaces $\widehat{E}_U$ are denoted in [Scha, Ch. III, p. 97] as $\widetilde{E}_U$ and in [Jar, §6.8, p. 116] as $\widetilde{E_{(U)}}$.

Many conditions and structural results on classes of Hausdorff locally convex topological $\mathbf C$-vector spaces $E$ reduce to an analysis in the special case of Banach spaces via the local Banach spaces of $E$. We begin with the following observation, which provides a class of nuclear spaces:

## PDF page 687

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **687**

Lemma C.2.4.4 (Local Banach spaces of weak duals). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. For any convex circled $0$-neighborhood $U\subset E'_\sigma$, the local Banach space $\widehat{(E'_\sigma)}_U$ is finite-dimensional. In particular, the weak dual $E'_\sigma$ of $E$ is always nuclear.*

Proof. Since $U$ is a $0$-neighborhood for the weak topology on $E'$, there exist finitely many elements $\{x_1,\dots,x_N\}\subset E$ and a real number $\varepsilon>0$ such that

$$
U\supset U_\varepsilon(x_1,\dots,x_N):=\bigcap_{1\le k\le N}\{\varphi\in E':|\langle x_k,\varphi\rangle_{E,E'}|\le\varepsilon\}. \tag{C.2.4.3}
$$

Consider the linear subspace $V:=\bigcap_{1\le k\le N}\ker(\iota_E(x_k))\subset E'$, where $\iota_E:E\to (E')^*$ is the evaluation linear map. Noting that each $\iota_E(x_k)$ is continuous on $E'$ with respect to the weak topology, $V$ is closed in $E'_\sigma$ and of finite codimension. It is contained in $U_\varepsilon(x_1,\dots,x_N)$, and hence in $U$. In particular, for $F:=E'$ we see that $F_U/p_U^{-1}(0)$ is a quotient of $F/V$ and so is finite-dimensional. In particular, $\widehat{F}_U=F_U/p_U^{-1}(0)$ is finite-dimensional. $\square$

We will be using below the following observation: by Lemma C.2.1.7, if $E$ is barrelled then $E'_\sigma$ is quasi-complete, and hence the (weakly-)closed convex circled hull of a weakly compact subset of $E'_\sigma$ is weakly compact. This is a consequence of the preservation of pre-compactness (i.e., compactness of closure in the completion) under formation of the convex circled hull in any Hausdorff locally convex topological $\mathbf C$-vector space [Scha, Ch. II, 4.3]. Indeed, in a quasi-complete Hausdorff locally convex topological vector space $F$ any pre-compact subset $C\subset F$ is bounded in $\widehat{F}$ (as compactness implies boundedness) and hence is bounded in $F$. Thus, the closure $\overline{C}\subset F$ is bounded [Scha, Ch. I, 5.1] and thus is complete in $F$ (as $F$ is quasi-complete), so $\overline{C}$ is also closed in $\overline{F}$. By pre-compactness of $C$ in $\widehat{F}$, this gives the compactness of $\overline{C}$ as desired.

Remark C.2.4.5. The barreledness of $E$ above as a sufficient condition for quasi-completeness of $E'_\sigma$ cannot be entirely dropped: there are examples of Hausdorff locally convex topological $\mathbf C$-vector spaces $E$ for which $E'_\sigma$ is not quasi-complete.

We refer the reader to [Gro-e, II, §1, p. 88] for an example of a Fréchet space $F$ whose strong dual $E:=F'_\beta$ is not bornological (equivalently, not barrelled; see [Scha, Ch. IV, 6.6]) and whose weak dual $E'_\sigma$ is not quasi-complete. To see this example is not quasi-complete, we assume to the contrary that the nuclear space $E'_\sigma$ is quasi-complete and seek a contradiction.$^{15}$

We now return to the task at hand. The following lemma is outlined in [Tre, pp. 500-501]. We provide here below the details of the argument, in light of its importance in the description of the continuous dual of $E\otimes_\varepsilon F$ for $E,F$ Hausdorff locally convex topological $\mathbf C$-vector spaces:

Lemma C.2.4.6 (Local representation of continuous forms). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, and $K\subset E$ a compact subset. For any $x\in\overline{\mathrm{ch}}(K)$ (the closed convex hull of $K$ in $E$) there exists a positive Radon measure $\mu$ on $K$ satisfying $\mu(K)=1$ such that the $(E')^*$-valued function $f:K\to (E')^*$ defined as $f(y):=\iota_E(y)$ is $\mu$-integrable in the sense of Pettis, and we have*

$$
\iota_E(x)=\int_K f(y)\,\mathrm d\mu(y) \tag{C.2.4.4}
$$

*as continuous linear forms on $E'_\sigma$ (so $\ell(x)=\int_K\ell(y)\,\mathrm d\mu(y)$ for all $\ell\in E'$).*

We will be discussing the integral in the sense of Pettis in §C.4. We record the proof of Lemma C.2.4.6 below for ease of access, referring to the relevant results in §C.4 on vector-valued integration.

Proof. Using weak topologies, the natural linear map $\iota_E:E_\sigma\to (E')^*_\sigma$ is continuous. Since closure agrees with weak closure for convex subsets of any Hausdorff locally convex topological vector space [Scha,

$^{15}$How do we get a contradiction? Can it be via [Tre, Cor. 1 or Cor. 3 to Prop. 50.2]?

## PDF page 688

**688** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

Ch. IV, 3.1], it follows that the $\sigma((E')^*,E')$-closure of the convex hull of $\iota_E(K)$ contains the image under $\iota_E$ of the closed convex hull of $K$ in $E$. By Theorem C.4.3.2, such $\sigma((E')^*,E')$-closure is itself compact in $(E')^*$, and it equals the set $\{\int_K f\,\mathrm d\mu\}$ as $\mu$ varies over all the probability measures on $K$. For any $x\in\overline{\mathrm{ch}}(K)$, there therefore exists a probability measure $\mu$ on $K$ such that $\iota_E(x)=\int_K\iota_E(y)\,\mathrm d\mu(y)$. (This integral a-priori belongs to $((E')^*_\sigma)'^*$.) $\square$

Remark C.2.4.7. The construction discussed in [Tre, Prop.49.1] of the Radon measure $\mu$ associated to $x\in\overline{\mathrm{ch}}(K)$ as in the statement of Lemma C.2.4.6 contains a point that, we believe, warrants clarification. We therefore thought it helpful to the reader to give a proof of Lemma C.2.4.6 above, so as to render the Lemma applicable as intended throughout the proof of [Tre, Prop.49.1].

The issue is continuity of the extension by linearity of the continuous inverse of $\delta:K\to C(K)'_\sigma$ that sends each $x\in K$ to the point-evaluation functional $\delta_x\in C(K)'$ (a homeomorphism onto its image by compactness of $K$) on the linear span $V$ of $\delta(K)$ which would, if true (with $E$ endowed with its given topology), lead to a continuous linear map $\overline{V}\to\widehat{E}$.

Then since $C(K)'_\sigma$ is nuclear with finite-dimensional local Banach spaces (by Lemma C.2.4.4),'so likewise for $\overline{V}$, we would obtain that such a continuous map has finite-dimensional linear image in $E$ containing $K$, which would force $K$ to be contained in a finite-dimensional linear subspace of $E$. Such linear extension of the inverse to the homeomorphism $\delta$, cannot be continuous as soon as $E$ is an infinite-dimensional Banach space and $K$ is not contained within any finite-dimensional subspace (such $K$ exists, such as $\{0\}\cup\{x_n\}_{n\ge 1}$ for a sequence of linearly independent vectors converging to $0$).

On the other hand, the construction being outlined in [Tre, Prop.49.1] is correct because Lemma C.2.4.6 exhibits the desired measure $\mu$ in [Tre, (49.1)].

The following result is [Tre, Prop.49.1], and the reader can now go through its proof as written in loc.cit., using Lemma C.2.4.6 providing the proof of [Tre, (49.1)] upon which the proof of the result rests.

Proposition C.2.4.8 (Integral bi-linear forms). *A continuous bi-linear form $u:E\times F\to\mathbf C$ is integral, i.e. an element of $\mathscr J(E,F)\subset\mathscr B(E,F)$, if and only if there exist weakly closed equicontinuous subsets $A'\subset E'$ and $B'\subset F'$ and a positive Radon measure $\mu$ on the weakly compact subset $A'\times B'\subset E'_\sigma\times F'_\sigma$ such that $\mu(A'\times B')\le 1$ and for all $(x,y)\in E\times F$, we have*

$$
u(x,y)=\int_{A'\times B'}\langle x,\varphi\rangle_{E,E'}\langle y,\psi\rangle_{F,F'}\,\mathrm d\mu(\varphi,\psi). \tag{C.2.4.5}
$$

C.2.4.3. *Integral mappings and characterizations of nuclearity.* Using integral continuous bilinear forms, we can extend the list of equivalent characterizations of nuclearity for Hausdorff locally convex topological $\mathbf C$-vector spaces from Theorem C.2.4.2 as follows (from [Tre, Rem. 50.1], using [Tre, Def. 49.2]):$^{16}$

Theorem C.2.4.9 (Characterizations of nuclearity - II). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. The following conditions are equivalent:*

*(1) $E$ is nuclear.*

*(2) For any convex circled $0$-neighborhood $U\subset E$, there exists a convex circled $0$-neighborhood $V\subset U$, such that the canonical continuous linear operator $\widehat{E}_V\to\widehat{E}_U$ is integral in the sense that the associated continuous bi-linear form on $\widehat{E}_V\times(\widehat{E}_U)'_\beta$ is integral.*

The idea behind the equivalence in Theorem C.2.4.9 is that integral and nuclear maps between Hilbert spaces are the same class of continuous linear maps (see [Tre, Prop. 49.5, Thm. 49.6] and that integral maps to a complete target can be factored through a Hilbert space (see [Tre, Prop. 49.7].

---

$^{16}$Is this result ever needed? If not, remove all of §C.2.4.3. Too heavy on the reader, need not be told “everything”. Personally, I found [Tre, Rem. 50.1] to be more exhausting than convincing.

## PDF page 689

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **689**

C.2.4.4. *Permanence properties.* Nuclearity satisfies the following permanence properties, contained within [Scha, Ch. III, 7.4, 7.5].

Lemma C.2.4.10 (Permanence properties). *Nuclearity of Hausdorff locally convex topological $\mathbf C$-vector spaces is stable under passage to:*

*(1) linear topological subspaces, Hausdorff quotients by linear subspaces;*

*(2) linear topological products indexed by an arbitrary set, countable topological direct sums;*

*(3) binary projective tensor products (i.e. if two Hausdorff locally convex topological $\mathbf C$-vector spaces $E,F$ are nuclear then $E\otimes_\pi F$ is nuclear).*

We further recall the following nuclearity criterion from [Tre, Prop. 50.6]:$^{17}$

Lemma C.2.4.11 (Duality and nuclearity for Fréchet spaces). *Let $E$ be a Fréchet space. Then $E$ is nuclear if and only if so is $E'_\beta$.*

We will use the following permanence properties that follow from Lemma C.2.4.10(1, 2):

Lemma C.2.4.12 (Nuclearity of inductive and projective limits). *A Hausdorff locally convex topological $\mathbf C$-vector space $E$ is nuclear if any of the following conditions hold:*

*(1) $E$ is the locally convex inductive limit of a sequence of nuclear Hausdorff locally convex topological $\mathbf C$-vector spaces.*

*(2) $E$ is a projective limit, indexed by an arbitrary co-filtered set, of nuclear Hausdorff locally convex topological $\mathbf C$-vector spaces.*

Remark C.2.4.13. The Hausdorff assumption on $E$ is also assumed$^{18}$ in [Gro-b, Ch. II, §2, no. 2, Cor. 1] insofar as it is necessary to deduce nuclearity from presenting the locally convex inductive limit as a *separated* quotient of a nuclear locally convex topological direct sum. The assumption is needed since separatedness is not generally inherited by locally convex inductive limits. We have specialized part (1) to the case the inductive system of nuclear spaces is comprised of Hausdorff spaces too.

Remark C.2.4.14. We further refer the reader to [Scha, Ch.III, §7] for a discussion of the above results from the second part of Grothendieck's dissertation, noting that the Hausdorff property is part of the *definition* of “locally convex topological vector space” in [Scha, Ch. II, p. 47].

C.2.4.5. *Approximation Property.* We consider the injective linear map

$$
\lambda:E'\otimes F\to\mathscr L(E,F) \tag{C.2.4.6}
$$

uniquely determined by

$$
\lambda(\varphi\otimes f):=\langle\cdot,\varphi\rangle_{E,E'}\cdot f. \tag{C.2.4.7}
$$

The following result is [Scha, Ch. III, 9.1] (in which we use the notation $\mathscr L_\gamma$ from Definition C.2.1.5(2)):

Lemma C.2.4.15 (Approximation property). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. The following conditions are equivalent:*

*(1) The identity map in $\mathscr L_\gamma(E,E)$ is in the closure of the image of $E'\otimes E$ under $\lambda$ from (C.2.4.6).*

*(2) The image of $E'\otimes E$ in $\mathscr L_\gamma(E,E)$ under $\lambda$ from (C.2.4.6) is dense.*

*(3) For every Hausdorff locally convex topological $\mathbf C$-vector space $F$, the image of $E'\otimes F$ in $\mathscr L_\gamma(E,F)$ under $\lambda$ from (C.2.4.6) is dense.*

---

$^{17}$This result originally included $E$ that is (DF), but who cares? Removed that.

$^{18}$But nuclearity hasn't even been *defined* beyond the Hausdorff case, so why make this Remark at all?

## PDF page 690

**690** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

*(4) For every Hausdorff locally convex topological $\mathbf C$-vector space $F$, the image of $F'\otimes E$ in $\mathscr L_\gamma(F,E)$ under $\lambda$ from (C.2.4.6) is dense.*

The next lemma records two properties of main interest for us about nuclear spaces beyond their defining condition from Definition C.2.4.1. The first of the two properties stated in the lemma will be used systematically throughout this work to infer that certain Fréchet spaces, or strict inductive limits of Fréchet spaces, are reflexive by deducing that they are Montel via [Tre, Cor. 3 to Prop. 50.2], which asserts that any nuclear Hausdorff locally convex $\mathbf C$-vector space that is also barreled and quasi-complete is Montel (all Fréchet spaces are barreled [Scha, Ch. II, Cor. to 7.1]). The second will be used to infer that in the presence of the equivalent conditions from Lemma C.2.4.15, the traces of nuclear operators (to be discussed in §C.3) can be computed as matrix traces relative to a Schauder basis if one exists.

Lemma C.2.4.16 (Nuclearity and the Approximation Property). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. Assume $E$ is nuclear.*

*(1) Every bounded subset of $E$ is pre-compact. In particular, for any Hausdorff locally convex topological $\mathbf C$-vector space $F$, $\mathscr L_\gamma(E,F)=\mathscr L_\beta(E,F)$.*

*(2) The image of $E'\otimes E$ under $\lambda$ from (C.2.4.6) is dense in $\mathscr L_\gamma(E,E)$ (so all four properties in Lemma (C.2.4.15) hold).*

Proof. Part (1) is [Scha, Ch. III, Cor. 2 to 7.2], and part (2) is [Scha, Ch. III, Cor. 2 to 9.1]. $\square$

Remark C.2.4.17. As a consequence of Lemma C.2.4.16, for $E,F$ two Hausdorff locally convex topological $\mathbf C$-vector spaces with $E$ nuclear, the image of $\lambda:E'\otimes F\to\mathscr L_\beta(E,F)$ is dense (i.e., the finite-rank operators are dense) where the target has the topology of convergence on the bounded subsets of $E$.

We also note that the first part of the lemma says bounded subsets of nuclear spaces $E$ have compact closure in $\widehat{E}$. It does *not* say their closure in $E$ is compact; if $E$ is also quasi-complete (in addition to being nuclear) then bounded subsets of $E$ do have compact closure [Tre, Cor. 1 to Prop. 50.2].

C.2.4.6. *Kernel Theorems.* Nuclearity ensures the existence of kernels for certain classes of continuous operators. We recall the statement of the Schwartz Kernel Theorem in its general form (see [Scha, Ch. IV, 9.5, p. 172]):

Theorem C.2.4.18 (Schwartz Kernel Theorem). *Let $E,F$ be Hausdorff locally convex topological $\mathbf C$-vector spaces. Assume $E$ is nuclear. For each continuous bilinear forms $B:E\times F\to\mathbf C$, there exist equicontinuous sequences $\{\varphi_m\}_{m\ge 0}\subset E'$ and $\{\psi_m\}_{m\ge 0}\subset F'$, and an absolutely summable sequence of complex numbers $\{\lambda_m\}_{m\ge 0}$, such that*

$$
B=\sum_{m\ge 0}\lambda_m\langle\cdot,\varphi_m\rangle_{E,E'}\cdot\langle\cdot,\psi_m\rangle_{E,E'} \tag{C.2.4.8}
$$

*where the convergence is with respect to the topology (on the space of continuous bilinear forms) of uniform convergence on the bounded subsets of $E\times F$.*

We refer the reader to [Scha, Ch. III, §5, p. 91] for a discussion of the topology (on the space of continuous bilinear forms) of uniform convergence on the bounded subsets of $E\times F$, particularly that it is a Hausdorff locally convex topological $\mathbf C$-vector space structure (the notation of loc.cit., writes this space as $\mathscr B(E,F;\mathbf C)$ whereas [Tre, Ch. 42] denotes it as $B(E,F)$). Continuity of $B:E\times F\to\mathbf C$ implies that the image $B(S,T)\subset\mathbf C$ is bounded for any bounded subset $S\times T\subset E\times F$.

We now specialize to the case of a complete nuclear Hausdorff locally convex topological $\mathbf C$-vector space $E$, and a continuous linear map $T:E\to E'_\beta$, so the bilinear form on $E\times E$ defined by

$$
(x,y)\mapsto\langle x,Ty\rangle_{E,E'} \tag{C.2.4.9}
$$

## PDF page 691

**C.2. COMPLEMENTS ON MAPPING SPACES, TOPOLOGICAL TENSOR PRODUCTS, AND NUCLEARITY** · **691**

is continuous. By Theorem C.2.4.18, there exist equicontinuous sequences $\{\varphi_m\}_{m\ge 0},\{\psi_m\}_{m\ge 0}\subset E'$ and an absolutely summable sequence of complex numbers $\{\lambda_m\}_{m\ge 0}$ such that

$$
\langle x,Ty\rangle_{E,E'}=\sum_{m\ge 0}\lambda_m\langle x,\varphi_m\rangle_{E,E'}\cdot\langle y,\psi_m\rangle_{E,E'}.
$$

We will be using the Schwartz Kernel Theorem in special forms (of which Theorem C.2.4.18 is an extension) as given in [Tre, Thm. 51.6] (e.g., $\mathcal S(\mathbf R^n)\widehat{\otimes}_\pi\mathcal S(\mathbf R^m)\simeq\mathcal S(\mathbf R^{n+m})$ as topological vector spaces). We record one such version here for reference:$^{19}$

Theorem C.2.4.19 (Schwartz Kernel Theorem for Schwartz-Bruhat spacees). *Let $G_1,G_2$ be Hausdorff locally compact abelian groups. Assume $G_1$ and $G_2$ are second-countable. Let $\mathcal S(G_1),\mathcal S(G_2)$ be the Hausdorff locally convex topological $\mathbf C$-vector spaces of Schwartz-Bruhat functions on $G_1$, respectively $G_2$. The canonical continuous linear map*

$$
\mathcal S(G_1)'_\beta\widehat{\otimes}_\pi\mathcal S(G_2)\to\mathscr L_\beta(\mathcal S(G_1),\mathcal S(G_2)) \tag{C.2.4.10}
$$

*is a topological isomorphism.*

We refer the reader to Appendix D for a discussion of Schwartz-Bruhat spaces $\mathcal S(G)$ in general. Lemma D.1.8.1 gives further variants of the result.

Proof. By Theorem D.1.5.7, the spaces $\mathcal S(G_1)$ and $\mathcal S(G_2)$ as well as their strong duals are nuclear, complete, and Montel, where the latter means “closed bounded subsets of $E$ are compact, and $E$ is reflexive (in the sense of the strong double-dual)” [Scha, p. 147]. Reflexivity implies barreledness [Scha, Ch. IV, 5.6], so we can apply [Tre, Prop. 50.5] which gives that the natural continuous linear map

$$
E'_\beta\widehat{\otimes}_\pi F\to\mathscr L_\beta(E,F)
$$

is a topological isomorphism for any complete Hausdorff locally convex topological vector spaces $E$ and $F$ such that $E$ is barreled and $E'_\beta$ is nuclear and complete. $\square$

C.2.5. **Complements on the finest locally convex topology.** Finite-dimensional $\mathbf C$-vector spaces have a unique Hausdorff topological vector space structure [Scha, Ch. I, 3.2]. Building on that, as a piece of algebra, there is the notion of *finest locally convex topology* on a $\mathbf C$-vector space $E$. This can be described in two ways (which must therefore coincide): it is defined by the family of all seminorms on $E$, and it is the locally convex inductive limit of the collection of finite-dimensional subspaces. This will be used only in countable-dimensional cases, so such spaces are then even strict LF-spaces.

One example is the Schwartz-Bruhat function space $\mathcal S(F_v)=C^\infty_c(F_v)$ for $F$ a number field and $v$ a finite place of $F$. Another such example is $\mathcal S(\prod_{v\in S}F_v)$ for $S$ a finite set of *finite* places of $F$, as are $\mathcal S(\mathbf A^f_F)$ (for $\mathbf A^f_F$ the finite adeles of $F$) and $\mathcal S(\widehat{\prod}_{v\notin S}(F_v,\mathcal O_{F_v}))$ for $S$ any finite set of places of $F$ containing the Archimedean places of $F$. In this subsection we record some basic facts about this topology, most of which are elementary.

Proposition C.2.5.1 (Properties of the finest locally convex topology). *Let $E$ be a $\mathbf C$-vector space, $\tau$ its finest locally convex topology.*

*(1) The topology $\tau$ is defined by the family of all seminorms on $E$, and is the locally convex inductive limit of all finite-dimensional subspaces of $E$.*

*(2) For any Hausdorff locally convex topological $\mathbf C$-vector space $M$, any linear map $T:E\to M$ is continuous. In particular, the inclusion $(E,\tau)'\subset E^*$ is an equality of vector spaces.*

*(3) Every $\mathbf C$-linear subspace of $E$ is $\tau$-closed and topologically complemented, so $\tau$ is inherited by all $\mathbf C$-linear subspaces and quotients of $E$. Moreover, $(E,\tau)$ is complete.*

---

$^{19}$This result is [Tre, Prop. 50.5] without needing any of the extra generalities above, none of which are therefore ever cited, so why include any of the stuff above?

## PDF page 692

**692** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

*(4) A subset $B\subset E$ is $\tau$-bounded if and only if it is contained in a finite-dimensional subspace of $E$ and bounded with respect to the Euclidean topology on such a subspace.*

*(5) A subset $C\subset E$ is $\tau$-sequentially closed if and only if its intersection with each finite-dimensional $\mathbf C$-linear subspace of $E$ is closed.*

*(6) If $E$ is has countable dimension then $(E,\tau)$ is a nuclear strict LF-space. In particular, with respect to $\tau$ any such $E$ is complete, nuclear and Montel, and its strong dual $E'_\beta$ is a nuclear Fréchet space.*

Proof. We discussed (1) already (namely both descriptions are finest among all locally convex topologies, so they must coincide). The assertion in (2) is immediate from the description as a locally convex inductive limit. To see (3), if $E_0\subset E$ is a $\mathbf C$-linear subspace and $E_1\subset E$ is a linear complement then for the respective finest locally convex topologies $\tau_j$ on $E_j$ we see that $E_0\oplus E_1\to E$ is a topological isomorphism since every finite-dimensional subspace of $E$ is contained in $F_0\oplus F_1$ for finite-dimensional subspaces $F_j\subset E_j$.

The completeness of $(E,\tau)$ is immediate from yet another description of $\tau$ as a locally convex direct sum of lines, since completeness is inherited by arbitrary locally convex direct sums [Scha, Ch. II, 6.2]. This description via a direct sum of lines yields the assertion in (4) from a general property of bounded subsets of locally convex direct sums [Scha, Ch. II, 6.3]. Since convergent *sequences* in a Hausdorff topological vector space are bounded, the sufficiency in (5) is immediate from (4). The necessity in (5) is clear.

Finally, in the countable-dimensional case we can express $E$ as a strict countable inductive limit of finite-dimensional spaces, so $E$ is a nuclear strict LF-space since finite-dimensional spaces are certainly nuclear and strict countable inductive limits preserve nuclearity [Scha, Ch. III, Cor. to 7.4]. Likewise the Montel property is preserved by such inductive limits [Scha, p. 147], so $E$ is Montel. Nuclearity of $E'_\beta$ is inherited from that of $E$ because $E$ is a nuclear Fréchet space [Tre, Prop. 50.6]. Completeness of $E'_\beta$ is a consequence of the bornological property of $E$ [Scha, Ch. IV, 6.1], where the bornological property is inherited through inductive limits from the finite-dimensional case [Scha, Ch. II, Cor. 1 to 8.2].

It remains to show in (6) that $E'_\beta$ is metrizable. Since $E$ is a locally convex countable direct sum of lines, which in turn can be viewed as the strict locally convex direct limit of finite direct sums among such lines, Lemma C.1.6.1(2) yields that the strong dual is the locally convex countable product of (the duals of such) lines. The topology on such a product is the product topology, so the metrizability is immediate from the countability of the product. $\square$

One final permanence property of the finest locally convex topology concerns stability under tensor products in the countable-dimensional case:

Lemma C.2.5.2. *Let $E_1,E_2$ be two Hausdorff locally convex topological $\mathbf C$-vector spaces. Assume $E_1,E_2$ are countably $\mathbf C$-linearly generated, and carry the finest locally convex topology. Then so do $E_1\otimes_\pi E_2$, $E_1\otimes_\varepsilon E_2$ and $E_1\otimes_\iota E_2$, so all three topologies on $E_1\otimes E_2$ coincide and are complete.*

Proof. The completeness of the finest locally convex topology on any $\mathbf C$-vector space is part of Proposition C.2.5.1(3). Since $E_1,E_2$ are nuclear, the continuous linear map $E_1\otimes_\varepsilon E_2\to E_1\otimes_\pi E_2$ given by the identity on $E_1\otimes E_2$ is a topological isomorphism by Theorem C.2.4.2(4) (this gives isomorphism after passing to completions, but both topological tensor products topologically embed into their completions and so we get the assertion without passing to completions). Thus, it suffices to analyze the projective topology and the inductive topology on $E_1\otimes E_2$.

By (C.2.3.26), $E_1\otimes_\iota E_2$ carries the finest locally convex topology on $E_1\otimes E_2$. Since $E_1$ and $E_2$ are each topologically a locally convex direct sum of lines (with their unique Hausdorff topological vector space structure), and lines are normable, by Proposition C.2.3.9(1) it follows that $E_1\otimes_\pi E_2$ is also a locally convex direct sum of countably many lines; i.e., this projective tensor product topology is the finest locally convex topology on $E_1\otimes E_2$. $\square$

## PDF page 693

**C.3. NUCLEAR OPERATORS** · **693**

**C.3. Nuclear operators**

In this section we collect results on nuclear operators. We will be first discussing a few complements on nuclear operators on general Hausdorff locally convex topological $\mathbf C$-vector spaces, with emphasis on a factorization principle enabling the computation of nuclear traces of nuclear operators equipped with a factorization through a continuous injective linear map between Hausdorff locally convex topological $\mathbf C$-vector spaces. This has appeared before in [Me1, §4, Cor. 4.7, p. 28], and we discuss it here in detail for ease of access.

We will then focus on the case of nuclear operators on Hilbert spaces, and methods to compute their traces. We will first discuss some complements on the strong operator topology (i.e., pointwise convergence) on the $\mathbf C$-algebra of continuous endomorphisms on a Hilbert space, then recall the basic properties of Hilbert-Schmidt and nuclear operators on a Hilbert space and several convergence results of compositions with sequences of orthogonal projectors and more general self-adjoint operators. We include proofs of some of these results for ease of access.

We will then briefly discuss the Schatten-von Neumann classes of index $p=1,2$ for operators between two (possibly distinct) Hilbert spaces. We conclude this section on nuclear operators with a discussion of a special class of nuclear operators: those associated to a measurable integral kernel on Hilbert spaces of the special form $L^2(X,\mu)$, for $X$ a Hausdorff locally compact topological space and $\mu$ a Radon measure on $X$. We will discuss how to “smoothen” their integral kernel along the diagonal, and use that smoothening to compute nuclear traces.

**C.3.1. Preparations.** Let $E,F$ be Hausdorff locally convex topological vector spaces. For Banach $E$, the strong dual $E'_{\beta}$ for $E$ Banach has its topology defined by the dual norm $\|\varphi\|=\sup_{\|x\|\le 1}|\varphi(x)|$. In general there is a canonical continuous linear map

$$
E'_{\beta}\otimes_{\pi}F\to\mathscr{L}_{\beta}(E,F). \tag{C.3.1.1}
$$

The target has the topology of uniform convergence on bounded sets, so for Banach $E$ and $F$ it is the operator-norm topology and so in such cases the target is complete. Thus, for Banach $E$ and $F$, (C.3.1.1) uniquely extends by continuity to a continuous linear map

$$
E'_{\beta}\widehat{\otimes}_{\pi}F\to\mathscr{L}_{\beta}(E,F). \tag{C.3.1.2}
$$

For Banach $E$ and $F$, nuclear maps in $\mathscr{L}_{\beta}(E,F)$ are defined to be those in the range of (C.3.1.2); these have an explicit description as in (C.2.4.2).

Remark C.3.1.1. Beyond the Banach setting there is another class of sufficient conditions for completeness of the target of (C.3.1.1), with a stronger conclusion: if $E$ and $F$ are complete, $E$ is barreled, and $E'_{\beta}$ is nuclear and complete (these hold when $E$ and $F$ are Banach with $E$ nuclear; see [Tre, Prop. 50.6] for the nuclearity of $E'_{\beta}$ when $E$ is nuclear Fréchet), [Tre, Prop. 50.5] gives that the target of (C.3.1.1) is complete and the resulting continuous linear extension in (C.3.1.2) is a topological isomorphism.

To extend the concept of nuclearity for continuous linear maps $T:E\to F$ beyond the Banach setting, consider a convex circled absorbing subset $U\subset E$ (e.g., a convex circled $0$-neighborhood). By the absorbing property, $U$ spans $E$ linearly. The separated completion of the seminormed space $(E,p_U)$, with $p_U:E\to\mathbf R_{\ge 0}$ the Minkowski functional of $U$ from (C.1.2.1), is denoted $\widehat{E}_U$ and is a Banach space.

Given instead a *bounded* convex circled subset $B\subset E$, the linear span $E_B=\cup_{m\ge 1}mB$ of $B$ in $E$ equipped with its Minkowski functional $p_B:E_B\to\mathbf R_{\ge 0}$ is also a normed space (i.e. its semi-normed topology is already separated). If $(E_B,p_B)$ is a Banach space already before completion, we refer to $B$ as a *Banach disc*.

For $E,F$ two locally convex topological $\mathbf C$-vector spaces, a continuous linear operator $T:E\to F$ is termed *nuclear* if and only if there exists a convex circled $0$-neighborhood $U\subset E$ and a Banach disc $B$ in $F$, such that

## PDF page 694

**694** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

$T(U)\subset B$, and the induced linear map $\overline{T}:\widehat{E}_U\to F_B$ is nuclear within $\mathscr{L}(\widehat{E}_U,F_B)$ between Banach spaces; i.e., it is of the form recalled in (C.2.4.2).

Every nuclear operator between two Banach spaces $E,F$ is in particular a limit in the topology of bounded convergence (and so in any coarser $\mathfrak{S}$-topology) of finite-rank operators since (C.3.1.1) is continuous. This holds more generally for nuclear maps between Hausdorff locally convex topological $\mathbf C$-vector spaces, with the explicit description (C.2.4.2) in the Banach case replaced by a mildly generalized description as follows (see [Scha, Ch. III, 7.1, Remark] for a proof):

Lemma C.3.1.2. *Let $E,F$ be Hausdorff locally convex topological $\mathbf C$-vector spaces. A linear map $T\in\mathscr{L}(E,F)$ is nuclear if and only if there exist:*

*(1) a sequence $\{\lambda_n\}_{n\ge 1}\subset\mathbf C$ such that $\sum_{n\ge 1}|\lambda_n|<\infty$,*

*(2) an equicontinuous sequence $\{\varphi_m\}_{m\ge 1}\subset E'$,*

*(3) a sequence $\{x_m\}_{m\ge 1}\subset B$ for a bounded $B$ that is a Banach disc of $F$*

*such that*

$$
T=\sum_{n\ge 1}(\lambda_n\langle\cdot,\varphi_m\rangle_{E,E'})x_m \tag{C.3.1.3}
$$

*as $\mathbf C$-linear operators on $E$. It can be further arranged that $\varphi_m\to 0$ uniformly on some $0$-neighborhood $U\subset E$ and $x_m\to 0$ in $F_B$ (so also $x_m\to 0$ in $F$).*

Sums as on the right side of (C.3.1.3) are always convergent in the topology of uniform convergence on the bounded subsets of $E$. It follows from the lemma that nuclear maps $u$ are compact in the sense that the closure $\overline{u(U)}\subset F$ is compact for some $0$-neighborhood $U\subset E$.

**C.3.2. Nuclear operators picking up their nuclear trace from a subspace.** The following result asserts that nuclear endomorphisms of a Hausdorff locally convex topological $\mathbf C$-vector space with the approximation property have a well-defined trace:

Proposition C.3.2.1. *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. Assume $E$ has the approximation property as in Lemma C.2.4.15. Let $A\in\mathscr{L}(E)$ be a nuclear operator, and let*

$$
A=\sum_{m\ge 0}\lambda_m\langle\cdot,\varphi_m\rangle_{E,E'}x_m \tag{C.3.2.1}
$$

*be a representation for $A$ as in (C.3.1.3). Then the absolutely convergent sum*

$$
\operatorname{Trace}(A):=\sum_{m\ge 0}\lambda_m\langle x_m,\varphi_m\rangle_{E,E'} \tag{C.3.2.2}
$$

*is well posed; i.e., it does not depend on the choices of $\{\lambda_m\}_{m\ge 0}\subset\mathbf C$, $\{\varphi_m\}_{m\ge 0}\subset E'$ and $\{x_m\}_{m\ge 0}\subset E$, but only on $A$.*

*If $T\in\mathscr{L}(E)$ is a linear topological automorphism then $T^{-1}AT$ is nuclear and*

$$
\operatorname{Trace}(A)=\operatorname{Trace}(T^{-1}\circ A\circ T). \tag{C.3.2.3}
$$

Proof. This is [Lit-I, §4.2, Thm. 1] (which uses the approximation property). We now prove the identity in (C.3.2.3). Let $B\subset E$ be a Banach disc containing $\{x_m\}_{m\ge 0}$. Then $T^{-1}(B)\subset E$ is clearly a Banach disc, and since $T^{-1}$ induces a continuous isomorphism $E_B\to E_{T^{-1}(B)}$ with inverse is induced by $T$ (so $E_{T^{-1}(B)}$ is a Banach space).

The set $\{T'(\varphi_m)\}_{m\ge 0}\subset E'$ is clearly equicontinuous. It follows that

$$
T^{-1}\circ A\circ T=\sum_{m\ge 0}\lambda_m\langle\cdot,T'(\varphi_m)\rangle_{E,E'}T^{-1}(x_m)
$$

## PDF page 695

**C.3. NUCLEAR OPERATORS** · **695**

is a nuclear presentation for $T^{-1}\circ A\circ T$ on $E$, and by (C.3.2.2) we have

$$
\begin{aligned}
\operatorname{Trace}(T^{-1}\circ A\circ T) &=\sum_{m\ge 0}\lambda_m\langle T^{-1}(x_m),T'(\varphi_m)\rangle_{E,E'} \tag{C.3.2.4} \\
&=\sum_{m\ge 0}\lambda_m\langle TT^{-1}(x_m),\varphi_m\rangle_{E,E'} \\
&=\sum_{m\ge 0}\lambda_m\langle x_m,\varphi_m\rangle_{E,E'} \\
&=\operatorname{Trace}(A).
\end{aligned}
$$

$\square$

We refer to $\operatorname{Trace}(A)$ as defined in (C.3.2.2) to the *nuclear trace* of $A$. The following result records some stability properties of the nuclear trace of certain nuclear operators.

Lemma C.3.2.2 (Picking up traces through continuous linear injections). *Let $E_1,E_2$ be two Hausdorff locally convex topological $\mathbf C$-vector spaces. Let $A:E_2\to E_2$ be a continuous endomorphism. Assume:*

*(1) $E_1,E_2$ both have the approximation property,*

*(2) there exists an injective continuous operator $T:E_1\to E_2$,*

*(3) there exists a continuous linear operator $A_0:E_2\to E_1$ with $A=T\circ A_0$,*

*(4) $A_0$ is nuclear.*

*Then $A_1:=A_0\circ T:E_1\to E_1$ is nuclear and*

$$
\operatorname{Trace}(A_1)=\operatorname{Trace}(A). \tag{C.3.2.5}
$$

To explain the intuition behind this lemma before we carry out the proof (which uses an argument adapted from [Me1, §4, Cor. 4.7]), we give a commutative diagram summarizing some of the information (with $T$ injective):

```latex
\begin{tikzcd}
E_1 \arrow[r, "T"] \arrow[d, "A_1"'] & E_2 \arrow[d, "A"] \arrow[dl, "A_0" description] \\
E_1 \arrow[r, "T"'] & E_2
\end{tikzcd}
```

Proof. Assume first that $A$ is of finite rank, so $A(E_2)$ is topologically complemented in $E_2$ by [Scha, Ch. II, Cor. 2 to 4.2]. There exist finitely many elements $\{x_1,\ldots,x_N\}\subset A(E_2)\subset T(E_1)\subset E_2$, continuous $\{\varphi_1,\ldots,\varphi_N\}\subset E'_2$, and complex numbers $\lambda_1,\ldots,\lambda_N\in\mathbf C$, such that

$$
A=\sum_{1\le m\le N}\lambda_m\langle\cdot,\varphi_m\rangle_{E_2,E'_2}x_m. \tag{C.3.2.6}
$$

Since $T$ is injective, there therefore exist unique $y_1,\ldots,y_N\in E_1$ such that $T(y_m)=x_m$ for $1\le m\le N$ and we have

$$
T\circ A_1=A\circ T=\sum_{1\le m\le N}\lambda_m\langle\cdot,T'(\varphi_m)\rangle_{E_1,E'_1}x_m=T\left(\sum_m\lambda_m\langle\cdot,T'(\varphi_m)\rangle_{E_1,E'_1}y_m\right), \tag{C.3.2.7}
$$

so

$$
A_1=\sum_{1\le m\le N}\lambda_m\langle\cdot,T'(\varphi_m)\rangle_{E_1,E'_1}y_m.
$$

## PDF page 696

**696** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

Thus,

$$
\begin{aligned}
\operatorname{Trace}(A_1) &=\sum_{1\le m\le N}\lambda_m\langle y_m,T'(\varphi_m)\rangle_{E_1,E'_1} \\
&=\sum_{1\le m\le N}\lambda_m\langle T(y_m),\varphi_m\rangle_{E_2,E'_2} \\
&=\sum_{1\le m\le N}\lambda_m\langle x_m,\varphi_m\rangle_{E_2,E'_2} \\
&=\operatorname{Trace}(A).
\end{aligned}
$$

This means that the identity in (C.3.2.5) holds when $A$ has finite rank.

Since $E_2$ has the approximation property (see Lemma C.2.4.15), we may approximate the map $A_0\in\mathscr{L}(E_2,E_1)$ (obtained as the unique continuous linear $E_2\to E_1$ such that $A=T\circ A_0$) by a net $\{A_k\}_{k\in I}$ in the image of $E_1\otimes E'_2$ with respect to the topology of uniform convergence on pre-compact subsets (see Definition C.2.1.5(2)).

Both nets $A_k\circ T$ and $T\circ A_k$ converge in $\mathscr{L}_{\gamma}(E_1)$, respectively $\mathscr{L}_{\gamma}(E_2)$; i.e., with respect to the topology of uniform convergence on pre-compact subsets. The limit of the former is $A_0\circ T=A_1$, and the limit of the latter is $T\circ A_0=A$, and since $\operatorname{Trace}(A_k\circ T)=\operatorname{Trace}(T\circ A_k)$ by the foregoing, which establishes this identity for every $k\in I$ since $T\circ A_k$ is of finite rank, we have that (C.3.2.5) holds by adapting the method of proof of [Lit-I, §4.2, Thm. 1] (which only considers endomorphisms, rather than intervening maps such as $T$ that are not endomorphisms), as can be done since $A$ and $A_1$ inherit nuclearity from $A_0$ (by [Scha, Ch. III, Cor. 2, to 7.1]) and the topology of uniform convergence on all absolutely convex compact subsets is coarser than the topology of uniform convergence on all pre-compact subsets.

$\square$

**C.3.3. Topologies on the endomorphism algebra of a Hilbert space.** We recall that a Hausdorff locally convex topological complex vector space $E$ is complete if and only if it is complete as a uniform space (every topological vector space has a canonical uniform structure, and it is with respect to this structure that completeness is defined in [Scha, Ch. I, pp. 6-10]), equivalently if and only if every Cauchy net converges to an element of $E$. We further refer the reader to [NB, §3.1] for more on completeness, and to [NB, Thm. 3.1.6] for the dictionary between Cauchy nets and Cauchy filter-bases.

Completeness for a Hausdorff locally convex topological vector space $E$ that is already quasi-complete is a genuinely stronger condition than quasi-completeness. The key issue is that completeness entails every Cauchy net converging to an element of $E$, while quasi-completeness is the condition that any *bounded* Cauchy net is convergent. Cauchy sequences are bounded, but generally not Cauchy nets.

For example, for a Fréchet space $E$ (so it is barreled [Scha, Ch. II, Cor. to 7.1]), the weak topology $E'_{\sigma}$ on $E'$ is quasi-complete by Lemma C.2.1.7 but the topological embedding $E'_{\sigma(E',E)}\hookrightarrow E^*_{\sigma(E^*,E)}$ is identified with the completion (see Lemma C.4.1.2 for a self-contained argument via some literature references). The algebraic dual $E^*$ strictly contains $E'$ when $E$ is infinite-dimensional, so in such cases $E'_{\sigma}$ is quasi-complete but not complete. In *metrizable* locally convex topological vector spaces, it was explained after Definition C.1.3.1 that the concepts of completeness and metric (equivalently sequential) completeness coincide, and these both agree with quasi-completeness because Cauchy sequences in a Hausdorff topological vector space are always bounded.

For $H$ a complex Hilbert space, we denote by $\mathscr{B}(H)$ the $\mathbf C$-vector space of all bounded linear operators on $H$. Recall that the strong operator topology, denoted “SOT”, on $\mathscr{B}(H)$ is the topology of pointwise convergence, generated by the family of seminorms

$$
q_u(T):=\|T(u)\|_H,\ u\in H \tag{C.3.3.1}
$$

## PDF page 697

**C.3. NUCLEAR OPERATORS** · **697**

where $\|\cdot\|_H$ is the norm on $H$. The operator-norm of a bounded linear operator $T:H\to H$ is defined as

$$
\|T\|:=\sup_{u\in H,\|u\|_H\le 1}\|T(u)\| \tag{C.3.3.2}
$$

and promotes $\mathscr{B}(H)$ to a Banach space. We denote it by $\mathscr{B}_{\mathrm{SOT}}(H)$ when endowed with the strong operator topology, and $\mathscr{B}_{\mathrm{NT}}(H)$ when endowed with the operator-norm topology.

Lemma C.3.3.1 (Properties of the strong-operator topology). *Let $H$ be a complex Hilbert space.*

*(1) If $H$ is separable then every bounded subset in $\mathscr{B}_{\mathrm{SOT}}(H)$ is metrizable.*

*(2) $\mathscr{B}_{\mathrm{SOT}}(H)$ is Hausdorff locally convex and quasi-complete.*

Proof. (1) : This is [Cnw-a, Ch. IX, Prop. 1.3(e)], where “bounded” is meant for the norm topology on $\mathscr{B}(H)$, which is the same as boundedness in $\mathscr{B}_{\mathrm{SOT}}(H)$ by [Scha, Ch. III, 3.4].

(2) : The locally convex strong operator topology on $\mathscr{B}(H)$ is clearly Hausdorff. Let $\{T_i\}_{i\in I}$ be a bounded Cauchy net in $\mathscr{B}_{\mathrm{SOT}}(H)$, with $I$ a directed set. Since the evaluation maps $e_{\phi}:\mathscr{B}(H)\to H$ sending $T$ to $e_{\phi}:=T(\phi)$ for every $\phi\in H$ are continuous with respect to the strong operator topology, the net $\{T_i(\phi)\}_{i\in I}$ is Cauchy and hence it converges in $H$ since $H$ is complete. We call $T(\phi)$ the limit in $H$. By the Uniform Boundedness Principle [Scha, Ch. III, Cor. to 4.2], $\sup_{i\in I}\|T_i\|$ is finite. Thus, $T$ is a bounded linear operator on $H$ and $T_i$ converges to $T$ in the strong operator topology by design. This proves that every bounded Cauchy net of $\mathscr{B}_{\mathrm{SOT}}(H)$ converges in $\mathscr{B}_{\mathrm{SOT}}(H)$.

$\square$

We further refer the reader to Remark 4.3.1.6, for more on the topology of $\mathscr{B}_{\mathrm{SOT}}(H)$ specifically, and on topological properties of the topological group of unitary operators on a Hilbert space in the special case $H=L^2(G,\mu)$ for a second-countable Hausdorff locally compact abelian group $G$ and a choice of Haar measure $\mu$ on $G$.

**C.3.4. Trace-class operators on Hilbert spaces.** Hilbert spaces have the approximation property by [Scha, Ch. III, Cor. 1 to 9.2]. Nuclear endomorphisms of a Hilbert space are exactly the trace-class operators (see [Kub, Thm. 6.1]), and serve as a familiar example.

C.3.4.1. *Trace-class operators: definitions and basic properties.* In the special case of Hilbert spaces, we favor the notation $\mathscr{B}_{\mathrm{NT}}(H)$ over $\mathscr{L}_{\beta}(H)$, and $\mathscr{B}_{\mathrm{SOT}}(H)$ over $\mathscr{L}_{\sigma}(H)$, the former being endowed with the norm topology, the latter with the strong operator topology.

Lemma C.3.4.1. *Let $H$ be a Hilbert space. Let $\Sigma$ be an orthonormal basis of $H$. If $T\in\mathscr{B}_{\mathrm{NT}}(H)$ is nuclear (equivalently, trace-class) then:*

*(1) the infinite sum $\sum_{\phi\in\Sigma}|\langle T(\phi),\phi\rangle_H|$ converges;' i.e., $\langle T(\phi),\phi\rangle_H$ vanishes for all but countably many $\phi$, and the sum of the countably many nonzero ones is absolutely convergent.*

*(2) The value of the sum $\sum_{\phi\in\Sigma}|\langle T(\phi),\phi\rangle_H|$ is independent of the choice of $\Sigma$.*

*(3) The value of the absolutely convergent sum $\sum_{\phi\in\Sigma}\langle T(\phi),\phi\rangle_H$ is independent of the choice of $\Sigma$.*

We refer the reader to [Cnw-c, Ch. 3, Prop. 18.9] for the proof of Lemma C.3.4.1. The following is [Cnw-c, Ch. 3, Def. 18.10]:

Definition C.3.4.2. Let $H$ be a Hilbert space, and $T\in\mathscr{B}_{\mathrm{NT}}(H)$ a nuclear operator. We define:

(1) the trace $\operatorname{Trace}(T)$ of $T$ to be the value of the sum $\sum_{\phi\in\Sigma}\langle T(\phi),\phi\rangle_H$ for any choice of orthonormal basis $\Sigma$ of $H$.

(2) The trace-norm of $T$ to be $\|T\|_{\mathrm{Tr}}:=\sum_{\phi\in\Sigma}\langle|T|(\phi),\phi\rangle_H$, where $|T|:=\sqrt{T^*T}$ via the Spectral Theorem for $T^*T$ (finiteness of $\|T\|_{\mathrm{Tr}}$ is the definition of trace-class).

We denote by $\mathrm{N}(H)$ the subspace of $\mathscr{B}_{\mathrm{NT}}(H)$ of nuclear endomorphisms of $H$.

## PDF page 698

**698** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

Lemma C.3.4.1 implies that the concepts defined in Definition C.3.4.2 are well-posed. We will now briefly review their properties, collecting the ones required, below.

Lemma C.3.4.3. *Let $H$ be a Hilbert space, $A$ a compact operator on $H$, $Q\in\mathscr{B}(H)$. Let $\{Q_m\}_{m\ge 0}$ be a sequence of bounded operators on $H$ such that $Q_m\to Q$ in $\mathscr{B}_{\mathrm{SOT}}(H)$. Then $Q_mA\to QA$ with respect to the operator-norm topology, i.e. in $\mathscr{B}_{\mathrm{NT}}(H)$.*

Proof. By [Cnw-a, Ch. II, Thm. 4.4(c)], there exists a sequence $\{A_k\}_{k\ge 0}$ of operators on $H$ of finite rank, such that $\|A_k-A\|\to 0$ as $k\to+\infty$. Let $\varepsilon>0$ and choose $k_0\ge 0$ so large that we have $\|A_k-A\|<\varepsilon/2$ for all $k\ge k_0$.

We have $\|Q_m(A_k-A)\|\le\|Q_m\|\|A_k-A\|$, which is bounded above by $\frac{\varepsilon}{2}\|Q_m\|$ for all $k\ge k_0$. Since $\{Q_m\}_{m\ge 0}\subset\mathscr{B}_{\mathrm{SOT}}(H)$ is a convergent Cauchy sequence, hence bounded, by the Uniform Boundedness Principle there exists a positive real number $L>0$ such that $\sup_{m\ge 0}\|Q_m\|<L$. It follows that we have, for every $k\ge k_0$ and every integer $m\ge 0$:

$$
\|Q_m(A_k-A)\|\le\frac{L\varepsilon}{2}. \tag{C.3.4.1}
$$

We deduce the inequality, for every pair of integers $m,m'\ge 0$ and every $k\ge k_0$:

$$
\|(Q_m-Q_{m'})A\|\le\|(Q_m-Q_{m'})A-(Q_m-Q_{m'})A_k\|+\|(Q_m-Q_{m'})A_k\|\le L\varepsilon+\|(Q_m-Q_{m'})A_k\|. \tag{C.3.4.2}
$$

Being $\varepsilon>0$ arbitrary and independent of $m,m'\ge 0$, it is enough to replace $A$ with $A_{k_0}$, so we are reduced to the case $A$ is of finite rank.

Since $A$ is therefore a finite sum of rank-$1$ operators, we may and do assume $A$ is an operator of rank $1$; i.e., a continuous functional on $H$. Thus, upon choosing $\phi_0\ne 0$ in the range of $A$, there exists a unique $\phi\in H$ such that $A=\langle\phi,\cdot\rangle_H\phi_0$.

We have:

$$
Q_mA=\langle\phi,\cdot\rangle_HQ_m\phi_0
$$

and since $Q_m-Q$ tends to zero with respect to the strong operator topology, we have $Q_m\phi_0\to Q\phi_0$ with respect to the norm topology on $H$, and hence $Q_mA\to QA$ with respect to the operator-norm.

$\square$

Lemma C.3.4.4. *Let $H$ be a Hilbert space. Then:*

*(1) $\mathrm{N}(H)$ is a two-sided ideal of the $\mathbf C$-algebra $\mathscr{B}(H)$, and $\|\cdot\|_{\mathrm{Tr}}$ is a norm on $\mathrm{N}(H)$, promoting $\mathrm{N}(H)$ to a normed space.*

*(2) For any $T\in\mathrm{N}(H)$ and $A\in\mathscr{B}(H)$, we have*

$$
\|AT\|_{\mathrm{Tr}}=\|TA\|_{\mathrm{Tr}}\le\|A\|\|T\|_{\mathrm{Tr}}. \tag{C.3.4.3}
$$

*(3) The linear map $\operatorname{Trace}:\mathrm{N}(H)\to\mathbf C$ satisfies $|\operatorname{Tr}(A)|\le\|A\|_{r}$, so it is continuous with respect to the $\|\cdot\|_{\mathrm{Tr}}$-topology.*

*(4) $\mathrm{N}(H)$ contains the range of $H'\otimes_{\pi}H\to\mathscr{B}_{\mathrm{NT}}(H)$ as a dense linear subspace. In particular, $\mathrm{N}(H)$ is separable as a normed space if $H$ is separable as a Hilbert space.*

*(5) Let $\{P_i\}_{i\in I}\subset\mathscr{B}(H)$ be a net of bounded operators strongly converging to zero. Let $F\in\mathscr{B}(H)$ be a finite-rank operator. Then $\{P_iF\}_{i\in I}$ converges to zero in $\mathrm{N}(H)$, i.e. with respect to the trace-norm topology.*

Proof. Since the concepts of nuclear operator and of trace-class operator are equivalent for endomorphisms of a Hilbert space (see [Kub, Thm. 6.1]), we use the theory of trace-class operators.

(1) : This is [Cnw-c, Ch. 3, Thm. 18.11(a)].

(2) : This is [Cnw-c, Ch. 3, Thm. 18.11(g, e)].

(3) : This is [Cnw-c, Ch. 3, Thm. 18.11(c)] (applied to $T=\mathrm{Id}$).

(4) : This is [Cnw-c, Ch. 3, Thm. 18.11(d)].

## PDF page 699

**C.3. NUCLEAR OPERATORS** · **699**

(5) : Let $m$ be the rank of $F$, and let $\{\alpha_{i,1},\ldots,\alpha_{i,k_i}\}$ be (without multiplicity) the eigenvalues of $|P_iF|$, which is a positive, compact, self-adjoint operator. Note that since $P_iF$ is of finite rank, so is $(P_iF)^*\cdot(P_iF)$, and hence so is its square-root $|P_iF|$. The ranks of each are bounded above by $m$, and hence $k_i\le m$, and each $\alpha_{i,n}$ is a nonnegative real number. We may order the $\alpha_{i,n}$ increasingly, and assume $\alpha_{i,k_i}$ is their maximum. Since $F$ is finite-rank and $P_i\to 0$ in $\mathscr{B}_{\mathrm{SOT}}(H)$, then $P_iF\to 0$ in norm. The norm of each $P_iF$ is $\alpha_{i,k_i}$, and hence the net $\{\alpha_{i,k_i}\}$ tends to zero.

The sum $\sum_{1\le n\le k_i}\alpha_{i,n}$ is the trace-norm of $P_iF$ for each $i\in I$, and since $k_i\le m$ for each $i\in I$, we have $\|P_iF\|_{\mathrm{Tr}}\le m\alpha_{i,k_i}\to 0$, and so $P_iF\to 0$ in $\mathrm{N}(H)$.

$\square$

**C.3.5. Convergence properties of nuclear operators on Hilbert spaces.** The following Proposition enables to reduce trace calculations for nuclear operators on a Hilbert space to calculations on closed subspaces.

Proposition C.3.5.1 (Nuclear convergence of left-compositions with orthogonal projectors). *Let $H$ be a separable Hilbert space, $\{H_i\}_{i\in I}$ a set of nonzero closed subspaces such that for every $i,i'\in I$, with $i\ne i'$, $H_i$ and $H_{i'}$ are orthogonal in $H$, so $I$ is countable.*

*Let $\mathcal{F}_I$ be the countable set of finite subsets of $I$, partially ordered by inclusion.*

*Let:*

$$
P_i:H\to H_i \tag{C.3.5.1}
$$

*be the orthogonal projection operator onto $H_i$. Let $T\in\mathrm{N}(H)$ be a nuclear operator.*

*Assume that the net $\{\sum_{i\in\Sigma}P_i\}_{\Sigma\in\mathcal{F}_I}$ converges in $\mathscr{B}_{\mathrm{SOT}}(H)$ to the identity (i.e., $\widehat{\oplus}H_I=H$).*

*(1) For any cofinal subsequence $\{\Sigma_k\}_{k\ge 0}\subset\mathcal{F}_I$, the sequence*

$$
\{\sum_{i\in\Sigma_k}P_iT\}_{k\ge 0}\subset\mathrm{N}(H) \tag{C.3.5.2}
$$

*converges in $\mathrm{N}(H)$ to $T$, i.e. with respect to the normed topology induced by the trace-norm $\|\cdot\|_{\mathrm{Tr}}$ on $\mathrm{N}(H)$.*

*(2) Let $\{\Sigma_k\}_{k\ge 0}\subset\mathcal{F}_I$ be a cofinal subsequence. The trace of the nuclear operator $T$ is the limit of the sequence of complex numbers:*

$$
\left\{\sum_{i\in\Sigma_k}\operatorname{Trace}(P_iT)\right\}_{k\ge 0}. \tag{C.3.5.3}
$$

Remark C.3.5.2. We observe that given a Hilbert space $H$, a set $I$ and a collection $\{H_i\}_{i\in I}$ of closed subspaces such that for every pair of indeces $i,i'\in I$, with $i\ne i'$, $H_i$ is orthogonal to $H_{i'}$, requiring that the orthogonal projectors $P_i:H\to H_i$ satisfy, upon defining for every finite subset $\Sigma\subset I$, $P_{\Sigma}:=\sum_{i\in\Sigma}P_i$, that the net $\Sigma\mapsto P_{\Sigma}$ on the set of all finite subsets of $I$, converges to the identity with respect to the strong operator topology on $\mathscr{B}(H)$ is equivalent to requiring that $\bigoplus_{i\in I}H_i\subset H$ is dense.

Indeed, for every $\phi\in(\bigoplus_{i\in I}H_i)^{\perp}\subset H$, we have $P_{\Sigma}\phi\to\phi$ in $H$, while $P_{\Sigma}\phi=0$ for every finite subset $\Sigma\subset I$, and hence $\phi=0$. By [Cnw-a, Ch. I, Cor. 2.11], $\bigoplus_{i\in I}H_i$ is dense as a linear subspace of $H$.

Conversely, for any $\phi\in H$, we have $P_{\Sigma}\phi-\phi\in(\bigoplus_{i\in\Sigma}H_i)^{\perp}$, and we may find, by denseness of $\bigoplus_{i\in I}H_i$ in $H$ and [Cnw-a, Ch. I, Cor. 2.11], for each real number $\varepsilon>0$, a large enough finite subset $\Sigma_{\varepsilon}\subset I$ such that $\|P_{\Sigma_{\varepsilon}}\phi-\phi\|_H$ is smaller than $\varepsilon$, which shows that $\{P_{\Sigma}\}_{\Sigma\in\mathcal{F}_I}$ converges in $\mathscr{B}_{\mathrm{SOT}}(H)$ to the identity.

C.3.5.1. *Lemmas on singular values.* Before proving Proposition C.3.5.1, we need two lemmas on singular values.

Lemma C.3.5.3 (Min-Max formulas for singular values). *Let $H$ be a Hilbert space, $A$ a compact operator on $H$. Let $\{\sigma_m(A)\}_{m\ge 1}$ be its sequence of singular values, labelled decreasingly with multiplicity. Then:*

## PDF page 700

**700** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

*(1) For every integer $1\le m\le\dim(H)$, we have $\sigma_m(A)=\sigma_m(A^*)$. (The operator $A^*$ is compact by [Cnw-a, Ch. II, Thm. 4.4(a)].)*

*(2) $\sigma_1(A)=\|A\|$.*

*(3) The following formulas hold for all integers $1\le m\le\dim(H)$:*

$$
\sigma_m(A)=\min_{F\in H_{m-1}}\max_{\phi\in F^{\perp},\|\phi\|_H=1}\|A\phi\|_H=\max_{F\in H_m}\min_{\phi\in F,\|\phi\|_H=1}\|A\phi\|_H \tag{C.3.5.4}
$$

*where $H_m$ is the set of all $m$-dimensional subspaces of $H$.*

Proof. The singular values of $A$ are the eigenvalues of the compact and positive operator $|A|$, which is self-adjoint, being positive on a Hilbert space. We have $\|A\phi\|_H=\||A|\phi\|_H$, and hence we may replace $A$ with $|A|$ in (2) and (3), with (2) contained in (3) as the special case $m=1$.

Since $|A|$ is compact, positive, and self-adjoint, by the Spectral Theorem [Cnw-a, Ch. II, Thm. 5.1, Cor. 5.3] there exists a monotonically decreasing sequence of nonnegative real numbers $\{\lambda_m\}_{m\ge 1}$ tending to $0$ such that upon denoting by $P_m$ the orthogonal projector onto $\ker(\mathbf C e_m)$ for a unit $\lambda_m$-eigenvector $e_m$ of $|A|$, we have

$$
|A|=\sum_{m\ge 1}\lambda_mP_m=\sum_{m\ge 1}\lambda_m\langle\cdot,e_m\rangle_He_m. \tag{C.3.5.5}
$$

The convergence of both sums in (C.3.5.5) is with respect to the operator-norm topology on $\mathscr{B}(H)$.

Let $F\subset\mathbf C$ be a finite-dimensional subspace of dimension $m\le\dim(H)$, and call $V\subset H$ the closure of the linear subspace linearly generated by the $\lambda_{m'}$-eigenspaces for all $m'\ge m$. Then $V$ has co-dimension $m-1$ in $H$, and hence $V\cap F\ne 0$. We let $\phi\in V\cap F$ be a unit vector.

Since $\phi\in V$, then $\langle A\phi,\phi\rangle_H\le\lambda_m$. Indeed, we can write $\phi=\sum_{m'\ge m}c_{m',k}e_{m'}$ for complex numbers $c_{m'}$ such that $\sum_{m'\ge m}|c_{m'}|^2=1$. Then

$$
\langle A\phi,\phi\rangle_H=\left\langle\sum_{m'\ge m}\lambda_{m'}c_{m'}e_{m'},\sum_{m'\ge m}c_{m'}e_{m'}\right\rangle_H=\sum_{m'\ge m}\lambda_{m'}|c_{m'}|^2 \tag{C.3.5.6}
$$

and the right side of (C.3.5.6) is bounded above by $\lambda_m\sum_{m'\ge m}|c_{m'}|^2=\lambda_m$. It follows that

$$
\inf_{\phi\in F,\|\phi\|_H=1}\langle A\phi,\phi\rangle_H\le\lambda_m. \tag{C.3.5.7}
$$

The function $f:H\to\mathbf C$ defined by $f(\phi):=\langle A\phi,\phi\rangle_H$ is weakly continuous, since $A$ is compact. Indeed, for $\{\phi_k\}_{k\ge 0}\subset H$ a sequence converging weakly to $\phi$, so $\{\phi_k\}$ is weakly bounded and hence bounded, we have $A\phi_k\to A\phi$ strongly (this is clear for $A$ of finite rank, and then for general compact $A$ as a uniform limit of finite-rank operators), and so $f(\phi_k)\to f(\phi)$ (since $f(\phi_k)-f(\phi)=\langle A\phi_k-A\phi,\phi_j\rangle_H=\langle A\phi,\phi_k-\phi\rangle_H$); i.e., $f$ is continuous with respect to the $\sigma(H,H^*)$-topology on the source.

By [Cnw-a, Ch. V, Thm. 4.2(d)], the closed unit ball $B$ in $F$ is weakly compact in $H$, so $F\cap B$ is too, so $f$ attains a maximum and a minimum over $F\cap B$. We may therefore replace the infimum in (C.3.5.7) by a minimum.

We deduce that we have, for every integer $m\ge 1$:

$$
\sup_{F\in H_m}\min_{\phi\in F,\|\phi\|_H=1}\langle A\phi,\phi\rangle_H\le\lambda_m. \tag{C.3.5.8}
$$

Upon choosing $F$ to be the span of $e_1,\ldots,e_m$, the value of the the supremum in (C.3.5.7) is $\lambda_m$.

For $A$ replaced by $|A|^2$ and $\lambda_m$ by $\sigma_m(A)^2$, since $\|A\phi\|_H^2=\langle|A|^2\phi,\phi\rangle_H$ we have:

$$
\max_{F\in H_m}\min_{\phi\in F,\|\phi\|_H=1}\|A\phi\|_H^2=\max_{F\in H_m}\min_{\phi\in F,\|\phi\|_H=1}\langle|A|^2\phi,\phi\rangle_H=\sigma_m(A)^2. \tag{C.3.5.9}
$$

## PDF page 701

**C.3. NUCLEAR OPERATORS** · **701**

But $\max_{F\in H_m}\min_{\phi\in F,\lVert\phi\rVert_H=1}\lVert A\phi\rVert_H^2=(\max_{F\in H_m}\min_{\phi\in F,\lVert\phi\rVert_H=1}\lVert A\phi\rVert_H)^2$, as the squaring map on $\mathbf R_{\ge 0}$ is monotonically non-decreasing, so the outer terms in (C.3.5.4) coincide.

The remaining identity in (C.3.5.4) is proved in a similar manner, using the weak continuity of $f$ and the weak compactness of closed and bounded subsets of $H$, to replace the supremum with a maximum over the elements of $\phi\in F^\perp$ satisfying $\lVert\phi\rVert_H=1$. This settles (2) and (3).

It remains to prove (1). We write $A=\sum_{m\ge 1}\sigma_m(A)\langle\cdot,\phi_m\rangle_H\,\psi_m$ for orthonormal sets $\{\phi_m\}_{m\ge 1},\{\psi_m\}_{m\ge 1}$, which can be done by applying [Cnw-a, Ch. II, Cor. 5.4] to $|A|$ and using Polar Decomposition of $A$: the existence of $U\in\mathscr B(H)$ which is isometric on the range of $A$ and zero on its orthogonal, such that $A=U|A|$. Namely, upon defining $\{\phi_m\}_{m\ge 1}$ to be an orthonormal basis for $\ker(|A|)^\perp$ in $H$, diagonalizing $|A|$ as per [Cnw-a, Ch. II, Cor.5.3(b)] with eigenvalues $\sigma_m(A)$ for each $m\ge 1$ respectively, we then define $\psi_m:=U\phi_m$.

Then we have $A^*=\sum_{m\ge 1}\sigma_m(A)\langle\psi_m,\cdot\rangle_H\,\phi_m$. This implies that we have:

$$
AA^*=\sum_{m\ge 1}\sigma_m(A)^2\langle\cdot,\psi_m\rangle_H\,\psi_m
\tag{C.3.5.10}
$$

and hence the singular values $\{\sigma_m(A^*)\}_{m\ge 1}$ of $A^*$ being the nonnegative square roots of the eigenvalues of $AA^*$ are exactly the nonnegative real numbers $\sigma_m(A)$, for each $m\ge 1$ and counted with multiplicity. $\square$

LEMMA C.3.5.4 (Estimates on singular values). *Let $H$ be a Hilbert space. Let $A,B\in\mathscr B(H)$ be bounded endomorphisms of $H$. Assume that $A$ is compact. Then:*

(1) *$AB$ and $BA$ are compact,*

(2) *upon denoting by $\{\sigma_m(A)\}_{m\ge 1},\{\sigma_m(B)\}_{m\ge 1}$ and $\{\sigma_m(BA)\}_{m\ge 1},\{\sigma_m(AB)\}_{m\ge 1}$ the respective sequences of singular values ordered decreasingly, we have:*

$$
\sigma_m(AB)\le\sigma_m(A)\lVert B\rVert,\quad
\sigma_m(BA)\le\sigma_m(A)\lVert B\rVert
\tag{C.3.5.11}
$$

*for every integer $1\le m\le\dim(H)$.*

PROOF. (1) : This is classical: see [Cnw-a, Ch. II, Prop. 4.2(c)].

(2) : By the first of the two formulas in (C.3.5.4) from Lemma C.3.5.3 for the singular values of the compact operators $A,AB,BA$, we have, for each integer $1\le m\le\dim(H)$:

$$
\sigma_m(BA)=\inf_{F\in H_{m-1}}\sup_{\phi\in F^\perp,\lVert\phi\rVert_H=1}\lVert BA\phi\rVert_H
\tag{C.3.5.12}
$$

where $H_{m-1}$ is the set of all $(m-1)$-dimensional $\mathbf C$-linear subspaces of $H$.

Upon fixing $F\in H_{m-1}$, we have:

$$
\sup_{\phi\in F^\perp,\lVert\phi\rVert_H=1}\lVert BA\phi\rVert_H
\le\lVert B\rVert\sup_{\phi\in F^\perp,\lVert\phi\rVert_H=1}\lVert A\phi\rVert_H.
\tag{C.3.5.13}
$$

Passing to the infimum over all $F\in H_{m-1}$, we get:

$$
\sigma_m(BA)=\inf_{F\in H_{m-1}}\sup_{\phi\in F^\perp,\lVert\phi\rVert_H=1}\lVert BA\phi\rVert_H
\le\lVert B\rVert\inf_{F\in H_{m-1}}\sup_{\phi\in F^\perp,\lVert\phi\rVert_H=1}\lVert A\phi\rVert_H
=\sigma_m(A)\lVert B\rVert.
\tag{C.3.5.14}
$$

The analog of the inequality in (C.3.5.14) with $BA$ in place of $AB$ holds too, since $A^*$ is compact:

$$
\sigma_m(AB)=\sigma_m(B^*A^*)\le\lVert B^*\rVert\,\sigma_m(A^*)=\lVert B\rVert\,\sigma_m(A).
\tag{C.3.5.15}
$$

The first and last identities in (C.3.5.15) use Lemma C.3.5.3(1) and that $\lVert B\rVert=\lVert B^*\rVert$. $\square$

We can now prove Proposition C.3.5.1, bearing in mind from [Kub, Thm.6.1] that the concepts of nuclear and trace-class operator on a Hilbert space coincide.

PROOF. (1) : Each $P_iT$ is nuclear since it is of finite rank. We observe that for any *finite* subset $\Sigma\subset I$, the subspace topology on $\bigoplus_{i\in\Sigma}H_i$ is a closed subspace of $H$.

## PDF page 702

**702** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

Upon calling $P_\Sigma:=\sum_{i\in\Sigma}P_i$, then $P_\Sigma$ is itself an orthogonal projector onto $\bigoplus_{i\in\Sigma}H_i$. In particular, it satisfies $\lVert P_\Sigma\rVert\le 1$. By the same token, $\mathrm{Id}-P_\Sigma$ also satisfies $\lVert\mathrm{Id}-P_\Sigma\rVert\le 1$, because $\mathrm{Id}-P_\Sigma$ is itself an orthogonal projector onto $(\oplus H_i)^\perp$.

Since, $T$ and $P_iT$ are compact for every $i\in I$, we deduce that for every integer $m\ge 1$, we have by (C.3.5.11) from Lemma C.3.5.4(2):

$$
0\le\sigma_m(T-P_\Sigma T)\le\lVert\mathrm{Id}-P_\Sigma\rVert\,\sigma_m(T)\le\sigma_m(T)
$$

and since $T$ is nuclear we have by [Cnw-c, Ch. 3, Thm. 18.11(b)] that the series $\sum_{m\ge 1}\sigma_m(T)$ converges (absolutely, since each $\sigma_m(T)$ is nonnegative). By Dominated Convergence, we have:

$$
\lim_{k\to+\infty}\sum_{m\ge 1}\sigma_m(T-P_{\Sigma_k}T)
=\sum_{m\ge 1}\lim_{k\to+\infty}\sigma_m(T-P_{\Sigma_k}T).
\tag{C.3.5.16}
$$

By Lemma C.3.5.3(2), we have $\sigma_m(T-P_{\Sigma_k}T)\le\sigma_1(T-P_{\Sigma_k}T)=\lVert T-P_{\Sigma_k}T\rVert$, and by Lemma C.3.4.3 we have $\lim_{k\to+\infty}\lVert T-P_{\Sigma_k}T\rVert=0$, since $P_{\Sigma_k}\to\mathrm{Id}$ with respect to the strong operator topology, and $T$ is nuclear, hence compact by [Scha, Ch. III, Cor. 1 to 7.1].

By (C.3.5.16), we therefore have:

$$
\lim_{k\to+\infty}\lVert T-P_{\Sigma_k}T\rVert_{\mathrm{Tr}}
=\sum_{m\ge 1}\lim_{k\to+\infty}\sigma_m(T-P_{\Sigma_k}T)=0
\tag{C.3.5.17}
$$

This says the sequence of nuclear operators $\{P_{\Sigma_k}T\}_{k\ge 0}$ converges to $T$ with respect to the topology on $\mathrm N(H)$ induced by the trace-norm.

(2) : The assertions follow from continuity of the trace functional on $\mathrm N(H)$ with respect to $\lVert\cdot\rVert_{\mathrm{Tr}}$, which follows from [Cnw-c, Ch. 3, Thm. 18.11(e)] (with $T=\mathrm{id}_H$). $\square$

COROLLARY C.3.5.5 (SOT-exhaustive filtrations and nuclear convergence). *Let $H$ be a separable Hilbert space. Let $\{H_i\}_{i\ge 1}$ be a countable set of closed linear subspaces such that for every $i'\ge i$ we have $H_i\subset H_{i'}$.*

*Let $T\in\mathrm N(H)$ be a nuclear operator, and $P_i:H\to H_i$ the orthogonal projector onto $H$. Assume $\bigcup_{i\ge 1}H_i$ is dense in $H$. Then:*

(1) *$P_i\to\mathrm{Id}$ with respect to the strong operator topology.*

(2) *The sequences of nuclear operators $\{P_iT\}_{i\ge 1}$ and $\{TP_i\}_{i\ge 1}$ both converge to $T$ with respect to the topology induced by the trace-norm $\lVert\cdot\rVert_{\mathrm{Tr}}$ on $\mathrm N(H)$.*

(3) *We have:*

$$
\lim_{i\to+\infty}\operatorname{Trace}(P_iT)
=\lim_{i\to+\infty}\operatorname{Trace}(TP_i)=\operatorname{Trace}(T).
\tag{C.3.5.18}
$$

PROOF. (1) : For any $\phi\in\bigcup_{i\ge 1}H_i$, there exists $i_0\ge 0$ large enough so as to have $\phi\in H_{i_0}$, and hence we have:

$$
\lim_{i\to+\infty}\lVert(\mathrm{Id}-P_i)\phi\rVert_H^2
=\lim_{i\to+\infty}\langle(\mathrm{Id}-P_i)\phi,\phi\rangle_H=0
\tag{C.3.5.19}
$$

since $(\mathrm{Id}-P_i)\phi$ is orthogonal to $H_{i_0}$ for every $i\ge i_0$.

Let $\phi\in H$ be arbitrary, and fix a real number $\varepsilon>0$. Let $\phi_0\in\bigcup_{i\ge 1}H_i$ be such that $\lVert\phi-\phi_0\rVert<\varepsilon$. There exists an integer $i_0\ge 1$ large enough so as to have $\phi_0\in H_{i_0}$. We have:

$$
\lVert(\mathrm{Id}-P_i)(\phi-\phi_0)+(\mathrm{Id}-P_i)\phi_0\rVert_H
\le\lVert(\mathrm{Id}-P_i)(\phi-\phi_0)\rVert_H+\lVert(\mathrm{Id}-P_i)\phi_0\rVert_H
\tag{C.3.5.20}
$$

with $\lim_{i\to+\infty}\lVert(\mathrm{Id}-P_i)\phi_0\rVert_H=0$ and $\lVert(\mathrm{Id}-P_i)(\phi-\phi_0)\rVert_H\le\lVert\phi-\phi_0\rVert$ since $\lVert\mathrm{Id}-P_i\rVert\le 1$, so

$$
\overline{\lim}_{i\to+\infty}\lVert(\mathrm{Id}-P_i)\phi\rVert_H<\varepsilon.
$$

Since $\varepsilon>0$ is arbitrary, we deduce that

$$
\lim_{i\to+\infty}\lVert(\mathrm{Id}-P_i)\phi\rVert_H=0.
\tag{C.3.5.21}
$$

## PDF page 703

**C.3. NUCLEAR OPERATORS** · **703**

It follows that indeed $P_i\to\mathrm{Id}$ in $\mathscr B_{\mathrm{SOT}}(H)$ as $i\to+\infty$. This settles (1).

Assertion (3) follows from (2) by continuity of the trace functional on $\mathrm N(H)$ with respect to $\lVert\cdot\rVert_{\mathrm{Tr}}$, so it remains to prove (2). We define $Q_0:=P_1$ and $Q_i$ for $i\ge 1$ to be the orthogonal projection operator onto $H_{i+1}\cap H_i^\perp$ in $H$. Since $H_{i+1}=H_i\oplus(H_{i+1}\cap H_i^\perp)$ as Hilbert subspaces of $H$, we have $P_{i+1}=\sum_{0\le m\le i}Q_m$ as elements of $\mathscr B(H)$. By hypothesis $T$ is nuclear, and (by [Kub, Thm.6.1]) nuclear and trace-class operators are equivalent concepts on $\mathscr B(H)$, so $Q_mT$ is nuclear for every $m\ge 0$ by [Cnw-b, Ch. 3, Thm. 18.11(a)]. Hence,

$$
\mathrm{Trace}(P_{i+1}T)=\sum_{0\le m\le i}\mathrm{Trace}(Q_mT)
\tag{C.3.5.22}
$$

for every integer $i\ge 0$.

By Proposition C.3.5.1(1) applied with the projectors $Q_i$, we have $P_{i+1}T=\sum_{0\le m\le i}Q_mT\to T$ with respect to the normed topology on $\mathrm N(H)$ induced by the trace-norm. By Proposition C.3.5.1(2), (C.3.5.18) also holds.

We have

$$
\lVert TP_i-T\rVert_{\mathrm{Tr}}=\sum_{m\ge 1}\sigma_m(TP_i-T)=\sum_{m\ge 1}\sigma_m((TP_i-T)^*)
\tag{C.3.5.23}
$$

by Lemma C.3.5.3(1). Note that since $T$ is compact, by [Cnw-a, Ch. II, Thm. 4.4(b)] so are $TP_i$, $T-TP_i$, and the adjoints $(T-TP_i)^*$, $T^*$, $P_i^*T^*=(TP_i)^*$ for each integer $i\ge 1$. Their singular values are therefore defined, and the Lemma applies to provide the identities in (C.3.5.23).

We likewise see that $(TP_i-T)^*$ is nuclear and its trace-norm agrees with $\lVert TP_{i_k}-T\rVert_{\mathrm{Tr}}$. Thus,

$$
\lVert TP_i-T\rVert_{\mathrm{Tr}}=\sum_{m\ge 1}\sigma_m(P_i^*T^*-T^*)=\sum_{m\ge 1}\sigma_m(P_iT^*-T^*)=\lVert P_iT^*-T^*\rVert_{\mathrm{Tr}}
\tag{C.3.5.24}
$$

where we are using self-adjointness of $P_i$. Since $T^*$ is nuclear, by Proposition C.3.5.3(1) we obtain from the previous case that $\lVert P_iT^*-T^*\rVert_{\mathrm{Tr}}\to 0$ as $i\to+\infty$, so $\lim_{i\to+\infty}\lVert TP_i-T\rVert_{\mathrm{Tr}}=0$. $\square$

**C.3.6. Schatten-von Neumann classes of index $p=1,2$.** In this subsection we continue to discuss nuclear operators on Hilbert spaces, in certain special cases of interest: integral operators acting on $L^2$-spaces of homogeneous spaces.

We let $E,F$ be Hilbert spaces, and denote by $\mathscr K(E,F)$ the $\mathbf C$-linear space of compact operators $T:E\to F$ (namely, $\overline{T(U)}\subset F$ is compact for some 0-neighborhood $U\subset E$). For $H:=E=F$, $\mathscr K(H)$ is an ideal of operators and is closed under the subspace topology inherited from $\mathscr B_{\mathrm N}(H)=\mathscr L_\beta(H)$; i.e., the operator-norm topology (see [Cnw-a, Ch. II, Prop. 4.2(b)]). In general, the formation of $\mathscr K(E,F)$ is compatible with composition of operators on both sides (by the definition). , by [Jar, Part III,Ch.17,§17.1,Prop.1(c)].

Compact operators are characterized as follows:

THEOREM C.3.6.1 (Structure of compact operators on Hilbert spaces). *Let $E,F$ be Hilbert spaces, $T\in\mathscr L(E,F)$. The following conditions on $T$ are equivalent:*

(1) *$T$ is compact.*

(2) *There exist a sequence $\{\lambda_k\}_{k\ge 1}\subset\mathbf R_{\ge 0}$ monotonically decreasing with limit 0 and orthonormal sequences $\{e_k\}_{k\ge 1}\subset E$, $\{f_k\}_{k\ge 1}\subset F$, such that*

$$
T=\sum_{k\ge 1}\lambda_k\langle\cdot,e_k\rangle_E\,f_k
\tag{C.3.6.1}
$$

*where the sum is convergent with respect to the topology of simple convergence.*

*If $T$ is compact, then the sum in (C.3.6.1) converges uniformly on the bounded subsets of $E$; i.e., for the operator norm. The operator-norm of $T$ is $\lambda_1$.*

## PDF page 704

**704** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

PROOF. Passing to the endomorphism of $E\oplus F$ given by

$$
\begin{bmatrix}0&0\\T&0\end{bmatrix}
$$

reduces the implication (1) $\Rightarrow$ (2) with operator-norm convergence to the case $E=F$ that we saw via Polar Decomposition for $T$ and the Spectral Theorem for $|T|$ in the proof of Lemma C.3.5.3(3).

We note that the norm of $Tx$ for each $x\in E$ satisfies

$$
\lVert Tx\rVert_F^2=\sum_{k\ge 0}\lvert\lambda_k\langle x,e_k\rangle_E\rvert^2\le\lvert\lambda_k\rvert\,\lVert x\rVert_E^2
$$

for every $k\ge 1$, and hence $\lVert T\rVert_F\le\lvert\lambda_1\rvert=\lambda_1$. The upper bound is attained upon choosing $x=e_1$.

The operator-norm convergence under the pointwise hypothesis in (2) follows from the inequality $\lVert T-\sum_{1\le k\le N}\lambda_k\langle\cdot,e_k\rangle_E\,f_k\rVert_F\le\lvert\lambda_{N+1}\rvert$. Likewise, (2) implies $T$ is a norm-limit of finite-rank operators, hence compact. $\square$

We further recall the following, concerning the decreasing sequence $\{\lambda_k\}_{k\ge 1}\subset\mathbf R_{\ge 0}$. It is uniquely determined by $T$, and does not depend on the orthonormal sequences $\{e_k\}_{k\ge 0},\{f_k\}_{k\ge 0}$ from Theorem C.3.6.1. This is the content of [Jar, §20.2, Prop. 1]. For $E=F$, the real numbers $\lambda_k$ agree with the singular values of $T$, counted with multiplicity and ordered decreasingly. In general, these are the $n$-*th approximation numbers* given in [Jar, §19.8]. We denote them by $\sigma_k(T)$, for each integer $k\ge 1$. By definition, for any continuous map $T\in\mathscr L(E,F)$,

$$
\sigma_k(T):=\inf\{\lVert A-T\rVert_{\mathscr L_\beta(E,F)}:\dim(\mathrm{Im}(A))\le k-1\}.
\tag{C.3.6.2}
$$

DEFINITION C.3.6.2 (Schatten-von-Neumann classes). Let $E,F$ be Hilbert space spaces. Let $p\ge 1$ be a real number. We define:

(1) *The Schatten-von Neumann class of index $p$ to be the $\mathbf C$-linear subspace:*

$$
S_p(E,F)\subset\mathscr K(E,F)
\tag{C.3.6.3}
$$

of those compact operators such that $\sum_{k\ge 1}\sigma_k(T)^p$ is convergent. We denote by $\lVert\cdot\rVert_{S_p}$ the function on $S_p(E,F)$ defined as

$$
\lVert T\rVert_{S_p}:=\left(\sum_{k\ge 1}\sigma_k(T)^p\right)^{1/p}.
\tag{C.3.6.4}
$$

(2) The space of Hilbert-Schmidt operators $E\to F$, to be the $S_2(E,F)$.

(3) The space of trace-class operators $E\to F$, to be $S_1(E,F)$.

We record here a generalization of Lemma C.3.5.4 for singular values of continuous operators $E\to F$ when $E$ and $F$ are general Hilbert spaces, allowing $E\ne F$.

LEMMA C.3.6.3 (Compositions and singular values). *Let $E,F,G$ be Hilbert spaces, and $m,n\ge 1$ be integers. We have:*

(1) *$\sigma_m(A+B)\le\sigma_m(A)+\sigma_m(B)$, for any $A,B\in\mathscr L(E,F)$.*

(2) *$\lvert\sigma_m(A)-\sigma_m(B)\rvert\le\lVert A-B\rVert_{\mathscr L_\beta(E,F)}$, for any $A,B\in\mathscr L(E,F)$.*

(3) *$\sigma_{m+n}(AB)\le\sigma_m(A)\sigma_n(B)$, for any $A\in\mathscr L(F,G)$, $B\in\mathscr L(E,F)$.*

PROOF. This is [Jar, §19.8, Prop. 1]. $\square$

## PDF page 705

**C.3. NUCLEAR OPERATORS** · **705**

C.3.6.1. *Nuclear, Hilbert-Schmidt and compact operators as topological tensor products.* For $X,Y$ two Hausdorff locally compact second countable topological spaces, and $\mu,\nu$ two Radon measures on $X$, respectively $Y$,

$$
S_2(L^2(X,\mu),L^2(Y,\nu))=L^2(X\times Y,\mu\otimes\nu)
\tag{C.3.6.5}
$$

i.e. every Hilbert-Schmidt operator $T:L^2(X,\mu)\to L^2(Y,\nu)$ is obtained by integration against a kernel function $k\in L^2(X\times Y,\mu\otimes\nu)$:

$$
(T\phi)(y)=\int_X k(x,y)\phi(x)\,\mathrm{d}\mu(x)
\tag{C.3.6.6}
$$

for almost all $y\in Y$. The typical example we will be encountering throughout this work, for $S_p(E,F)$, is the cases $p=1,2$ and for $E=L^2(X,\mu)$, $F=L^2(Y,\nu)$.

We will need the following:

PROPOSITION C.3.6.4. *Let $E,F$ be Hilbert spaces, $p\ge 1$ a real number. Then:*

(1) *the canonical injective linear map:*

$$
\chi:E'\otimes F\to\mathscr L(E,F)
\tag{C.3.6.7}
$$

*uniquely determined by $\phi\otimes f\mapsto\phi\cdot f$, is valued in $S_p(E,F)$ for every $p\ge 1$.*

(2) *The subspace topology induced on $E'\otimes F$ by $\lVert\cdot\rVert_{S_2}$ is equivalent to the linear topology induced by the inner product structure on $E'\otimes F$ uniquely determined on elementary tensors by:*

$$
\langle\varphi_1\otimes f_1,\varphi_2\otimes f_2\rangle_\sigma:=\langle\varphi_1,\varphi_2\rangle_{E'}\,\langle f_1,f_2\rangle_F.
\tag{C.3.6.8}
$$

*Upon denoting by:*

$$
E'\widehat\otimes_\sigma F
\tag{C.3.6.9}
$$

*the completion of $E'\otimes F$ with respect to the normed topology induced by the norm $\lVert\cdot\rVert_\sigma$ associated to the inner product assigned by (C.3.6.8), the continuous linear map $E'\widehat\otimes_\sigma F\to S_2(E,F)$ is an isometry.*

(3) *The injective linear map $\chi$ from (C.3.6.7) extends by continuity with respect to both the projective and injective tensor product topologies, and the continuous linear operators $\chi_\pi:E'\widehat\otimes_\pi F\to\mathscr L(E,F)$ and $\chi_\varepsilon:E'\widehat\otimes_\varepsilon F\to\mathscr L(E,F)$ obtained by continuous extension are linear isometries onto $S_1(E,F)$, respectively $\mathscr K(E,F)$.*

PROOF. (1) : This is clear since the image consists of finite-rank maps.

(2) and (3) : This is a consequence of the definitions. Upon denoting by $\lVert\cdot\rVert_\sigma$ the norm on $E'\otimes F$ induced by the inner product $\langle\cdot,\cdot\rangle_\sigma$ assigned in (C.3.6.8), $\lVert\cdot\rVert_\sigma$ is a “reasonable tensor norm” in the sense of [Ryan, §6.1,p.127], so its norm-topology on $E'\otimes F$ is finer than the $\varepsilon$-topology and weaker than the $\pi$-topology (see [Ryan, Prop. 6.1(a)]). The completion of $E'\otimes F$ with respect to the $\varepsilon$-topology is isometric to the closure in $\mathscr L_\beta(E,F)$ of $\chi(E'\otimes F)$, which is $\mathscr K(E,F)$ since Hilbert spaces have the metric Approximation Property (see [Ryan, Cor. 4.13]).

That $\chi_\pi$ is an isometry onto $S_1(E,F)$ is the content of [Ryan, Prop. 7.24] for $p=1$ (see also [Ryan, Prop. 6.6(c)]). $\square$

C.3.6.2. *Closure properties of Schatten-von Neumann classes.* We collect here generalizations of Proposition C.3.5.1 and Corollary C.3.5.5, for the Schatten-von Neumann ideals $S_p(E,F)$, with $E,F$ Hilbert spaces.

PROPOSITION C.3.6.5 (Closure properties of Schatten-von Neumann classes). *Let $E,F$ be Hilbert spaces. Let $p\ge 1$ be a real number. Pick $A\in S_p(E,F)$ and let $\{B_k\}_{k\ge 0}\subset\mathscr L(E)$ and $\{C_j\}_{j\ge 0}\subset\mathscr L(F)$ be sequences of continuous operators converging strongly (i.e., pointwise) to $B\in\mathscr L(E)$ respectively $C\in\mathscr L(F)$.*

## PDF page 706

**706** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

*Assume that $B_k$ is self-adjoint for each $k\ge 0$ (so $B=B^*$). Then the following sequences:*

$$
\{C_jA\}_{j\ge 0},\{AB_k\}_{k\ge 0},\{C_jAB_k\}_{j,k\ge 0}
\tag{C.3.6.10}
$$

*converge respectively in $S_p(E,F)$ to $CA$ as $j\to\infty$, $AB$ as $k\to\infty$, and $CAB$ as $j,k\to\infty$ together.*

PROOF. Assume first that $A$ is of finite rank $N\ge 0$. We may write

$$
A=\sum_{1\le r\le N}\lambda_r\langle\cdot e_r\rangle_E\,f_r
\tag{C.3.6.11}
$$

for positive real numbers numbers $\lambda_1,\dots,\lambda_N\le\lVert A\rVert$, and sets of unit vectors $\{e_r\}_{1\le r\le N}\subset E$ and $\{f_r\}_{1\le r\le N}\subset F$.

We have:

$$
C_jA=\sum_{1\le r\le N}\lambda_r\langle\cdot,e_r\rangle_E\,C_jf_r,\ AB_k=\sum_{1\le r\le N}\lambda_r\langle\cdot,B_k^*e_r\rangle_E\,f_r,\ C_jAB_k=\sum_{1\le r\le N}\lambda_r\langle\cdot,B_k^*e_r\rangle_E\,C_jf_r.
\tag{C.3.6.12}
$$

Since $B_k$ is self-adjoint for each $k\ge 0$, we have $B_k^*=B_k$. Since $B_k\to B$ and $C_k\to C$ strongly, we deduce $B_k^*e_r\to Be_r$ and $C_jf_r\to Cf_r$, and we claim $C_jA\to CA$, $AB_k\to AB$, and $C_jAB_k\to CAB$ within $S_p(E,F)$; i.e., with respect to the topology on $S_p(E,F)$ induced by the norm $\lVert\cdot\rVert_{S_p}$ from (C.3.6.4). Indeed, we have:

$$
\lVert C_jA-CA\rVert_{S_p}\le\sum_{1\le r\le N}\lvert\lambda_r\rvert\lVert C_jf_r-C_jf_r\rVert_F,\ \lVert AB_k-AB_k\rVert_{S_p}\le\sum_{1\le r\le N}\lvert\lambda_r\rvert\lVert B_ke_r-Be_r\rVert_E
\tag{C.3.6.13}
$$

where we have used the triangle inequality for $\lVert\cdot\rVert_{S_p}$, which follows from Lemma C.3.6.3(1) combined with $\sigma_m(\langle\cdot,e_r\rangle_E\,C_jf_r)=0=\sigma_m(\langle\cdot,B_k^*e_r\rangle_E\,f_r)$ for $m>1$ (see [Jar, §19.8, Prop. 2] for $n=1$), which gives $\lVert\langle\cdot,e_r\rangle_E\,(C_jf_r-Cf_r)\rVert_{S_p}=\lVert\langle\cdot,e_r\rangle_E\,(C_jf_r-Cf_r)\rVert\le\lVert C_jf_r-Cf_r\rVert$, and $\lVert\langle(B_k^*e_r-B_k^*e_r,\cdot\rangle_E\,f_r\rVert\le\lVert B_ke_r-Be_r\rVert$. The inequalities in (C.3.6.13) imply that we have $C_jA\to CA$ and $AB_k\to AB$ in $S_p(E,F)$.

For any $j,k\ge 0$ we have

$$
\lVert C_jAB_k-CAB\rVert_{S_p}\le\lVert C_jAB_k-CAB_k\rVert_{S_p}+\lVert CAB_k-CAB_k\rVert_{S_p}\le\lVert C_jA-CA\rVert_{S_p}\sup_{i\ge 0}\lVert B_k\rVert+\lVert CAB_k-CAB_k\rVert_{S_p}
\tag{C.3.6.14}
$$

where we used the inequality $\lVert C_jAB_k-CAB_k\rVert_{S_p}\le\lVert C_jA-CA\rVert_{S_p}\lVert B_k\rVert$ by (C.3.5.11) and Lemma C.3.6.3(2). Finiteness of $\sup_{k\ge 0}\lVert B_k\rVert$ holds by the Uniform Boundedness Principle since $B_k\to B$ strongly and $\mathscr B_{\mathrm{SOT}}(E)$ is Hausdorff.

We conclude that $\lVert C_jAB_k-CAB\rVert_{S_p}\to 0$ as $j,k\to\infty$ together, which proves the Proposition in case $A$ is of finite rank.

We now discuss the general case. By [Jar, §19.8, Thm.3], for every real number $\varepsilon>0$ there exists a finite rank operator $A_0\in\mathscr L(E,F)$ such that $\lVert A-A_0\rVert_{S_p}\le\varepsilon$. We have:

$$
\lVert C_jA-CA\rVert_{S_p}\le\lVert C_jA_0-CA_0\rVert_{S_p}+(\lVert C_j\rVert+\lVert C\rVert)\,\lVert A-A_0\rVert_{S_p}<\lVert C_jA_0-CA_0\rVert_{S_p}+(\lVert C_j\rVert+\lVert C\rVert)\,\varepsilon.
\tag{C.3.6.15}
$$

Since $C_j\to C$ strongly and $\mathscr B_{\mathrm{SOT}}(F)$ is Hausdorff, we have that $\sup_{j\ge 0}\lVert C_j\rVert$ is finite by the Uniform Boundedness Principle.

We deduce from (C.3.6.15) and the settled case of finite-rank operators that

$$
\overline{\lim}_{j\to+\infty}\lVert C_jA-CA\rVert_{S_p}\le(\sup_{j\ge 0}\lVert C_j\rVert+\lVert C\rVert)\,\varepsilon.
\tag{C.3.6.16}
$$

Since $\varepsilon>0$ is arbitrary, we deduce that $C_jA\to CA$ in $S_p(E,F)$.

Likewise

$$
\lVert AB_k-AB\rVert_{S_p}\le\lVert A_0B_k-A_0B_k\rVert_{S_p}+(\lVert B_k\rVert+\lVert B\rVert)\,\lVert A-A_0\rVert_{S_p}\le\lVert A_0B_k-A_0B\rVert_{S_p}+(\lVert B_k\rVert+\lVert B\rVert)\,\varepsilon.
\tag{C.3.6.17}
$$

## PDF page 707

**C.3. NUCLEAR OPERATORS** · **707**

That $\sup_{k\ge 0}\lVert B_k\rVert$ is finite was noted earlier. We deduce from (C.3.6.17) that

$$
\overline{\lim}_{k\to+\infty}\lVert AB_k-AB\rVert_{S_p}\le(\sup_{k\ge 0}\lVert B_k\rVert+\lVert B\rVert)\,\varepsilon.
\tag{C.3.6.18}
$$

Since $\varepsilon>0$ is arbitrary, $AB_k\to AB$ in $S_p(E,F)$.

Finally,

$$
\lVert C_jAB_k-CAB\rVert_{S_p}\le\lVert C_jAB_k-CAB_k\rVert_{S_p}+\lVert CAB_k-CAB\rVert_{S_p}\le\lVert C_jA-CA\rVert_{S_p}\sup_{k\ge 0}\lVert B_k\rVert+\lVert CAB_k-CAB\rVert_{S_p}
\tag{C.3.6.19}
$$

where we used the inequality $\lVert C_jAB_k-CAB_k\rVert_{S_p}\le\lVert C_jA-CA\rVert_{S_p}\lVert B_k\rVert$ explained already. and finiteness of $\sup_{k\ge 0}\lVert B_k\rVert$ noted already. We deduce from (C.3.6.19) that $\lVert C_jAB_k-CAB\rVert_{S_p}\to 0$ as $j,k\to\infty$ together. $\square$

REMARK C.3.6.6. For $p=1$, Proposition C.3.6.5 contains Proposition C.3.5.1 and Corollary C.3.5.5 as a special case. Indeed, for any cofinal sequence $\{\Sigma_k\}_{k\ge 0}\subset\mathcal F_I$ as in Proposition C.3.6.5(2), we may call $C_k:=\sum_{i\in\Sigma_k}P_i$ and $A:=T$, to obtain Proposition C.3.5.1 from Proposition C.3.6.5.

Corollary C.3.5.5 is obtained from Proposition C.3.6.5 upon choosing $B_k:=P_{i_k}$, a self-adjoint operator converging to the identity strongly by assumption.

**C.3.7. Integral kernels.** We further recall here a result describing a class of examples of nuclear operators, and how to compute their trace. For $X$ a Hausdorff locally compact second-countable topological space, and $\mu$ a Radon measure on $X$, we consider the Hilbert space $L^2(X,\mu)$ of $\mu$-measurable square $\mu$-integrable functions on $X$, topologized with the $L^2$-norm topology.

A nuclear operator $A$ on $E:=L^2(X,\mu)$ is, in particular, Hilbert-Schmidt (see [Cnw-c, Prop.18.8(c)]); i.e., $A\in S_p(E)$ for $p=1,2$, and it therefore corresponds to a unique element of $E'\widehat\otimes_\sigma E$ (see Proposition C.3.6.4) which, since $E'\widehat\otimes_\sigma E$ is isometric to $L^2(X\times X,\mu\otimes\mu)$, corresponds to a unique $(\mu\otimes\mu)$-measurable function $k(x,y)\in L^2(X\times X,\mu\otimes\mu)$ such that the effect of $A$ on $\phi\in L^2(X,\mu)$ is by convolution, i.e. we have

$$
(A\phi)(x)=\int_X k(x,y)\phi(y)\,\mathrm{d}\mu(y)
$$

as $\mu$-measurable and square $\mu$-integrable functions on $X$.

Characterizing nuclearity of $A$ in terms of the integral kernel $k$ is a non-trivial task. In the special case $A$ is positive, this is indeed possible. Using an analog of the Hardy-Littlewood Maximal Theorem and an analog of Lebesgue's Differentiation Theorem (for which we refer the reader to the discussion in §A.5.1 and §A.5.2, §A.5.3 and §A.5.4 of Appendix A.5 in the special case $X=G$ is a Hausdorff locally compact abelian group equipped with a $D'$-sequence, which serves the same purpose of the open balls in Euclidean spaces through the proof of the inequalities of the Maximal Theorem, and their application to the Differentiation Theorem), which the reader will find discussed in an axiomatized manner using martingales in [Bris-a, §2, pp. 231-2], and in [Bris-b, §2, p. 1182] in the case of Euclidean spaces (and more general subsets of Euclidean spaces), we can “smoothen” the kernel function $k(x,y)$ along the diagonal in $X\times X$ (which is a $(\mu\otimes\mu)$-null set, on whose points the kernel function may be undefined), to define a new $\mu$-measurable function $\widetilde k(x,x)$ out of $k(x,y)$. It turns out (see [Bris-a, Thm. 4.2, p. 238]) that $A$ is nuclear if and only if $\widetilde k(x,x)$ is absolutely $\mu$-integrable as a $\mu$-measurable function of $x\in X$ defined $\mu$-almost everywhere.

Beyond the case of positive operators this characterization breaks down, as illustrated by means of an example (see [Bris-b, Example 3.2, p. 1186] for the well known example of the Volterra operator on $L^2([0,1],\lambda)$, with $\lambda$ the normalized Lebesgue measure on $\mathbf R$, which is a Hilbert-Schmidt operator whose kernel has an absolutely integrable smoothening along the diagonal).

It is always possible to factorize a nuclear operator on a Hilbert space as the composition of two Hilbert-Schmidt operators, and it turns out that the convolution of their own Hilbert-Schmidt kernels makes sense along the diagonal (i.e., away from a subset of the diagonal of $\mu$-measure zero, it agrees with the smoothening

## PDF page 708

**708** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

of the kernel function associated to the nuclear operator itself, viewed as a Hilbert-Schmidt operator; see [Bris-a, Thm. 3.3, p. 238]).

This observation is used, for example, in [Arthur, §3,Lemma 3.8,p.353] (where the kernels $H'$ and $H''$ are Hilbert-Schmidt kernels, whose convolution is the kernel $H$ whose associated operator is nuclear and whose trace is being computed in the Lemma) in the process of proving instances of the classical Arthur-Selberg trace formula.

If the operator $A$ is assumed to be nuclear, then the smoothening of its Hilbert-Schmidt kernel along the diagonal (in whichever way it is computed, whether through Lebesgue's Differentiation or by convolution of two factor Hilbert-Schmidt kernels) can be used to compute its nuclear trace. This is an important result, which generalizes a classical Theorem of Mercer (see [Bris-b, Prop. 1.2, p. 1182]) asserting that when the Hilbert-Schmidt kernel of the nuclear operator $A$ is continuous as a function of $(x,y)\in X\times X$ then its integral along the diagonal as a function of $(x,x)$ and with respect to the Radon measure $\mu$ on $X$ equals the nuclear trace of $A$.

THEOREM C.3.7.1 (Trace formula for integral nuclear operators). *Let $X$ be a Hausdorff locally compact second countable topological space, $\mu$ a Radon measure on $X$. Let $k\in L^2(X\times X,\mu\otimes\mu)$ be a square-integrable function. Then:*

(1) *the integral operator:*

$$
(T\phi)(x):=\int_X k(x,y)\phi(y)\,\mathrm{d}\mu(y)
\tag{C.3.7.1}
$$

*is Hilbert-Schmidt, with Hilbert-Schmidt norm given by $\lVert k\rVert_{L^2(X\times X,\mu\otimes\mu)}$.*

(2) *Assume $T$ is nuclear. Then:*

*(a) if $k(x,y)$ is continuous almost everywhere along the diagonal in $X\times X$ then it is absolutely integrable and*

$$
\mathrm{Trace}(T)=\int_X k(x,x)\,\mathrm{d}\mu(x).
\tag{C.3.7.2}
$$

*(b) The kernel function $k(x,y)$ admits a smoothening $\widetilde k(x,x)$ along the diagonal such that the trace formula in (C.3.7.2) holds with $\widetilde k(x,x)$ replacing $k(x,x)$.*

We refer to [Bris-a, Cor. 3.2, pp. 237] for a proof of Theorem C.3.7.1(2.a), and to [Bris-a, Thm. 3.1, p. 235] for a proof Theorem C.3.7.1(2.b).

Throughout the trace calculation that is the main focus of this work, we will be showing how to define the smoothening of the appropriate integral kernel directly, using the analogs of the Hardy-Littlewood Maximal Theorem and Lebesgue's Differentiation Theorem discussed in Appendix A.5 to avoid necessitating the reader to familiarize themself with martingales and their use in [Bris-a].

**C.4. Integration in the sense of Pettis**

One essential tool to analyze holomorphic scalar-valued functions is contour integration. We now discuss its counterpart for vector-valued functions, with a view towards the applications of interest, with values in a locally convex space that is generally not Banach. We have selected the integral in the sense of Pettis, and we will be collecting the necessary foundations throughout this section. The material in this section will be used for integration of certain linear operators varying continuously over a Hausdorff locally compact abelian topological group.

All locally convex topological vector spaces throughout this section will be Hausdorff and over the complex numbers.

## PDF page 709

**C.4. INTEGRATION IN THE SENSE OF PETTIS** · **709**

**C.4.1. Weak completion.** We begin by recalling a few facts about the relation of a Hausdorff locally convex topological $\mathbf C$-vector space $E$, and the algebraic dual $(E')^*$ of its continuous dual $E'$.

The algebraic dual of a complex vector space $V$ is simply the complex vector space $V^*$ of all $\mathbf C$-linear forms on it. If $V$ and $W$ are two such spaces equipped with a bilinear pairing

$$
\langle\cdot,\cdot\rangle:V\times W\to\mathbf C
$$

yielding linear *injections* $V\hookrightarrow W^*$ and $W\hookrightarrow V^*$ then we say “$V$ and $W$ are in duality” and write $\langle V,W\rangle$ to denoted this data (as in [Scha, Ch. IV, §1]).

We recall that on a Hausdorff locally convex topological complex vector space $E$, we find the locally convex weak topology $\sigma(E,E')$ generated by the family of seminorms

$$
q_\varphi:E\to\mathbf R_{\ge 0}
$$

defined by $q_\varphi(u):=\lvert\varphi(u)\rvert$ as $\varphi$ varies over $E'$. By the Hahn-Banach Theorem, $\sigma(E,E')$ is Hausdorff. We sometimes refer to the given topology on $E$ as the *initial topology*, as in [Bou-TVS, p. IV.4] (where $\sigma(E,E')$ is referred to as the *weakened topology* on $E$).

Among the Hausdorff locally convex topologies $\mathscr T$ on $E$, a special class are those for which $E'$ is the subspace of $E^*$ consisting of $\mathscr T$-continuous linear functionals; these are called *polar topologies*, or *consistent* with the pairing between $E$ and $E'$. The weak topology is polar, as is the *Mackey topology* $\tau(E,E')$ defined as the topology of uniform convergence in $E$ on the weakly-compact convex circled subsets in $E'$. Among the topologies such that the continuous dual of $E$ remains $E'$, $\sigma(E,E')$ is the coarsest and $\tau(E,E')$ the finest (and the initial topology sits between them); see [Scha, Ch. IV, §3-§4] for more on such topologies. We will now look into $\sigma(E,E')$ more closely.

Given a locally convex topological complex vector space $E$, there exists a canonical $\mathbf C$-linear map

$$
\iota_E:E\to(E')^*
\tag{C.4.1.1}
$$

sending $u\in E$ to the $\mathbf C$-linear form $\iota_E(u)$ on $(E')^*$ taking a continuous linear form $\varphi\in E'$ to $\varphi(u)$. This is injective by the Hahn-Banach Theorem [Scha, Ch. III, Cor. 1 to 4.2].

The map $\iota_E$ enjoys the following naturality property:

LEMMA C.4.1.1. *Let $E,E_1,E_2$ be Hausdorff locally convex topological $\mathbf C$-vector spaces. Then $\iota_E$ from (C.4.1.1) is injective and the $\sigma((E')^*,E')$-topology on $(E')^*$ induces the $\sigma(E,E')$-topology on $E$ as the subspace topology. Moreover:*

(1) *The $\mathbf C$-linear injection $\iota_E:E\to(E')^*$ is continuous with respect to the initial topology on the source and the $\sigma((E')^*,E')$-topology on the target.*

(2) *For any continuous $\mathbf C$-linear operator $T:E_1\to E_2$, the algebraic dual map $T^*:E_2^*\to E_1^*$ restricts to a $\mathbf C$-linear map $T':E_2'\to E_1'$ and this is continuous with respect to the $\sigma(E_2',E_2)$-topology on the source and the $\sigma(E_1',E_1)$-topology on the target. Moreover, the algebraic dual $(T')^*:(E_1')^*\to(E_2')^*$ of the topological dual $T'$ is continuous with respect to $\sigma((E_1')^*,E_1')$ and $\sigma((E_2')^*,E_2')$, and the following diagram*

(C.4.1.2)

```latex
\begin{tikzcd}
E_1 \arrow[r, "T"] \arrow[d, "\iota_{E_1}"'] & E_2 \arrow[d, "\iota_{E_2}"] \\
(E_1')^* \arrow[r, "(T')^*"'] & (E_2')^*
\end{tikzcd}
```

*commutes.*

PROOF. Assertion (1) is a matter of unraveling definitions (continuity even holds using $\sigma(E,E')$ on $E$). Then (2) is also definition-chasing. $\square$

## PDF page 710

**710** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

LEMMA C.4.1.2. *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. The completion of $E$ with respect to the $\sigma(E,E')$-topology is isomorphic to $(E')^*$. Moreover:*

(1) *If $C\subset E$ is convex then its closure in $E$ for the given topology is the same as for $\sigma(E,E')$, and if that closure is compact for the given topology on $E$ then it is also the closure in $(E')^*$ for $\sigma((E')^*,E')$.*

(2) *If $E$ is a normed space then the linear map $\iota_E:E\to(E')^*$ in (C.4.1.1) factors through the natural embedding $c_E:E\to E'':=(E'_\beta)'$ that is isometric, where $E'$ is equipped with the usual dual-norm topology.*

The dual-norm topology on $E'$ in (2) is familiar from the theory of Banach spaces (applied to $\widehat E$ whose topological dual agrees with $E'$) and agrees with the strong-dual topology $\beta(E',E)$ of convergence on bounded (or equivalently weakly bounded) subsets of $E$; see [Scha, p. 142].

PROOF. Density of $E$ in $(E')^*$ with respect to $\sigma((E')^*,E')$ holds by [Scha, Ch. IV, 1.3] (with $G=(E')^*$, $F=E'$ the notation there). Completeness of $(E')^*$ with respect to $\sigma((E')^*,E')$ is [NB, Thm. 8.2.9].

(1) : The closure assertions follow from [Scha, Ch. IV, 3.1] (with $F=E$, $G=E'$ there), and for the compactness aspect use that $\sigma((E')^*,E')|_E=\sigma(E,E')$ and that $\sigma((E')^*,E')$ is Hausdorff.

(2) : The map $\iota_E$ factors as a linear map through $c_E:E\to E''$ as explained near the start of [Bou-TVS, Ch. IV, §1, p. IV.14], and by [Bou-TVS, Ch. IV, §1, Prop.8(i)] it is an isometric embedding. $\square$

REMARK C.4.1.3. The locally convex topological complex vector space $(E')^*$ with the topology $\sigma((E')^*,E')$ is referred to as the *weak completion* of $E$ in [Gro-a, §2].

**C.4.2. Vector-valued measurable and integrable functions.** We recall that for a complex Borel measure $\mu$ on a locally compact Hausdorff space $X$, $\mu$ is a Radon measure if and only if the total variation $\lvert\mu\rvert$ of $\mu$ is a Radon measure (see [Fol, Thm. 7.16]). Moreover, $\lVert\mu\rVert:=\lvert\mu\rvert(X)$ is a norm on the complex vector space of complex bounded Radon measures on $X$. For $X$ that is also second-countable, every complex Borel measure finite on compact subsets is Radon by [Fol, Thm. 7.8].

DEFINITION C.4.2.1. Let $X$ be a locally compact Hausdorff space and $\mu$ a Radon measure on $X$. Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space and $f:X\to E$ a function. We say

(1) $f$ is *weakly measurable* if and only if for every $\varphi\in E'$, the function $\varphi\circ f:X\to\mathbf C$ is $\mu$-measurable.

(2) $f$ is *weakly $\mu$-integrable* if and only if it is weakly measurable and for every $\varphi\in E'$, $\varphi\circ f:X\to\mathbf C$ is $\mu$-integrable. For a weakly $\mu$-integrable function $f:X\to E$, we denote by $\int_X f\,\mathrm{d}\mu$ the unique element of $(E')^*$ defined by

$$
\left\langle\int_X f\,\mathrm{d}\mu,\varphi\right\rangle_{(E')^*,E'}:=\int_X\langle f(x),\varphi\rangle_{E,E'}\,\mathrm{d}\mu(x),\ \varphi\in E'.
\tag{C.4.2.1}
$$

In other words, $\int_X f\,\mathrm{d}\mu\in(E')^*$ is $\varphi\mapsto\int_X(\varphi\circ f)\mathrm{d}\mu$ by definition.

(3) $f$ is *$\mu$-integrable, or integrable in the sense of Pettis,* if and only if it is weakly $\mu$-integrable (so in particular weakly $\mu$-measureable) and the $\mathbf C$-linear form $\int_X f\,\mathrm{d}\mu$ on $E'$ defined in (C.4.2.1) is in the image of the canonical $\mathbf C$-linear injection $\iota_E:E\to(E')^*$. We denote by $\int_X f\,\mathrm{d}\mu$ again the unique element of $E$ that maps to the linear form on $E'$ from (C.4.2.1) under $\iota_E$, if any.

REMARK C.4.2.2. When $E$ is a Banach space, there is Bochner's theory of $E$-valued integration that can be developed in a style similar to scalar-valued integration, as is done for example in [Lang-d, Ch. VI]. Any $f:X\to E$ that is integrable in the sense of Bochner is also integrable in the sense of Pettis with the same value for $\int_X f \mathrm{d}\mu\in E$, since the formation of the Bochner integral commutes with continuous linear mappings $E\to F$ (such as a continuous linear functional $E\to\mathbf C$).

The relation between the two theories is often not needed in this work because (as was noted §C.1.4) the Banach-valued theory is often not applicable due to infinite-dimensional nuclear spaces $E$ never being normable [Tre, Cor. 2 to Prop. 50.2]. Nonetheless, the Bochner integral often agrees with the integral in the

## PDF page 711

**C.4. INTEGRATION IN THE SENSE OF PETTIS** · **711**

sense of Pettis when $E$ is a Banach space. Specifically, we may deduce (from [Za, Ch. 6, §31, p. 222,(e)], for instance) as a consequence of Pettis' Separable Measurability Theorem (see [DU, Ch. II, §1, Thm. 2]) that the two integrals coincide when the function is continuous and weakly integrable on a locally compact Hausdorff Radon space and valued in a separable Banach space. For all the intended purposes of this work, the two theories of integration will coincide when both are available.

**C.4.3. Integrability criteria and permanence properties.** We recall that $C(X)$, the $\mathbf C$-vector space of continuous complex-valued functions on the topological space $X$, is a Banach space with respect to the uniform norm if $X$ is a compact Hausdorff topological space. The $\mathbf C$-linear space $\mathscr M(X)$ of complex Radon measures on $X$ is its continuous dual [Fol, Thm. 7.1, Cor. 7.18], with $\lVert\mu\rVert$ as the dual norm on $\mathscr M(X)$. In particular, for such compact Hausdorff $X$, by Agaoglu's Theorem [Scha, Ch. III, Cor. to 4.3; Ch. IV, 3.1] the subset $\mathscr M^{\le 1}(X)$ of such measures $\mu$ with $\lVert\mu\rVert\le 1$ is weakly-compact (i.e., compact with respect to $\sigma(\mathscr M(X),C(X))$). We refer to the weak topology on $\mathscr M(X)$ (i.e., the $\sigma(\mathscr M(X),C(X))$-topology) as the *vague topology* as in [Fol, p. 223].

C.4.3.1. *Vector-valued Mean Value Theorems.* The following Lemma indicates one avenue that leads to a criterion for integrability.

LEMMA C.4.3.1 (Mean-Value Theorem). *Let $X$ be a locally compact Hausdorff space and $\mu$ a finite complex Radon measure on $X$. Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space and $f:X\to E$ a weakly $\mu$-integrable continuous function. Then we have*

$$
\int_X f\,\mathrm{d}\mu\in\lVert\mu\rVert\cdot\overline{\mathrm{cch}}(f(X))
\tag{C.4.3.1}
$$

*where $\overline{\mathrm{cch}}(f(X))$ is the weak-closure within $(E')^*$ of the convex circled hull (also called the absolutely convex hull) of the image of $f$.*

The formation of the convex circled hull of a subset $C\subset E$ commutes with continuous linear maps to another Hausdorff locally convex topological $\mathbf C$-vector space. But when applied to $\iota_E$, beware that the map $\iota_E$ is generally not closed and so the closure of $\mathrm{cch}(C)$ in $E$ with respect to the given topology on $E$ and in $(E')^*$ with respect to the $\sigma((E')^*,E')$-topology may differ (when the closure in $E$ is not compact).

We refer the reader to [Bou-I, Ch. VI ,§1, no. 2, p. VI.5, Prop. 5] for the special case of Lemma C.4.3.1 when $\mu$ is real-valued and positive.

PROOF. For any $\varphi\in E'$, we have

$$
\left\lvert\int_X\langle f(x),\varphi\rangle_{E,E'}\,\mathrm{d}\mu(x)\right\rvert\in[0,\lvert\mu\rvert(X)]\cdot\overline{\lvert\langle f(X),\varphi\rangle_{E,E'}\rvert}\subset\mathbf R.
$$

By design of $\sigma((E')^*,E')$ as an inverse-image topology (see the discussion at the bottom of [Bou-TVS, p. II.42]) from the product topology on $\prod_{\varphi\in E'}\mathbf C$ along the map $u\mapsto(\langle u,\varphi\rangle_{(E')^*,E'})_{\varphi\in E'}$, the average $\lVert\mu\rVert^{-1}\int_X f\,\mathrm{d}\mu$ is contained in the bi-polar set $(f(X)^\circ)^\bullet$ of $f(X)$ (because on any $\varphi$ in the (absolute) polar $f(X)^\circ\subset E'$, the absolute value of $\lVert\mu\rVert^{-1}\int_X\langle f(x),\varphi\rangle_{E,E'}\,\mathrm{d}\mu(x)$ is bounded above by 1), which by [DS, §2, Prop. 1, p. 64] is $\overline{\mathrm{cch}}(f(X))$ (the closure being formed with respect to the $\sigma((E')^*,E')$-topology, and the duality being $\langle E,E'\rangle$ for the formation of the polar $f(X)^\circ$ and being $\langle E',(E')^*\rangle$ for the formation of the second polar $(\cdot)^\bullet$). $\square$

The following is an existence result for Radon measures on a compact Hausdorff topological space $X$ characterizing the closed convex hull of the set of values of a continuous vector-valued function:

THEOREM C.4.3.2 (Weakly closed convex hull of the value set of a continuous vector-valued function). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $X$ a compact Hausdorff topological space. Let $f:X\to E$ be a continuous function. Let $\mathscr M(X)$ be the $\mathbf C$-linear space space of complex Radon measures on*

## PDF page 712

**712** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

*$X$, $\mathscr M^1_+(X)$ the subset of the positive Radon measures on $X$ satisfying $\lVert\mu\rVert=1$, $\mathscr M^{\le 1}(X)$ the compact subset of those complex Radon measures satisfying $\lVert\mu\rVert\le 1$.*

(1) *We have, as subsets of $(E')^*$:*

$$
\left\{\int_X f(x)\,\mathrm{d}\mu(x),\mu\in\mathscr M^1_+(X)\right\}=\overline{\mathrm{Ch}}(f(X))
\tag{C.4.3.2}
$$

*the closure of the right side of (C.4.3.2) being formed in $(E')^*$ topologized with the $\sigma((E')^*,E')$-topology. Moreover, both sets in (C.4.3.2) are compact with respect to the $\sigma((E')^*,E')$-topology.*

(2) *The assertions in (1) hold upon replacing $\mathscr M^1_+(X)$ with $\mathscr M^{\le 1}(X)$ and the closed convex hull with the closed convex circled hull.*

PROOF. (1) : This is [Voigt, Prop. 14.4] since we work over $\mathbf C$ ([Bou-I, Ch. III, §3, Prop. 5] is over $\mathbf R$).

(2) : Let $A$ be the convex circled hull of the subset of $(E')^*$ given by the values $\int_X f(x)\,\mathrm{d}\mu(x)$ as $\mu$ varies over the complex Radon measures on $X$ with *finite support* satisfying $\lVert\mu\rVert\le 1$. Then by definition $A=\mathrm{cch}(f(X))$. By Lemma C.4.3.1, the convex circled superset

$$
B:=\left\{\int_X f(x)\,\mathrm{d}\mu(x),\mu\in\mathscr M^{\le 1}(X)\right\}\subset(E')^*
$$

of the values $\int_X f(x)\,\mathrm{d}\mu(x)$ as $\mu$ varies over $\mathscr M^{\le 1}(X)$, which contains $A$, is contained in the $\sigma((E')^*,E')$-closure of $\mathrm{cch}(f(X))$. This proves that the $\sigma((E')^*,E')$-closure of the set $B$ is $\overline{\mathrm{cch}}(f(X))$. It remains to show that $B$ is itself $\sigma((E')^*,E')$-compact, in which case it is $\sigma((E')^*,E')$-closed and hence equals $\overline{\mathrm{cch}}(f(X))$.

The assignment $\mu\mapsto\int_X f(x)\,\mathrm{d}\mu(x)$ on $\mu\in\mathscr M(X)$ is continuous with respect to the $\sigma(\mathscr M(X),C(X))$-topology on each bounded subset of $\mathscr M(X)_\sigma$ (such as the compact subset $\mathscr M^{\le 1}(X)$) and the $\sigma((E')^*,E')$-topology on $(E')^*$. (Note that formation of $\int_X f(x)\,\mathrm{d}\mu(x)$ is not generally continuous with respect to $\mu\in\mathscr M(X)$ using the $\sigma(\mathscr M(X),C(X))$-topology; it is continuous on the convex cone of positive measures, and on all $\sigma(\mathscr M(X),C(X))$-bounded subsets by [Bou-I, Ch. III, §4, No. 4, Corollary, p. III.40], which is what we are using here.) But $\mathscr M^{\le 1}(X)$ is compact with respect to the $\sigma(\mathscr M(X),C(X))$-topology, and hence so is $B$ with respect to the $\sigma((E')^*,E')$-topology. $\square$

REMARK C.4.3.3. In the proof of Theorem C.4.3.2, we used properties of the $\sigma(\mathscr M(X),C(X))$-topology for $X$ a compact Hausdorff topological space.

Vague continuity on the cone of positive Radon measures can be thought of as a generalization of an analog of the Monotone Convergence Theorem, while continuity on weakly bounded subsets of $\mathscr M(X)$ can be thought as being in a similar vein as the Dominated Convergence Theorem.

We are going to be routinely making two assumptions on $E$ throughout our work, aside from $E$ being locally convex: that $E$ be Hausdorff, and *quasi-complete*. In our situations of interest, these will always be satisfied. This and Lemma C.4.3.1 provide an integrability criterion for continuous compactly supported functions (see Theorem C.4.3.5 below).

A priori, the linear form $\int_X f\,\mathrm{d}\mu$ is only contained in the weak completion $(E')^*$ of $E$ (see the start of Lemma C.4.3.1). For the purposes of this work, there will be two avenues to decide when a weakly integrable function $f:X\to E$ is integrable (in the sense of Definition C.4.2.1(3)). Quasi-completeness of $E$ is one of them. The definition of quasi-completeness is that every *bounded* closed subset of $E$ is complete. (Here we are using boundedness in the sense of locally convex topological vector spaces.) This is equivalent to saying that every *bounded* Cauchy net in $E$ converges in $E$. It is therefore also referred to as *bounded completeness*. We refer the reader to [Scha, Ch. I, 5.6; Ch. II, Cor. to 4.3] for some properties of quasi-complete Hausdorff locally convex topological vector spaces.

REMARK C.4.3.4 (Cautionary remark on boundedness and net-convergence). For the purposes of checking convergence or continuity in a Hausdorff topological vector space with nets, we are allowed to test such

## PDF page 713

**C.4. INTEGRATION IN THE SENSE OF PETTIS** · **713**

conditions upon replacing an $I$-indexed net $\{x_i\}_{i\in I}$ with the resulting $I_0$-indexed net obtained by restriction to $I_0\subset I$, with $I_0:=\{i\in I:i\ge i_0\}$, for some fixed arbitrary $i_0\in I$; we refer to $\{x_i\}_{i\ge i_0}$ as a *tail* of the original net. It is elementary that every Cauchy sequence in a topological $\mathbf C$-vector space $E$ is bounded (in the sense of topological vector spaces), but in metrizable locally convex topological $\mathbf C$-vector spaces even a convergent net can fail to be “eventually bounded” (i.e., no tail $\{x_i\}_{i\ge i_0}$ is bounded).

To make examples, we begin with the simpler construction of an unbounded convergent net. Let $I=\mathbf R_{>0}$ equipped with its natural ordering. Define $z_a:=a^{-1}\in\mathbf C$ for each $a\in I$. The net of complex numbers $\{z_a\}_{a\in I}$ is convergent to $0\in\mathbf C$, but the net is not bounded in $\mathbf C$. However, this net is eventually bounded; e.g., $\{z_a\}_{a\ge 1}$ is bounded.

To make a net converging to $0$ in the meterizable case such that the net is not eventually bounded, consider an infinite-dimensional nuclear metrizable locally convex space $F$ (such as the Schwartz space $\mathcal S(\mathbf R)$) and pick a decreasing base of convex $0$-neighborhoods $U_1\supset U_2\supset\cdots$ (this exists by metrizability). For each *nonzero* $x\in U_1$, define $n(x)$ to be the largest positive integer $N$ such that $x\in U_N$, and let $J$ be the set $U_1-\{0\}$ with the partial ordering $x\ge y$ precisely when $n(x)\ge n(y)$. Defining $x_j=j\in U_1$, the net $\{x_j\}_{j\in J}$ converges to $0$ and we claim no tail $\{x_j\}_{j\ge j_0}$ is bounded. Suppose to the contrary that some such tail is bounded, so the convex $0$-neighborhood $U_{n(x_{j_0})}$ is bounded. Then $F$ is normable [Scha, Ch. II,, 2.1], but a nuclear normable locally convex space is finite-dimensional [Tre, Cor. 2 to Prop. 50.2], a contradiction.

In the non-metrizable locally convex case, to make a Cauchy set that is not eventually bounded (as will also help to make examples that are quasi-complete but not complete, a distinction that does not arise in the metrizable setting), let $H$ be an infinite-dimensional separable Hilbert space and $E:=\mathscr B_{\mathrm{SOT}}(H)$ be the $\mathbf C$-vector space of bounded endomorphisms of $H$ equipped with the strong operator topology (i.e., pointwise convergence). By Lemma C.3.3.1, this $E$ is Hausdorff, locally convex, and quasi-complete. We will construct a Cauchy net in $E$ that has no limit (so $E$ is not complete) so by quasi-completeness of $E$ such a Cauchy net cannot be eventually bounded (as otherwise it would have a limit, by quasi-completeness). This also shows $E$ is not metrizable, since quasi-completeness implies completeness in the metrizable case.

To make the desired Cauchy net, let $\varphi\in H^*-H'$ be a discontinuous linear functional on $H$ (as exists since $H$ is infinite-dimensional). Then by extending the restriction of $\varphi$ on each finite-dimensional subspace to a continuous linear functional on $H$ using the Hahn-Banach Theorem (in the form given in [Scha, Ch. II, 4.2]) and partially ordering the set $I$ of finite-dimensional subspaces of $H$ by inclusion, we obtain a net $\{\varphi_i\}_{i\in I}\subset H'$ of continuous linear functionals converging to $\varphi$ “pointwise”: for every $h\in H$, we have $\varphi_i(h)\to\varphi(h)$ as a net of complex numbers.

Upon fixing $h\in H$ nonzero, we obtain a net $\{A_i\}_{i\in I}\subset E$ by defining $A_i(u):=\varphi_i(u)\cdot h$ for each $u\in H$, and $A_i\to A$ pointwise on $H$ for $A(u):=\varphi(u)\cdot h$ but $A$ is not a bounded operator on $H$. Explicitly, we have $\|A_i(u)-A(u)\|_H=|\varphi_i(u)-\varphi(u)|\,\|h\|_H\to 0$. In particular, $\{A_i\}_{i\in I}\subset E$ is a Cauchy net. But this net has no limit in $E$, since a limit (if one exists) would have to agree pointwise with the discontinuous $A$.

C.4.3.2. *Stability properties of vector-valued integrals and integrability criteria.* Quasi-completeness of a Hausdorff locally convex topological vector space $E$ is a useful criterion for integrability in favorable cases: if $f$ is continuous and compactly supported, then it is integrable in the $E$-valued sense.

Theorem C.4.3.5 (Pettis’ Integrability Criterion). *Let $X$ be a locally compact Hausdorff space and $\mu$ a finite complex Radon measure on $X$. Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space and $f:X\to E$ a compactly supported continuous function. If $E$ is quasi-complete then $f$ is $\mu$-integrable.*

This is [Gro-a, Lemme 2], where the assumptions of the Lemma are met because convex hulls interact well with pre-compactness in the quasi-complete case: in a Hausdorff quasi-complete locally convex topological $\mathbf C$-vector space, the convex circled hull of any pre-compact subset is pre-compact [Scha, Ch. II, Cor. to 4.3].

## PDF page 714

**714** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

Proof. For closed $Z\subset X$ with $\mathrm{supp}(f)\subset Z$, we have $\int_Z f\,\mathrm{d}\mu=\int_X f\,\mathrm{d}\mu$ in $E'$ by the respective definitions of these functionals. By Lemma C.4.3.1 applied to $\mathrm{supp}(f)$, we have

$$
\int_X f\,\mathrm{d}\mu\in\mu(\mathrm{supp}(f))\cdot\overline{\mathrm{cch}}(f(X)) \tag{C.4.3.3}
$$

where $\overline{\mathrm{cch}}f(X)$ is the closure of the convex circled hull (also called the absolutely convex hull) of the image of $f$, formed within the weak completion $(E')^*$ of $E$. But $\mathrm{supp}(f)$ is compact, so $f(X)$ is also compact, and the quasi-completeness of $E$ then ensures such closure is contained in $E$ by Lemma C.4.1.2(1). There therefore exists an element of $E$ representing the integral $\int_X f\,\mathrm{d}\mu$. $\square$

Remark C.4.3.6. We refer the reader to [Bou-I, §3.3, Prop. 7, p. III.37] for another criterion for the linear form $\varphi\mapsto\int_X\langle f(x),\varphi\rangle\,\mathrm{d}\mu(x)$ (an element of $(E')^*$) to be contained in $E$.

In our case, $X$ will either be a closed positively oriented simple parametric curve within the complex plane, equipped with its own finite complex Radon measure induced by the parametrization, or a compact subset of a locally compact Hausdorff abelian topological group equipped with a normalized Haar measure, or a fibral Radon measure in a product factorization of a Haar measure induced by fibering such group over another locally compact Hausdorff abelian topological group.

Quasi-completeness of $E$ in Theorem C.4.3.5 is one avenue to ensure integrability. Another such criterion leverages duality:

Lemma C.4.3.7. *Let $X$ be a locally compact Hausdorff space, and $\mu$ a finite complex Radon measure on $X$. Let $B$ be a complex Banach space, and $f:X\to B$ a weakly measurable function. Assume that $f$ is weakly $\mu$-integrable and $B$ is reflexive. Then $f$ is $\mu$-integrable.*

Proof. Let $B'$ be the strong dual of $B$ (this is the usual dual Banach space). By [DU, Ch. II, §3, Lemma 1], applied to $E=X$ in the notation of *loc.cit.*, there exists $\lambda\in B''$ such that

$$
\langle\lambda,\varphi\rangle_{B'',B'}=\int_X\langle f(x),\varphi\rangle_{B,B'}\,\mathrm{d}\mu(x) \tag{C.4.3.4}
$$

for every $\varphi\in B'$ (i.e., the right side is continuous in $\varphi\in B'$). Since $B$ is reflexive by hypothesis, $\iota_B:B\to (B')^*$ maps $B$ onto (and in fact topologically isomorphically) $B''$ and hence there exists $b\in B$ such that $\iota_B(b)=\lambda$. It follows that $f$ is $\mu$-integrable. $\square$

Before discussing a consequence of Lemma C.4.3.7, we require the following two properties of the integral in the sense of Pettis.

Lemma C.4.3.8. *Let $T:E_1\to E_2$ be a continuous linear map between Hausdorff locally convex complex vector spaces, and $(X,\mu)$ a locally compact Hausdorff topological space with $\mu$ a finite complex Radon measure. Let $f:X\to E_1$ be a weakly $\mu$-integrable function. Then*

$$
\int_X (T\circ f)\,\mathrm{d}\mu=(T')^*\left(\int_X f\,\mathrm{d}\mu\right) \tag{C.4.3.5}
$$

*as elements of $(E_2')^*$. If $f$ is $\mu$-integrable then so is $T\circ f$, and then*

$$
\int_X (T\circ f)\,\mathrm{d}\mu=T\left(\int_X f\,\mathrm{d}\mu\right) \tag{C.4.3.6}
$$

*as elements of $E_2$.*

Note that the integrals in (C.4.3.5) are simply the algebraic linear forms $\varphi\mapsto\int_X\langle f(x),\varphi\rangle_{E_1,E_1'}\,\mathrm{d}\mu(x)$ on $E_1'$ and $\varphi\mapsto\int_X\langle T(f(x)),\varphi\rangle_{E_2,E_2'}\,\mathrm{d}\mu(x)$ on $E_2'$, i.e. elements of $(E_1')^*$ and $(E_2')^*$ only, respectively. The Lemma is then a diagram chase for (C.4.3.5) with (C.4.1.2) then yielding (C.4.3.6).

## PDF page 715

**C.4. INTEGRATION IN THE SENSE OF PETTIS** · **715**

Proof. We let $\varphi\in E_2'$ be arbitrary, and compute

$$
\left\langle\int_X (T\circ f)\,\mathrm{d}\mu,\varphi\right\rangle_{(E_2')^*,E_2'}=\int_X\langle T(f(x)),\varphi\rangle_{E_2,E_2'}\,\mathrm{d}\mu(x) \tag{C.4.3.7}
$$

Since $T$ is continuous, then by [Bou-TVS, Ch. II, §6.4, Prop. 5] we have $\langle T(f(x)),\varphi\rangle_{E_2,E_2'}=\langle f(x),T'(\varphi)\rangle_{E_1,E_1'}$ for every $x\in X$ and $\varphi\in E_2'$, and so the right side of (C.4.3.7) equals

$$
\int_X\langle f(x),T'(\varphi)\rangle_{E_1,E_1'}\,\mathrm{d}\mu(x)=\left\langle\int_X f\,\mathrm{d}\mu,T'(\varphi)\right\rangle_{(E_1')^*,E_1'} \tag{C.4.3.8}
$$

We now observe that since $T'$ is continuous as an operator $E_2'\to E_1'$ with respect to the $\sigma(E_2',E_2)$-topology on the source and the $\sigma(E_1',E_1)$-topology on the target, then it is also continuous with respect to the $\sigma(E_2',(E_2')^*)$-topology on the source and the $\sigma(E_1',(E_1')^*)$-topology on the target by [Bou-TVS, Ch. II, §6.2, Cor. 2], because $E_k\subset (E_k')^*$ for $k=1,2$, since $E_1,E_2$ are Hausdorff. By [Bou-TVS, Ch. II, §6.4, Prop. 5], $(T')^*$ exists and is continuous and the right side of (C.4.3.8) further equals

$$
\left\langle (T')^*\left(\int_X f\,\mathrm{d}\mu\right),\varphi\right\rangle_{(E_1')^*,E_1'}
$$

This proves the identity in (C.4.3.5), being $\varphi\in E_2'$ arbitrary. Compatibility of $\iota_{E_k}:E_k\to (E_k')^*$ for $k=1,2$ with $T$ and $(T')^*$, provided by Lemma C.4.1.1, gives that if $f$ is $\mu$-integrable, i.e. $\int_X f\,\mathrm{d}\mu$ is in the image of $\iota_{E_1}$, then $\int_X (T\circ f)\,\mathrm{d}\mu$ is in the image of $\iota_{E_2}$, and so $T\circ f$ is also $\mu$-integrable, and (C.4.3.6) holds in $E_2$ by injectivity of $\iota_{E_2}$. $\square$

Lemma C.4.3.9. *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, and $(X,\mu)$ a locally compact Hausdorff topological space with $\mu$ a finite complex Radon measure. Let $f:X\to E$ be a $\mu$-integrable function. For every continuous seminorm $\nu$ on $E$ such that $x\mapsto\nu(f(x))$ is $\mu$-measurable, we have*

$$
\nu\left(\int_X f\,\mathrm{d}\mu\right)\le\int_X\nu(f(x))\,\mathrm{d}\mu(x). \tag{C.4.3.9}
$$

A variant is given in [Bou-I, Ch. VI, §1, no. 2, Prop. 6].

Remark C.4.3.10. The measurability assumption on $\nu(f(x))$ as a function of $x\in X$ ensures that the right side of (C.4.3.9) makes sense as a Lebesgue integral. The integral on the right side of (C.4.3.9) may still be infinite.

Proof. For every $u\in E$, there exists $\varphi\in E'$ such that $\varphi(u)=\nu(u)$ and for all $w\in E$ we have $|\varphi(w)|\le\nu(w)$. This is a consequence of the Hahn-Banach Theorem. Upon choosing $u:=\int_X f\,\mathrm{d}\mu$ and $w=f(x)$ for any $x\in X$, we obtain

$$
\left|\int_X\langle f(x),\varphi\rangle_{E,E'}\,\mathrm{d}\mu(x)\right|\le\int_X|\langle f(x),\varphi\rangle_{E,E'}|\,\mathrm{d}\mu(x)\le\int_X\nu(f(x))\,\mathrm{d}\mu(x) \tag{C.4.3.10}
$$

where the left side is $|\varphi(u)|=\nu(u)$. $\square$

Lemma C.4.3.11. *Let $E$ be a complex Hilbert space, and $\mathscr B(E)$ the vector space of continuous $\mathbf C$-linear operators on $E$. Let $X$ be a locally compact Hausdorff space, and $\mu$ a finite complex Radon measure on $X$. Let $f:X\to\mathscr B(E)$ be a function. Assume*

*(1) The function $f(u):x\mapsto f(x)(u)\in E$ is weakly measurable for every $u\in E$.*

*(2) The function $x\mapsto\|f(x)\|$ is $\mu$-measurable and $\mu$-integrable.*

*Then for every $u\in E$, the function $x\mapsto f(x)(u)$ is $\mu$-integrable, and the assignment*

$$
u\mapsto\int_X f(u)\,\mathrm{d}\mu \tag{C.4.3.11}
$$

## PDF page 716

**716** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

*is a bounded $\mathbf C$-linear operator on $E$.*

Proof. Let $\varphi\in E'$ be an arbitrary continuous linear form on $E$. Then we have, upon denoting $\|\cdot\|_{E'}$ the operator norm on $E'$, by $\|\cdot\|_E$ the norm on $E$, and $\|\cdot\|$ the operator norm on $\mathscr B(E)$,

$$
|\langle f(x)(u),\varphi\rangle_{E,E'}|\le\|\varphi\|_{E'}\|f(x)(u)\|_E\le\|\varphi\|_{E'}\|f(x)\|\,\|u\|_E \tag{C.4.3.12}
$$

By assumption, the function $x\mapsto\|f(x)\|$ is $\mu$-measurable. Since $x\mapsto f(x)(u)$ is weakly measurable, the integral of $\langle f(x)(u),\varphi\rangle_{E,E'}$ over $X$ is meaningful to contemplate. We integrate the outermost sides of (C.4.3.12) over $X$ and obtain

$$
\int_X|\langle f(x)(u),\varphi\rangle_{E,E'}|\,\mathrm{d}\mu(x)\le\|\varphi\|_{E'}\|u\|_E\int_X\|f(x)\|\,\mathrm{d}\mu(x). \tag{C.4.3.13}
$$

Since $x\mapsto\|f(x)\|$ is $\mu$-integrable, we deduce from (C.4.3.13) that for every $u\in E$, $x\mapsto f(x)(u)$ is weakly $\mu$-integrable. Since $E$ is a Hilbert space, it is reflexive. Lemma C.4.3.7 therefore applies and gives that $x\mapsto f(x)(u)$ is $\mu$-integrable for every $u\in E$. The topology on $E$ is normed, and by Lemma C.4.3.9 applied with $\nu=\|\cdot\|_E$, we have

$$
\left\|\int_X f(u)\,\mathrm{d}\mu\right\|_E\le\int_X\|f(u)\|_E\,\mathrm{d}\mu\le\|u\|_E\int_X\|f(x)\|\,\mathrm{d}\mu(x) \tag{C.4.3.14}
$$

showing boundedness of the linear endomorphism $u\mapsto\int_X f(u)\,\mathrm{d}\mu$ of $E$. $\square$

C.4.3.3. *Continuity criterion.* For $X$ a locally compact Hausdorff space and $E$ a Hausdorff locally convex topological $\mathbf C$-vector space, a net $\{f_i\}_{i\in I}$ of continuous functions on $X$ valued in $E$ converges to $f:X\to E$ uniformly on compact subsets, or *locally uniformly*, if for every compact subset $K\subset X$, the net $\{f_i|_K\}_{i\in I}$ converges to $f|_K$ uniformly. In turn, by this we mean that for every continuous seminorm $\nu$ on $E$, $\lim_{i\in I}\sup_{x\in K}\nu(f_i-f)=0$. In other words, the terminology for uniform and locally uniform convergence of nets of continuous scalar-valued functions retains the same meaning for continuous $E$-valued functions. Such convergence can be equivalently tested on a generating family of continuous seminorms on $E$.

Lemma C.4.3.12. *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, and $(X,\mu)$ a locally compact Hausdorff topological space with $\mu$ a finite complex Radon measure. Let $I$ be a directed set, and $\{f_i\}_{i\in I}$ a net of continuous, $\mu$-integrable functions $f_i:X\to E$ converging uniformly to the continuous $\mu$-integrable function $f:X\to E$. Then*

$$
\lim_{i\in I}\int_X f_i\,\mathrm{d}\mu=\int_X f\,\mathrm{d}\mu. \tag{C.4.3.15}
$$

Proof. We call $e_i:=\int_X f_i\,\mathrm{d}\mu$ (all elements of $E$ by Theorem C.4.3.5). Let $\nu:E\to\mathbf R_{\ge 0}$ be an arbitrary continuous seminorm on $E$. By Lemma C.4.3.9, we have

$$
\nu\left(\int_X (f_i-f)\,\mathrm{d}\mu\right)\le\int_X\nu(f_i-f)(x)\,\mathrm{d}\mu(x) \tag{C.4.3.16}
$$

for every $i\in I$. Since $\mu$ is finite Radon and the convergence of $\{f_i\}_{i\in I}$ is uniform, the right side of (C.4.3.16) is bounded above by $|\mu(X)|\sup_{x\in X}\nu(f_i-f)$ and so it tends to zero. $\square$

Remark C.4.3.13. We will specialize the concepts and results in this subsection to two classes of $E$: they are Hilbert spaces, and the $\mathbf C$-vector space of bounded linear endomorphism of a Hilbert space equipped with the locally convex strong operator topology, on the one hand, and with the operator-norm topology (which makes it into a Banach space), on the other. Hilbert spaces, as complete metric spaces, are quasi-complete as a consequence of the definition. As for $E:=\mathscr B_{\mathrm{SOT}}(H)$, the space of bounded linear endomorphisms of a Hilbert space $H$ endowed with the strong operator topology, $E$ is indeed quasi-complete, as a consequence of the Uniform Boundedness Principle: see Lemma C.3.3.1.

## PDF page 717

**C.4. INTEGRATION IN THE SENSE OF PETTIS** · **717**

C.4.4. **Fubini’s Theorem and Weil’s Integral Formula.** We require a version of Fubini’s Theorem for the integral in the sense of Pettis.

Lemma C.4.4.1. *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. Let $X,Y$ be two locally compact Hausdorff $\sigma$-compact topological spaces, and $\mu,\nu$ complete${}^{20}$ Radon measures on $X,Y$, respectively. Let $f:X\times Y\to E$ be a weakly $(\mu\otimes\nu)$-integrable function. Assume:*

*(1) the function $f(x,\cdot)$ is $\nu$-integrable for every $x\in X$,*

*(2) the function $f(\cdot,y)$ is $\mu$-integrable for every $y\in Y$.*

*Then $x\mapsto\int_Y f(x,y)\,\mathrm{d}\nu(y)\in E$ and $y\mapsto\int_X f(x,y)\,\mathrm{d}\mu(x)\in E$ are weakly $\mu$-integrable on $X$ and weakly $\nu$-integrable on $Y$ respectively and as elements of $(E')^*$ we have the identity*

$$
\int_{X\times Y} f\,\mathrm{d}(\nu\otimes\mu)=\int_Y\left(\int_X f(x,y)\,\mathrm{d}\mu(x)\right)\mathrm{d}\nu(y)=\int_X\left(\int_Y f(x,y)\,\mathrm{d}\nu(y)\right)\mathrm{d}\mu(x). \tag{C.4.4.1}
$$

Proof. By definition, for every $\varphi\in E'$ we have

$$
\varphi\left(\int_X f\,\mathrm{d}(\mu\otimes\nu)\right)=\int_X (\varphi\circ f)\,\mathrm{d}(\mu\otimes\nu)=\int_X\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}(\mu\otimes\nu) \tag{C.4.4.2}
$$

Since $f$ is weakly $(\mu\otimes\nu)$-integrable by assumption, then by the $\mathbf C$-valued Fubini theorem we have the following conclusions:

(1) $y\mapsto\langle f(x,y),\varphi\rangle_{E,E'}$ is $\nu$-integrable for almost all $x\in X$,

(2) $x\mapsto\langle f(x,y),\varphi\rangle_{E,E'}$ is $\mu$-integrable for almost all $y\in Y$,

(3) the functions $x\mapsto\int_Y\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}\nu(y)$ and $y\mapsto\int_X\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}\mu(x)$, defined almost everywhere on $X$, respectively $Y$, are integrable,

(4) we have the identity

$$
\int_{X\times Y}\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}(\mu\otimes\nu)(x,y)=\int_Y\left(\int_X\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}\mu(x)\right)\mathrm{d}\nu(y)=\int_X\left(\int_Y\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}\nu(y)\right)\mathrm{d}\mu(x). \tag{C.4.4.3}
$$

By hypothesis the functions $f(x,\cdot)$ and $f(\cdot,y)$ are integrable for *all* $x\in X$, respectively *all* $y\in Y$. The assignments $\varphi\mapsto\int_X\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}\mu(x)$ and $\varphi\mapsto\int_Y\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}\nu(y)$ are therefore elements of $E$, as opposed to merely elements of $(E')^*$, denoted $\int_X f(\cdot,y)\,\mathrm{d}\mu$ and $\int_Y f(x,\cdot)\,\mathrm{d}\nu$, and they are so for all $y\in Y$, and all $x\in X$, respectively. Each is weakly $\nu$-, respectively weakly $\mu$-integrable by (3) above. The integrals

$$
\int_Y\left(\int_X f(x,y)\,\mathrm{d}\mu(x)\right)\mathrm{d}\nu(y),\quad\int_X\left(\int_Y f(x,y)\,\mathrm{d}\nu(y)\right)\mathrm{d}\mu(x). \tag{C.4.4.4}
$$

are therefore both elements of $(E')^*$, and by (C.4.4.3) they equal the left side of (C.4.4.1) as elements of $(E')^*$. $\square$

Remark C.4.4.2. Upon assuming that $f$ in Lemma C.4.4.1 is continuous and compactly supported and $E$ is quasi-complete, the result of the Lemma relates to the Remark in [Bou-I, Ch. III, §4, p. III.43]. Indeed, the image $f(X\times Y)$ in $E$, endowed with the subspace topology, agrees with $f(\mathrm{supp}(f))$ and is therefore compact by continuity of $f$. Its closed convex circled hull is therefore also compact, since $E$ is quasi-complete (see [Scha, Ch. II, Cor. to 4.3]). In particular, that closed convex circled hull is complete and convex. By [Bou-I, Ch. III, §3, Prop. 7], the integral $\int_{X\times Y} f\,\mathrm{d}(\mu\otimes\nu)$ a priori only an element of $(E')^*$ is therefore contained in $E$ (as is also provided by Theorem C.4.3.5). Similarly $\int_Y f(\cdot,y)\,\mathrm{d}\nu(y)$ and $\int_X f(x,\cdot)\,\mathrm{d}\mu(x)$ are $\mu$-integrable and $\nu$-integrable respectively.

---

${}^{20}$Completeness of measures has been added in to ensure $\mu\otimes\nu$ is complete, as may be implicit in the proof; for uses elsewhere should Haar measures be complete by convention, so “Borel set” modified accordingly?

## PDF page 718

**718** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

By the Remark in [Bou-I, Ch. III, §4, p. III.43] and [Bou-I, Ch. III, Lemma 2], the functions $f(x,\cdot)$ and $(\cdot,y)$ are elements of $\widetilde{\mathscr K}(Y,E)$, respectively $\widetilde{\mathscr K}(X,E)$, in the notation of *loc.cit.* (see [Bou-I, Ch. III, §3, p. III.32]), and these are continuous $E$-valued functions on $Y$, respectively $X$, such that their composition with every $\varphi\in E'$ is compactly supported as a scalar-valued function.

Since $\langle f(x,y),\varphi\rangle_{E,E'}$ is a continuous scalar-valued integrable function on $X\times Y$, [Bou-I, Ch. III, §4, Lemma 2] applies and implies that both $y\mapsto\int_X\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}\mu(x)$ and $x\mapsto\int_Y\langle f(x,y),\varphi\rangle_{E,E'}\,\mathrm{d}\nu(y)$ are continuous compactly supported functions on $Y$, respectively $X$, for every $\varphi\in E'$. By (C.4.3.3) and by compactness of the support of the above functions, the integrals in (C.4.4.1) are contained in $E$ by Theorem C.4.3.5, being $E$ quasi-complete. However, the integrals $\int_X f(x,\cdot)\,\mathrm{d}\nu$ and $\int_X f(\cdot,y)\,\mathrm{d}\mu$ are a priori only elements $(E')^*$. Lemma C.4.4.1, instead, *assumes* that they are elements in $E\subset (E')^*$.

We recall here the following important result on the Haar integral, for which we refer the reader to [DE, Thm. 1.5.3] beyond the abelian case. The scope is to formulate and prove a form of it for integrals in the sense of Pettis.

Theorem C.4.4.3. *Let $G$ be a locally compact Hausdorff abelian group, $H\subset G$ a closed subgroup. There exists a Haar measure $\nu$ on the quotient $G/H$ uniquely determined by a choice of Haar measure $\mu_G$ on $G$ and $\mu_H$ on $H$ and such that for every $f\in C_c(G)$, we have*

$$
\int_G f(g)\,\mathrm{d}\mu_G(g)=\int_{G/H}\int_H f(xh)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\nu(x). \tag{C.4.4.5}
$$

*Moreover, for every $f\in L^1(G,\mu_G)$, then the assignment $x\mapsto\int_H f(xh)\,\mathrm{d}\mu_H(h)$ defines $\mu_G$-almost everywhere on $G$ a function that is $\nu$-measurable and absolutely $\nu$-integrable on $G/H$, and (C.4.4.5) holds for $f$.*

As an additional result, to check that a $\mu_G$-measurable function $f:G\to\mathbf C$ is (absolutely) $\mu_G$-integrable it is enough to check that the iterated integral in the right side of (C.4.4.5) for $|f|$ converges. This is [DE, Cor. 1.5.4]:

Lemma C.4.4.4. *Let $G$ be a locally compact Hausdorff abelian group, $H\subset G$ a closed subgroup, and $\mu_G$ and $\mu_H$ Haar measures on $G$ and $H$ respectively. Let $\nu$ be the unique Haar measure on the quotient $G/H$ provided by Theorem C.4.4.3. Let $f:G\to\mathbf C$ be a measurable function. Then if*

$$
\int_{G/H}\int_H |f(xh)|\,\mathrm{d}\mu_H(h)\,\mathrm{d}\nu(x) \tag{C.4.4.6}
$$

*converges, $f$ is absolutely $\mu_G$-integrable over $G$, and (C.4.4.5) holds.*

We now formulate an analog of Weil’s formula (C.4.4.5) when the functions are valued in a Hausdorff locally convex topological $\mathbf C$-vector space.${}^{21}$

Lemma C.4.4.5. *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space. Let $G$ be a locally compact Hausdorff abelian group, $H\subset G$ a closed subgroup, and $\mu_G$ and $\mu_H$ Haar measures on $G$ and $H$ respectively. Let $\nu$ be the Haar measure on the quotient $G/H$ provided by Theorem C.4.4.3. Let $f:G\to E$ be a weakly $\mu_G$-integrable function. Assume that for every $x\in G$, the function $h\mapsto f(xh)$ is $\mu_H$-integrable for every $x\in G$. Then*

*(1) the function $F:G\to E$ defined by*

$$
F(x):=\int_H f(xh)\,\mathrm{d}\mu_H(h),\quad x\in G \tag{C.4.4.7}
$$

*factors through a unique weakly $\nu$-integrable function on $f^H:G/H\to E$.*

---

${}^{21}$Does this result require Haar measures to be complete?

## PDF page 719

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **719**

*(2) The function $f^H$ is weakly $\nu$-integrable and we have the identity*

$$
\int_G f\,\mathrm{d}\mu_G=\int_{G/H} f^H(xH)\,\mathrm{d}\nu(xH) \tag{C.4.4.8}
$$

*as elements of $(E')^*$.*

Proof. (1) : Since the function $h\mapsto f(hx)$ on $H$ is $\mu_H$-integrable for every $x\in G$, then the integral

$$
F(x):=\int_H f(xh)\,\mathrm{d}\mu_H(h) \tag{C.4.4.9}
$$

is contained in $E$ for every $x\in G$, instead of merely in $(E')^*$. Let $x_0h'$ be the arbitrary element of the left $H$-coset $x_0H\subset G$. Then we have, for every $\varphi\in E'$

$$
\langle F(x_0h'),\varphi\rangle_{E,E'}=\langle F(x_0h'),\varphi\rangle_{(E')^*,E'}=\int_H\langle f(x_0h'h),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_H(h) \tag{C.4.4.10}
$$

where we have tacitly identified $\iota_E(F(x_0h'))$ with $F(x_0h')$. Upon calling $h'':=h'h$, the right side of (C.4.4.10) turns into

$$
\int_H\langle f(x_0h''),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_H((h')^{-1}h'')=\int_H\langle f(x_0h),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_H(h)=\langle F(x_0),\varphi\rangle_{(E')^*,E'}=\langle F(x_0),\varphi\rangle_{E,E'} \tag{C.4.4.11}
$$

by left-invariance of the Haar measure $\mu_H$ on $H$. We deduce the identity $\langle F(x_0),\varphi\rangle_{E,E'}=\langle F(x_0h'),\varphi\rangle_{E,E'}$, valid for every $\varphi\in E'$. Since $E$ is Hausdorff, by the Hahn-Banach Theorem we deduce $F(x_0h')=F(x_0)$. Thus, $F$ is constant on left $H$-cosets and hence descends uniquely to a function $f^H:G/H\to E$, defined as $f^H(xH):=F(x)$. By Theorem C.4.4.3 applied to the function $\langle f,\varphi\rangle_{E,E'}\in L^1(G,\mu_G)$, we have that the function $\langle f^H((\cdot)H),\varphi\rangle_{E,E'}$ is $\nu$-integrable on $G/H$ for every $\varphi\in E'$.

(2) : For every $\varphi\in E'$, we have by Lemma C.4.4.4 that $\langle f(x),\varphi\rangle_{E,E'}$ is $\mu_G$-integrable for every $\varphi\in E'$, and by Theorem C.4.4.3

$$
\int_G\langle f(x),\varphi\rangle_{E,E'}\,\mathrm{d}\mu_G(x)=\int_{G/H}\langle f^H(xH),\varphi\rangle_{E,E'}\,\mathrm{d}\nu(xH). \tag{C.4.4.12}
$$

This defines both $\int_G f\,\mathrm{d}\mu_G$ and $\int_{G/H} f^H\,\mathrm{d}\nu$ as elements of $(E')^*$, and as such they are equal. $\square$

We have now discussed all the required preparations on integration of functions defined on locally compact Hausdorff Radon spaces, and valued in Hausdorff locally convex topological $\mathbf C$-vector spaces.

C.5. **Meromorphic functions valued in a quasi-complete locally convex tvs**

We begin by recalling the classical concept of holomorphy for functions valued in a locally convex topological complex vector space. Our main reference for the concept and basic characterizations of holomorphy for functions valued in a locally convex topological vector space is [Gro-a]. We will occasionally use [Gro-b, Ch. II, §3] to characterize certain spaces of holomorphic and meromorphic functions as projective tensor products, under favorable conditions that we will find to be met in our situations of interest.

The literature on holomorphic and meromorphic functions valued in locally convex complex vector spaces is extensive. Sources of input for the material in this subsection and the next are [Kruse, §3, 7], [Jor-a, §3], and [BJM]. The latter two in particular further build from work of Grosse-Erdmann in [GE] on the topologies on spaces of scalar-valued meromorphic functions on complex domains, an analog of which we will be requiring.

The main difference between the existing literature and the material discussed in this section is that we will be allowing Riemann surfaces as domains of definition for meromorphic vector-valued functions, which entails some, while limited, non-trivial amount of additional work.

## PDF page 720

**720** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

C.5.1. **Vector-valued continuous and differentiable functions.** For a Hausdorff locally compact space $X$, we denote by $\overline X$ its one-point compactification, with $\infty$ the point at infinity, i.e. $\{\infty\}=\overline X-X$. The space $\overline X$ is compact Hausdorff, and $X\subset\overline X$ is an open subset whose subspace topology is the intrinsic topology on $X$.

We say a continuous complex-valued function $f$ on $X$ *tends to zero at infinity* if and only if it is bounded on $X$ and its (hence existing) continuous extension $F:\overline X\to\mathbf C$ satisfies $\lim_{x\to+\infty}F(x)=0$. This limit is in the sense of convergence in general topological spaces, defined by means of Cauchy filter-base or Cauchy net convergence.

We further recall that on $C_b(X)$, the $\mathbf C$-vector space of complex valued *bounded* continuous functions on $X$, we may define the uniform norm

$$
\|f\|_u:=\sup_{x\in X}|f(x)| \tag{C.5.1.1}
$$

which promotes $C_b(X)$ to a complex Banach space. We call the norm-topology on $C_b(X)$ the topology of *uniform convergence.*

Within $C_b(X)$ we further find the $\mathbf C$-vector subspace $C_c(X)$ of continuous complex-valued compactly supported functions. This is, algebraically, the filtered colimit of the $\mathbf C$-linear subspaces $C(X,K)$ of continuous functions on $X$ whose support is contained within the compact subset $K\subset X$. We denote by $\mathcal{K}_X$ the set of all compact subsets of $X$. An inclusion of compact subsets $K'\subset K$ induces a $\mathbf C$-linear extension-by-zero operator

$$
C(X,K')\to C(X,K)
$$

realizing $C_c(X)$ as $C_c(X)=\operatorname*{\mathrm{colim}}_{K\in\mathcal{K}_X}C(X,K)$ as a $\mathbf C$-linear subspace of $C_b(X)$. The uniform norm on $C_b(X)$ endows each $C(X,K)$ with the structure of a complete normed space, since it is a closed subspace of $C(K)$, this latter equipped with the topology of uniform convergence.

We may endow $C_c(X)$ with two topologies: one is the topology of uniform convergence inherited from $C_b(X)$. This is a Hausdorff norm-topology and as such locally convex. We note that the subspace $C_c(X)\subset C_b(X)$ equipped with the topology of uniform convergence is not complete. Its completion is denoted $C_0(X)$, and it is the subspace of $C_b(X)$ of those bounded continuous functions that vanish at $\infty$.

The other topology on $C_c(X)$ is the locally convex inductive limit topology, upon endowing each $C(X,K)$ with its norm-topology induced by the uniform norm. With this topology, $C_c(X)$ is a locally convex topological $\mathbf C$-vector space, and it is Hausdorff because this topology is finer than the topology of uniform convergence, which is Hausdorff. We refer to the locally convex inductive limit topology on $C_c(X)$ as the *inductive limit topology* on $C_c(X)$. Assuming $X$ is second-countable, so there is a *countable* cofinal system of $K$’s with respect to inclusion, the subspace topology on $C(X,K)$ from the inductive limit topology on $C_c(X)$, is its original the topology of uniform convergence by [Scha, Ch. II, 6.4] (this uses that the inclusions $C(X,K)\to C(X,K')$ for $K\subset K'$ are not only topological embeddings with respect to the uniform norm but are also closed embeddings since $C(X,K)$ is complete).

When the continuous functions on $X$ are valued in a Hausdorff locally convex topological $\mathbf C$-vector space $E$, similar notions exist and properties hold. Our main reference for the extension of these concepts to the case of $E$-valued functions is [Bou-I, Ch. III, §1].

We fix a Hausdorff locally convex topological $\mathbf C$-vector space $E$. The $\mathbf C$-vector space $C(X,E)$ of continuous $E$-valued functions is endowed with the topology generated by the collection of seminorms

$$
q_{K,\nu}(f):=\sup_{x\in K}\nu(f(x)) \tag{C.5.1.2}
$$

as $\nu$ varies over the set $S(E)$ of all continuous seminorms on $E$ ($\nu\circ f$ is continuous on $K$, hence bounded) and $K$ varies over the set $\mathcal{K}_X$ of all compact subsets of $X$.

## PDF page 721

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **721**

The family $\{q_{K,\nu}\}_{(K,\nu)\in\mathcal{K}_X\times S(E)}$ is separating because if $q_{K,\nu}(f)=0$ for all $(K,\nu)\in\mathcal{K}_X\times S(E)$ then $f(x)=0$ for all $x\in K$ and all $K\in\mathcal{K}_X$, and hence $f=0$. In particular, endowed with this topology, $C(X,E)$ is Hausdorff. We refer to this locally convex topology on $C(X,E)$ as the topology of *uniform convergence on compact subsets.*

C.5.1.1. *Properties of the spaces of continuous compactly supported $E$-valued functions.* The following is [Bou-I, Ch. III, §1.1, Def. 1].

Definition C.5.1.1. Let $X$ be a Hausdorff locally compact space and $E$ a Hausdorff locally convex topological $\mathbf C$-vector space. Let $f:X\to E$ be a continuous $E$-valued function. We define the *support* of $f$ as the closure of the open subset

$$
X_f:=X-f^{-1}(0) \tag{C.5.1.3}
$$

and denote it by $\mathrm{supp}(f)$. We say $f$ is *compactly supported* if and only if $\mathrm{supp}(f)$ is a compact subset of $X$. We denote by $C_c(X,E)$ the $\mathbf C$-vector space of all compactly supported $E$-valued continuous functions on $X$, and for any compact subset $K\subset X$, by $C(X,K;E)$ the linear subspace of $C_c(X,E)$ of all those compactly supported $E$-valued functions whose support is contained in $K$. We topologize $C_c(X,E)$ with the locally convex inductive limit of the topologies on $C(X,K;E)$, each induced by the family of seminorms $\{q_{K,\nu}\}_{\nu\in S(E)}$ from (C.5.1.2).

Remark C.5.1.2. On Definition C.5.1.1, we make the following observations.

(1) The subspace topology on $C_c(X,E)$ inherited from the topology on $C(X,E)$ of uniform convergence on compact subsets is locally convex. Its inductive limit topology (see [Scha, Ch. II, §6, pp. 56–60]) is also locally convex. These two topologies are generally *not* the same; we refer the reader to Example C.5.1.5. The former is coarser than the latter (i.e., the bijection $\varinjlim_K C(X,K;E)\to C_c(X,E)$ is continuous when the target has the topology of uniform convergence on compact subsets). When considering $C_c(X,E)$ as a locally convex topological $\mathbf C$-vector space, we will always be assuming that the topology it is being endowed with is the locally convex inductive limit topology.

Lemma C.5.1.3. *Let $X$ be a Hausdorff locally compact space, $E$ a Hausdorff locally convex $\mathbf C$-vector space. Then*

*(1) The locally convex topological $\mathbf C$-vector space $C_c(X,E)$ of continuous $E$-valued compactly supported functions on $X$ is Hausdorff. For any compact subset $K\subset X$, the topology induced on $C(X,K;E)$ by $C_c(X,E)$ is the topology of uniform convergence, and each of the linear subspaces $C(X,K;E)$ of $C_c(X,E)$ is closed.*

*(2) If $X$ is the topological disjoint union of an $I$-indexed family of locally compact Hausdorff spaces $\{X_i\}_{i\in I}$ then the canonical $\mathbf C$-linear map*

$$
C_c(X,E)\to\bigoplus_{i\in I}C_c(X_i,E) \tag{C.5.1.4}
$$

*is a linear topological isomorphism.*

*(3) If $X$ is paracompact and $E$ is quasi-complete then $C_c(X,E)$ is quasi-complete.*

*(4) If $X$ is paracompact then for every bounded subset $B\subset C_c(X,E)$ there exists a compact subset $K\subset X$ such that $B\subset C(X,K;E)$ (so it is bounded in $C(X,K;E)$ by (1)).*

*(5) $C_c(X,E)\subset C(X,E)$ is a dense subspace with respect to the topology of uniform convergence on compact subsets.*

*(6) If $E$ is quasi-complete, $C(X,E)$ is locally convex, Hausdorff and quasi-complete with respect to the topology of uniform convergence on compact subsets.*

The spaces of $E$-valued continuous functions discussed in the foregoing and studied in Lemma C.5.1.3 account for many spaces of vector-valued functions throughout this work. By [Bou-GT, Ch. I, §9, no. 10,

## PDF page 722

**722** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

Thm. 5], $X$ is paracompact if and only if topologically $X=\coprod X_i$ for $X_i$’s that are each covered by countably many compact subsets (so the inductive limit structure on each $C_c(X_i,E)$ in such cases is a countable strict inductive limit).

Proof. Parts (1) and (2) are [Bou-I, Ch. III, §1, Prop. 1(i)] and [Bou-I, Ch. III, §1, Prop. 1(iii)] respectively, where $C_c(X,E)$ is denoted $\mathscr K(X,E)$. Part (3) is [Bou-I, Ch. III, §1, p. III.4, Corollary], part (4) is [Bou-I, Ch. III, §1, Prop. 2(ii)], and part (5) is [Bou-I, Ch. III, §1, p. III.6, Prop. 4].

(6) : The topology of uniform convergence on compact subsets of $X$ is generated on $C(X,E)$ by the family of seminorms

$$
q_{K,i}(f):=\sup_{x\in K}\nu_i(f(x)) \tag{C.5.1.5}
$$

where $\{\nu_i\}_{i\in I}$ is a generating family for the locally convex topology on $E$. Since $E$ is Hausdorff, $\{\nu_i\}_{i\in I}$ is separating. It follows that $q_{K,i}(f)=0$ for all $i\in I$ implies $f(x)=0$ for all $x\in K$, for any compact subset $K\subset X$. This gives $f=0$, so $C(X,E)$ is Hausdorff.

Let $K\subset X$ be a compact subset. Then the restriction maps

$$
\rho_K:C(X,E)\to C(K,E)
$$

form a projective system, The topology on each $C(K,E)$ is generated the family of seminorms $\{q_{K,i}\}_{i\in I}$ from (C.5.1.5), for $K$ fixed. The topology on $C(X,E)$ is clearly the projective limit of the topologies on $C(K,E)$. By [Scha, Ch. II, 5.3], we are thereby reduced to the case $X$ is compact Hausdorff. In particular, $C(X,E)=C_c(X,E)$ and hence is quasi-complete by (3). $\square$

Remark C.5.1.4. By part (2), we see that part (4) is a special case of [Scha, Ch. II, 6.3, 6.5], a theorem of Dieudonné and Schwartz.

Example C.5.1.5 (Distinctness of the two topologies on $C_c(X,E)$). Assume $X$ is a Hausdorff, locally compact, paracompact space, and $E$ is a Fréchet space. By Lemma C.5.1.3, $C_c(X,E)$ is a *strict* locally convex inductive limit of the closed topological linear subspaces $C(X,K;E)$ (see [Scha, Ch. II, p. 57]). Every Cauchy sequence in $C_c(X,E)$ is bounded and hence contained within $C(X,K;E)$ for some compact subset $K\subset X$ and bounded there. The locally convex topological $\mathbf C$-vector space $C(X,K;E)$ is a Fréchet space, and as such, any Cauchy sequence in $C(X,K;E)$ converges in $C(X,K;E)$.

Assume that, for a locally compact Hausdorff abelian group $G$, $X$ carries a continuous free proper action of $G$. Let $K\subset X$ be a non-empty compact subset, and $f\in C_c(X,K;E)$ a fixed function. The action of $G$ by left translation provides a family of functions $f_g:=L_g(f)$, where $(L_g(f))(x)=f(g^{-1}x)$ for all $x\in X$ and each $g\in G$.

We now specialize to the case $X=\mathbf R$ and $G=\mathbf Z$ acting on $X$ by additive translation, and $E=\mathbf C$. Let $K$ be the unit interval in $\mathbf R$ and pick $f\ne 0$. Then the sequence $f_n:=L_n(f)$ in $C_c(\mathbf R)$ does not converge in $C_c(\mathbf R)$. Indeed, if it did then it would have to be contained and converge in some $C(K',\mathbf C)$ for some compact subset $K'\subset\mathbf R$, which cannot be since $\mathrm{supp}(f_n)\cap K'=\varnothing$ for all integers $n\in\mathbf Z$ with $|n|\gg 0$, and hence $\{f_n\}_{n\ge 1}$, a sequence of functions whose supports are non-empty in $\mathbf R$, cannot be contained in a single $C(K',\mathbf C)$. On the other hand, the sequence $\{f_n\}_{n\ge 1}$ tends to the constant function $0$ in $C(\mathbf R)$, and so it is a null sequence in the linear space $C_c(\mathbf R)$ endowed with the topology of uniform convergence on compact subsets.

For $E$ an arbitrary nonzero Fréchet space, choose a nonzero vector $e\in E$. The sequence $\{\phi_n\}_{n\ge 0}\subset C_c(\mathbf R,E)$ defined by $\phi_n:=f_n\otimes e$, viewed as a sequence in $C_c(\mathbf R,E)$ under the injective linear map

$$
C_c(\mathbf R)\otimes E\to C_c(\mathbf R,E)
$$

is also a sequence which does not converge to $0$ with respect to the locally convex inductive limit topology but is a null sequence in $C_c(\mathbf R,E)$ endowed with the topology of uniform convergence on compact subsets.

## PDF page 723

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **723**

A similar example can be made with $\mathbf R$ replaced by any Hausdorff locally compact space containing a non-empty open subset which is a topological manifold.

We will be henceforth assuming, unless otherwise stated, that $C_c(X,E)$ is endowed with the locally convex inductive limit topology of the topologies of uniform convergence on each $C(X,K;E)$ as in Definition C.5.1.1. We will be assuming that $C(X,E)$ is endowed, instead, with the topology of uniform convergence on compact subsets (so $C_c(X,E)\to C(X,E)$ is .continuous but generally not a topological embedding).

C.5.1.2. *Vector-valued differentiability.* We let $k$ be either one of the Archimedean topological fields $k=\mathbf R,\mathbf C$, and $E$ a Hausdorff locally convex topological $\mathbf C$-vector space. We will be closely following [Kruse, Def. 3.1] in defining three concepts of differentiability for $E$-valued functions on an open subset $\Omega\subset k^d$ for an integer $d\ge 0$.

The Hausdorff locally convex topological vector spaces throughout this subsection will still be assumed to be complex topological vector spaces even when $k=\mathbf R$, in which case for $E=\mathbf C$ the differentiable vector-valued functions discussed herein will recover the classical notion of differentiable complex-valued functions on a Euclidean space over the reals. In other words, the topological field $k$ is not the scalar field of the topological vector spaces occurring throughout this subsection: such field is always assumed to be $\mathbf C$.

We denote by $|\cdot|$ the Euclidean norm on $k$, whether real or complex. We further denote by $|\cdot|$ again, the Euclidean norm on $k^d$ for any $d\ge 0$.

Throughout this subsection, occasional references are made to the basic results on the integral in the sense of Pettis from §C.4.3: the Mean-Value Theorem (Theorem C.4.3.1; see also Theorem C.4.3.2), and the Integrability Criterion of Theorem C.4.3.5.

DEFINITION C.5.1.6 (Weak differentiability). Let $d\ge 0$ be an integer, and $\Omega\subset k^d$ an open subset. Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, and $f:\Omega\to E$ a function. We say $f$ is *weakly differentiable* over $\Omega$ if and only if for every $\varphi\in E'$, the function $\langle f,\varphi\rangle_{E,E'}:\Omega\to\mathbf C$ defined by

$$
\xi\mapsto\langle f(\xi),\varphi\rangle_{E,E'}
\tag{C.5.1.6}
$$

is once-differentiable in the ordinary sense (i.e. real-differentiable if $k=\mathbf R$, and differentiable in the complex sense if $k=\mathbf C$; see Remark C.5.1.7).

For $f$ weakly differentiable over $\Omega$, we define the function $\mathrm{D}f:\Omega\times k^d\to (E')^*$ by requiring that

$$
\langle\mathrm{D}f,\varphi\rangle_{E,E'}:=\mathrm{D}\langle f,\varphi\rangle_{E,E'}:\Omega\times k^d\to\mathbf C
\tag{C.5.1.7}
$$

be the function of $(\xi_1,\xi_2)\in\Omega\times k^d$ given by $(\xi_1,\xi_2)\mapsto\mathrm{D}_{\xi_1}\langle f,\varphi\rangle_{E,E'}(\xi_2)$, with $\mathrm{D}_{\xi_1}\langle f,\varphi\rangle_{E,E'}$ the differential of the $\mathbf C$-valued function $\langle f(\xi),\varphi\rangle_{E,E'}$ of $\xi\in\Omega$ at $\xi_1\in\Omega$.

We refer to $\mathrm{D}f$ as the *weak differential* of $f$. If $\mathrm{D}f:\Omega\times k^d\to (E')^*$ is continuous we say $f$ is *weakly continuously differentiable*.

REMARK C.5.1.7. For a scalar-valued function $f:\Omega\to\mathbf C$, $\Omega\subset k^d$ an open subset, to be differentiable “in the ordinary sense”, we mean that there exists a (clearly unique) $k$-linear map $J_{\xi_0}:k^d\to\mathbf C$ such that

$$
\lim_{\xi\to 0}\frac{f(\xi_0+\xi)-f(\xi_0)-J_{\xi_0}(\xi)}{|\xi|}
\tag{C.5.1.8}
$$

exists and vanishes. Specifically, we are not assuming that $J_{\xi_0}(\xi)\in\mathbf C$ is continuous in $(\xi_0,\xi)$; i.e., continuous as a map $\Omega\times k^d\to\mathbf C$. Differentiable “in the ordinary sense” does not mean “continuously differentiable”. In (C.5.1.8), $J_{\xi_0}(\xi)$ refers to the effect of the $k$-linear functional $J_{\xi_0}$ on the vector $\xi\in k^d$. If $k=\mathbf C$, and $f$ is complex-differentiable, then in particular we have $J_{\xi_0}(\xi)=f'(\xi_0)\xi$.

Much as for the integral in the sense of Pettis in §??, we now discuss differentiability for vector-valued functions in the weak sense first and then see when such a condition is equivalent to a stronger one.

## PDF page 724

**724** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

DEFINITION C.5.1.8 (Vector-valued differentiability). Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $d\ge 0$ an integer, $k$ either one of the fields $k=\mathbf R,\mathbf C$, endowed with their norm-topology. Let $\Omega\subset k^d$ be an open subset and $f:\Omega\to E$ be a function.

(1) $f$ is *continuously differentiable* over $\Omega$ *within $(E')^*$* if and only if:

(a) for every $\xi_1\in\Omega$, there exists a (clearly unique) $k$-linear map $\mathrm{D}_{\xi_1}f:k^d\to (E')^*$, continuous with respect to the Euclidean topology on the source and the $\sigma((E')^*,E')$-topology on the target, and such that for every $\xi_2\in k^d$, $(\mathrm{D}_{\xi_1}f)(\xi_2)$ is a continuous $(E')^*$-valued function of $\xi_1\in\Omega$, such that the limit in $(E')^*$ with respect to the $\sigma((E')^*,E')$-topology:

$$
\lim_{\xi\to\xi_1,\xi\ne\xi_1}\frac{f(\xi)-f(\xi_1)-(\mathrm{D}_{\xi_1}f)(\xi-\xi_1)}{|\xi-\xi_1|}=0
\tag{C.5.1.9}
$$

exists as an element of $(E')^*$ and it vanishes, where the limit is formed as $\xi\to\xi_1$ from within the open subset $\{\xi\in\Omega:\xi\ne\xi_1\}=\Omega-\{\xi_1\}\subset k^d$.

(b) Formation of the assignment $(\xi_1,\xi_2)\mapsto(\mathrm{D}_{\xi_1}f)(\xi_2)$ is continuous as a function $\Omega\times k^d\to (E')^*$ with respect to the product topology on the source, and the $\sigma((E')^*,E')$-topology on the target.

(2) $f$ is *Gateaux-differentiable* over $\Omega$ *within $(E')^*$* if and only if for every $(\xi_1,\xi_2)\in\Omega\times k^d$, the limit in $(E')^*$ with respect to the $\sigma((E')^*,E')$-topology:

$$
\lim_{h\to 0,h\in W}\frac{f(\xi_1+h\xi_2)-f(\xi_1)}{h}
\tag{C.5.1.10}
$$

exists as an element of $(E')^*$, where the limit is formed as $h\to 0$ over the open subset $W:=\{h\in k:h\ne 0,\xi_1+h\xi_2\in\Omega\}\subset k$.

We denote the value in $(E')^*$ of the limit in (C.5.1.10) as

$$
(\partial_{\xi_1}f)(\xi_2):=\lim_{h\to 0,h\in k,h\ne 0}\frac{f(\xi_1+h\xi_2)-f(\xi_1)}{h}
\tag{C.5.1.11}
$$

and refer to it as the *directional derivative* of $f$ at $\xi_1\in\Omega$ along $\xi_2\in k^d$.

(3) $f$ is *continuously differentiable over $\Omega$* if and only if:

(a) it is continuously differentiable over $\Omega$ within $(E')^*$.

(b) The map

$$
\Omega\times k^d\to (E')^*
\tag{C.5.1.12}
$$

given by

$$
(\xi_1,\xi_2)\mapsto(\mathrm{D}_{\xi_1}f)(\xi_2)
\tag{C.5.1.13}
$$

is valued in $E$ and continuous with respect to the Euclidean topology on the source, and the initial topology on $E$. We call the map in (C.5.1.13) the *differential* of $f$.

REMARK C.5.1.9. Since $k^d$ in Definition C.5.1.8 is a normed finite dimensional $k$-vector space, any $k$-linear map to $(E')^*$ is continuous with respect to the Euclidean topology on the source and the $\sigma((E')^*,E')$-topology on the target.

Definition C.5.1.8 is contained in [Kruse, Def. 3.1] with one difference. We are assuming that the linear differential and the limits in Definition C.5.1.8 are valued in $(E')^*$, which is complete with respect to the $\sigma((E')^*,E')$-topology, and agrees with the completion of $E$ with respect to the $\sigma(E,E')$-topology, also referred to as the *weak completion* of $E$ in [Gro-a]. We refer the reader to Lemma C.4.1.2 and Remark C.4.1.3.

The symbol $\widehat{E}$ in [Kruse, Def. 3.1] refers to the completion of $E$ as a topological vector space. Continuity of $E\to (E')^*$ for the given topology on $E$ and the weak topology $\sigma((E')^*,E')$ on the target (which is complete) induces a continuous linear map $\widehat{E}\to (E')^*$ but it may be non-injective or not a topological embedding.

## PDF page 725

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **725**

REMARK C.5.1.10. We note that if $k=\mathbf R$ and $d=2$, then upon identifying $\mathbf R^2$ with the complex plane, Gateaux-differentiability of a function $f:\mathbf C\to\mathbf C$ (choosing $E=\mathbf C$) does not imply differentiability in the complex sense, i.e. upon rethinking $f$ as a function $k^d\to\mathbf C$ with $k=\mathbf C$ and $d=1$. For $k=\mathbf C$ and $d=1$, Gateaux-differentiability amounts to differentiability in the complex sense, which we shall be discussing in §C.5.2.1.

REMARK C.5.1.11. We note that there is no continuity assumption on $f$ in any of the conditions assigned in Definition C.5.1.8.

LEMMA C.5.1.12 (On the equivalence of vector valued differentiability conditions). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $d\ge 0$ an integer, $k$ either one of the fields $k=\mathbf R,\mathbf C$ endowed with their Euclidean topology. Let $\Omega\subset k^d$ be an open subset, and $f:\Omega\to E$ a function. Then the following conditions are equivalent:*

(1) *$f$ is weakly differentiable over $\Omega$, and the differential $\mathrm{D}f:\Omega\times k^d\to (E')^*$ is continuous with respect to the product topology on the source, and the $\sigma((E')^*,E')$-topology on the target.*

(2) *$f$ is continuously differentiable over $\Omega$ within $(E')^*$.*

*If $f$ satisfies the above equivalent conditions, the weak differential satisfies:*

$$
(\mathrm{D}f)(\xi_1,\xi_2)=(\mathrm{D}_{\xi_2}f)(\xi_3)
\tag{C.5.1.14}
$$

*for every $(\xi_1,\xi_2)\in\Omega\times k^d$. Moreover, $f$ is Gateaux-differentiable within $(E')^*$.*

The following proof closely follows the proof of [Kruse, Rem. 3.2], to which we further refer the reader.

PROOF. (1) $\Rightarrow$ (2) : Assume $f$ is weakly differentiable. The weak differential $\mathrm{D}f$ exists and by assumption it is continuous with respect to the product topology on $\Omega\times k^d$ and the $\sigma((E')^*,E')$-topology on $(E')^*$. In particular, upon denoting by $i_{\xi_1}:k^d\to\Omega\times k^d$ the continuous map sending $\xi_2\in k^d$ to $(\xi_1,\xi_2)\in\Omega\times k^d$, and by $j_{\xi_2}:\Omega\to\Omega\times k^d$ the continuous map sending $\xi_1$ to $(\xi_1,\xi_2)$, both maps $(\mathrm{D}f)\circ i_{\xi_1}$ and $(\mathrm{D}f)\circ j_{\xi_2}$ are continuous as $(E')^*$-valued functions.

Moreover, by definition of weak differentiability, we have that the limit in $(E')^*$

$$
\lim_{\xi\to\xi_1,\xi\ne\xi_1}\frac{\iota_E(f(\xi))-\iota_E(f(\xi_1))-(\mathrm{D}f)(\xi_1,\xi-\xi_1)}{|\xi-\xi_1|}
\tag{C.5.1.15}
$$

exists in $(E')^*$ with respect to the $\sigma((E')^*,E')$-topology, and it vanishes. This implies that $f$ is continuously differentiable over $\Omega$ within $(E')^*$.

(2) $\Rightarrow$ (1) : Suppose $f$ is continuously differentiable over $\Omega$ within $(E')^*$. Then there exists a map:

$$
(\mathrm{D}_{(\cdot)}f)(\cdot):\Omega\times k^d\to (E')^*
\tag{C.5.1.16}
$$

separately continuous over each factor of $\Omega\times k^d$, each endowed with its topology induced from the norm on $k^d$, and the $\sigma((E')^*,E')$-topology on $(E')^*$. Moreover, the limit

$$
\lim_{\xi\to\xi_1,\xi\ne\xi_1}\frac{\iota_E(f(\xi))-\iota_E(f(\xi_1))-(\mathrm{D}_{\xi_1}f)(\xi-\xi_1)}{|\xi-\xi_1|}=0
\tag{C.5.1.17}
$$

in the topology of $\sigma((E')^*,E')$-convergence. For every $\varphi\in E'$, we may evaluate $\langle\cdot,\varphi\rangle_{(E')^*,E'}$ on (C.5.1.17), and obtain

$$
\lim_{\xi\to\xi_1,\xi\ne\xi_1}\left\langle\frac{f(\xi)-f(\xi_1)-(\mathrm{D}_{\xi_1}f)(\xi-\xi_1)}{|\xi-\xi_1|},\varphi\right\rangle_{E,E'}=\lim_{\xi\to\xi_1,\xi\ne\xi_1}\frac{\langle f(\xi),\varphi\rangle_{E,E'}-\langle f(\xi_1),\varphi\rangle_{E,E'}-\langle(\mathrm{D}_{\xi_1}f)(\xi-\xi_1),\varphi\rangle_{E,E'}}{|\xi-\xi_1|}
\tag{C.5.1.18}
$$

so the right side vanishes since the left side does by (C.5.1.17). This gives weak differentiability of $f$, and hence the weak differential is defined. By uniqueness of the differential for $\mathbf C$-valued differentiable functions

## PDF page 726

**726** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

on $\Omega$, we have that for every $\varphi\in E'$:

$$
\langle(\mathrm{D}f)(\xi_1,\xi_2),\varphi\rangle_{E,E'}=\langle(\mathrm{D}_{\xi_1}f)(\xi_2),\varphi\rangle_{E,E'}
$$

and hence (C.5.1.14) follows from the Hahn-Banach Theorem since $E$ is Hausdorff.

To see that $f$ is Gateaux-differentiable, we choose $\xi=\xi_1+h\xi_2$, and rename $\xi_2$ in (C.5.1.17) as $\xi_1$, in condition (C.5.1.9), to obtain that condition (C.5.1.10) is satisfied. $\square$

C.5.1.3. *Permanence properties of vector-valued differentiation.* We collect here basic properties of differentiability for $E$-valued functions over an open subset $\Omega\subset k^d$. Lemma C.5.1.13 below closely follows [Kruse, Rem. 3.2] and, in this form, is due to Grothendieck (see the sketch in [Gro-a, §2, Footnote 4, p. 39]).

LEMMA C.5.1.13 (On weak and strong differentiability). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $d\ge 1$ an integer, $k$ either one of the fields $k=\mathbf R,\mathbf C$, endowed with their norm-topology. Let $\Omega\subset k^d$ be an open subset, and $f:\Omega\to E$ a function. Then we have:*

(1) *If $f$ is weakly continuously differentiable (i.e., the weak derivative $\mathrm{D}f:\Omega\times k^d\to (E')^*$ exists and is continuous) then $f$ is Lipschitz-continuous (and hence continuous); i.e., for all $\xi',\xi\in\Omega$, $\xi'\ne\xi$, satisfying $|\xi'-\xi|\le 1$, the ratios:*

$$
\frac{f(\xi')-f(\xi)}{|\xi'-\xi|}
\tag{C.5.1.19}
$$

*are contained in a bounded, equivalently closed convex circled bounded, subset of $E$.*

(2) *If $f$ is weakly continuously differentiable and the weak differential $\mathrm{D}f$ is valued in $E$ and is continuous with respect to the product topology on the source, and the given topology on $E$ then $f$ is continuously differentiable over $\Omega$ and for every $(\xi_1,\xi_2)\in\Omega\times k^d$ the limit:*

$$
\lim_{h\to 0,h\in W}\frac{f(\xi_1+h\xi_2)-f(\xi_1)}{h}
\tag{C.5.1.20}
$$

*converges in $E$ to $(\mathrm{D}f)(\xi_1,\xi_2)$ with respect to the given topology on $E$, for $W\subset k$ the open subset $\{h\in k^\times:\xi_1+h\xi_2\in\Omega\}$.*

PROOF. (1) : Fix $\xi_1,\xi_2\in\Omega$ near enough so that the closed segment $[\xi_1,\xi_2]$ is contained in $\Omega$, and define $h:=|\xi_1-\xi_2|$. We consider the smooth curve $\gamma:[0,h]\to\xi_1+tu$ where $u:=(\xi_2-\xi_1)/h$. As a function of $t$, $F:t\mapsto(\mathrm{D}f)(\gamma(t),\gamma'(t))$ is valued in $(E')^*$, which is complete with respect to the $\sigma((E')^*,E')$-topology, and it is continuous since we assume $f$ is weakly continuously differentiable.

The integrability criterion of Theorem C.4.3.5 (viewing $k$-valued functions as $\mathbf C$-valued, since we have either $k=\mathbf R\subset\mathbf C$ or $k=\mathbf C$) therefore applies to $F$ and $(E')^*$, to give that the integral

$$
\int_{[0,h]}(\mathrm{D}f)(\gamma(t),\gamma'(t))\,\mathrm{d}t
$$

exists as an element of $(E')^*$, and not merely as an element of $(((E')^*)')^*$. It evaluates to

$$
\int_0^h\mathrm{D}_{\gamma(t)}\langle f,\varphi\rangle_{E,E'}(\gamma'(t))\,\mathrm{d}t=\int_0^h\frac{\mathrm{d}}{\mathrm{d}\mathrm{t}}(\langle f,\varphi\rangle_{E,E'}\circ\gamma)\,\mathrm{d}t=\langle f(\xi_2),\varphi\rangle_{E,E'}-\langle f(\xi_1),\varphi\rangle_{E,E'}
$$

since $\langle f,\varphi\rangle_{E,E'}$ is differentiable over $\Omega$ as a $\mathbf C$-valued function. As elements of $(E')^*$, we therefore have

$$
f(\xi_2)-f(\xi_1)=\int_{[0,h]}(\mathrm{D}f)(\gamma(t),\gamma'(t))\,\mathrm{d}t
\tag{C.5.1.21}
$$

where, however, the left side of (C.5.1.21) is an element of $E$. Let $K\subset (E')^*$ be the closed convex circled hull of $F([0,h])$. By continuity of $F$ (with respect to the Euclidean topology on $[0,h]$ and the $\sigma((E')^*,E')$-topology

## PDF page 727

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **727**

on $(E')^*$), $F([0,h])$ is compact and hence so is $K$ since $(E')^*$ is complete (see [Scha, Ch. III, Cor. to 4.3]). In particular, it is bounded in $(E')^*$.

By Theorem C.4.3.1, we therefore have:

$$
\int_{[0,h]}(\mathrm{D}f)(\gamma(t),\gamma'(t))\,\mathrm{d}t\in hK
\tag{C.5.1.22}
$$

and hence:

$$
\int_{[0,h]}(\mathrm{D}f)(\gamma(t),\gamma'(t))\,\mathrm{d}t\in h(K\cap E).
\tag{C.5.1.23}
$$

Since $K$ is bounded in $(E')^*$ with respect to the $\sigma((E')^*,E')$-topology, $K\cap E$ is bounded in $E$ with respect to the $\sigma(E,E')$-topology that is the subspace topology on $E$ from he $\sigma((E')^*,E')$-topology under the linear injection $\iota_E$. Thus, $K\cap E$ is bounded in $E$ for its given topology [Scha, Ch. III, 3.3], so $f$ is Lipschtiz-continuous.

(2) : By (1), $f$ is continuous. Moreover, for every $\varphi\in E'$, we have that the limit:

$$
\lim_{\xi\to\xi_1,\xi\ne\xi_1}\left\langle\frac{f(\xi)-f(\xi_1)-(\mathrm{D}_{\xi_1}f)(\xi-\xi_1)}{|\xi-\xi_1|},\varphi\right\rangle_{E,E'}
\tag{C.5.1.24}
$$

exists in $k$ and it vanishes. This means that within $(E')^*$ and with respect to the $\sigma((E')^*,E')$-topology, the limit:

$$
\lim_{\xi\to\xi_1,\xi\ne\xi_1}\frac{f(\xi)-f(\xi_1)-(\mathrm{D}f)(\xi_1,\xi-\xi_1)}{|\xi-\xi_1|}
\tag{C.5.1.25}
$$

exists and it vanishes. In particular, $f$ is differentiable over $\Omega$ within $(E')^*$. By assumption, $\mathrm{D}f$ is valued in $E$ and continuous, and so $f$ is differentiable over $\Omega$ and $\mathrm{D}f$ is its differential.

It remains to show the assertion on the mode of convergence of the limit in (C.5.1.20), which we already know exists in $(E')^*$ and is valued in $E$ by Lemma C.5.1.12, and converges with respect to the given topology on $E$.

For any distinct $\xi_1,\xi_2\in\Omega$ near enough so that $[\xi_1,\xi_2]\subset\Omega$, and $h=|\xi_1-\xi_2|$, let $\gamma:[0,h]\to\Omega$ be the smooth curve $\gamma(t)=\xi_1+(t/h)(\xi_2-\xi_1)$. Since $\mathrm{D}f$ is continuous with respect to the product topology on $\Omega\times k^d$ and the given topology on $E$, the function $(\mathrm{D}f)(\gamma(t),\gamma'(t))$ of $t\in[0,h]$ is continuous with respect to the Euclidean topology on $[0,h]$ and the given topology on $E$.

By Theorem C.4.3.5, the continuous $E$-valued function $t\mapsto F(t):=(\mathrm{D}f)(\gamma(t),\gamma'(t))-(\mathrm{D}f)(\xi_1,\gamma'(0))$ is integrable over $[0,h]$ in the sense of Pettis, and as in the proof of (1) its integral satisfies

$$
\frac{f(\gamma(h))-f(\xi_1)-(\mathrm{D}f)(\xi_1,\xi_2-\xi_1)}{h}=\frac{1}{h}\int_{[0,h]}F(t)\,\mathrm{d}t\in K\cap E
\tag{C.5.1.26}
$$

where $K$ is the closed convex circled hull of $F([0,|\xi_2-\xi_1|])$ in $(E')^*$.

We deduce from (C.5.1.26) that

$$
\frac{f(\xi_2)-f(\xi_1)-(\mathrm{D}f)(\xi_1,\xi_2-\xi_1)}{|\xi_2-\xi_1|}=\frac{1}{|\xi_2-\xi_1|}\int_{[0,|\xi_2-\xi_1|]}F(t)\,\mathrm{d}t\in K\cap E.
\tag{C.5.1.27}
$$

The subset $K\subset E$ as a closure for the given topology on $E$ by [Scha, Ch. IV, 3.1], so $K$ shrinks to $0$ in $E$ for its given topology as $\xi_2\to\xi_1$ by continuity of $F$ with respect to the given topology on $E$. Hence, as $\xi_2\to\xi_1$, the limit of the left side in (C.5.1.27) converges to $0$ in $E$ with respect to the initial topology. Replacing $\xi_2$ with $\xi+h\xi_2$ for nonzero $\xi\in k^d$ and $h\in k^\times$ sufficiently small, the left side of (C.5.1.27) is

$$
\frac{h}{|\xi_2||h|}\cdot\frac{f(\xi_1+h\xi_2)-f(\xi_1)}{h}(\mathrm{D}f)(\xi_1,\xi_2).
$$

$\square$

## PDF page 728

**728** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

We now define partial derivatives of a function $f:\Omega\to E$, with $\Omega\subset k^d$ an open subset, $d\ge 1$ an integer, and $E$ a Hausdorff locally convex topological $\mathbf C$-vector space. We further refer the reader to [Kruse, Def. 3.1(c)].

DEFINITION C.5.1.14 (Weak partial derivative operators). Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $d\ge 1$ an integer, $k$ either one of the Archimedean topological fields $k=\mathbf R,\mathbf C$, endowed with their Euclidean topology. Let $\Omega\subset k^d$ be a non-empty open subset, and $f:\Omega\to E$ a function. We call $e_i$ the $i$-th unit vector in the standard $k$-linear basis for $k^d$, for $1\le i\le d$.

We say $f$ is *weakly differentiable in the $e_i$-direction* over $\Omega$ if and only if for every $\varphi\in E'$, the function

$$
\langle f,\varphi\rangle_{E,E'}:\Omega\to\mathbf C
$$

is differentiable in the $e_i$-direction in the ordinary sense (i.e. real-differentiable if $k=\mathbf R$, and differentiable in the complex sense if $k=\mathbf C$).

For $f$ weakly differentiable in the $e_i$-direction over $\Omega$, we define the function $\mathrm{D}_if:\Omega\to (E')^*$ by

$$
\langle\mathrm{D}_if,\varphi\rangle_{(E')^*,E'}:=\mathrm{D}_i\langle f,\varphi\rangle_{E,E'}:\Omega\to\mathbf C
\tag{C.5.1.28}
$$

where the right side of (C.5.1.28) is the $i$-th partial derivative of the function $\langle f,\varphi\rangle_{E,E'}$, differentiable in the $e_i$-direction. We refer to $\mathrm{D}_if$ as the $i$-th *weak partial derivative* of $f$.

LEMMA C.5.1.15 (On weak differentiability). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $d\ge 1$ an integer, $k$ either one of the Archimedean topological fields $k=\mathbf R,\mathbf C$, endowed with their Euclidean topology. Let $\Omega\subset k^d$ be an open subset, and $f:\Omega\to E$ a function. Then the following conditions are equivalent:*

(1) *$f$ is weakly differentiable over $\Omega$, and the weak differential $\mathrm{D}f$ is a continuous function $\Omega\times k^d\to (E')^*$ with respect to the product topology on the source and the $\sigma((E')^*,E')$-topology on the target.*

(2) *$f$ satisfies the following conditions:*

(a) *$f$ is weakly differentiable in the $e_i$-direction over $\Omega$, for every $1\le i\le d$.*

(b) *$\mathrm{D}_if:\Omega\to (E')^*$ is continuous with respect to the Euclidean topology on the source and the $\sigma((E')^*,E')$-topology on the target, for every $1\le i\le d$.*

PROOF. (1) $\Rightarrow$ (2) : By assumption, the weak differential $\mathrm{D}f:\Omega\times k^d\to (E')^*$ is continuous with respect to the product topology on the source and the $\sigma((E')^*,E')$-topology on the target. It then follows that $(\mathrm{D}f)(\cdot,e_i)$ is an $(E')^*$-valued $e_i$-direction weak derivative on $\Omega$, and by hypothesis in (1) this is continuous with respect to the topology on $\Omega$ and the $\sigma((E')^*,E')$-topology on $(E')^*$. This proves that (2.a) and (2.b) hold.

(2) $\Rightarrow$ (1) : If $f$ is weakly differentiable in the $e_i$-direction for all $i$ with continuous derivatives with respect to the topology on $\Omega$ and the $\sigma((E')^*,E')$-topology on $(E')^*$ then for every $\varphi\in E'$ the function $\xi\mapsto\langle f(\xi),\varphi\rangle_{E,E'}$ admits partial derivatives at all points of $\Omega$, and they are each continuous. It is therefore differentiable on $\Omega$. Since $\varphi\in E'$ arbitrary, $f$ is weakly differentiable with $e_i$-direction weak derivative $(\mathrm{D}f)(\cdot,e_i)$. Thus, for every $\xi_2=\sum_{1\le i\le d}c_i(\xi_2)e_i\in k^d$ for $c_i(\xi_2)\in k$,

$$
\mathrm{D}f(\xi_1,\xi_2)=\sum_{1\le i\le d}c_i(\xi_2)\mathrm{D}_if(\xi_1)
\tag{C.5.1.29}
$$

since both elements of $(E')^*$ evaluate the same on all $\varphi\in E'$. Hence, $\mathrm{D}f$ is continuous with respect to the product topology on $\Omega\times k^d$ on the source and the $\sigma((E')^*,E')$-topology on the target. $\square$

LEMMA C.5.1.16 (On Gateaux-differentiability). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $d\ge 1$ an integer, $k$ either one of the fields $k=\mathbf R,\mathbf C$, endowed with their Euclidean topology. Let $\Omega\subset k^d$ be an open subset, and $f:\Omega\to E$ a function.*

## PDF page 729

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **729**

(1) *If $f$ is Gateaux-differentiable over $\Omega$ within $(E')^*$ then it is weakly differentiable in the $e_i$-direction over $\Omega$ for every $1\le i\le d$.*

(2) *If $f$ is Gateaux-differentiable over $\Omega$ within $(E')^*$ and the limit*

$$
\lim_{h\to 0,h\in k,h\ne 0}\frac{f(\xi_1+h\xi_2)-f(\xi_1)}{h}\in (E')^*
\tag{C.5.1.30}
$$

*(for each $\xi_2\in k^d$ and all $h\in k-\{0\}$ such that $\xi_1+h\xi_2\in\Omega$) is continuous as a function of $(\xi_1,\xi_2)\in\Omega\times k^d$ with respect to the product topology on $\Omega\times k^d$ on the source and the $\sigma((E')^*,E')$-topology on the target then $f$ is weakly differentiable over $\Omega$ and the directional derivative satisfies:*

$$
(\partial_{\xi_1}f)(\xi_2)=(\mathrm{D}f)(\xi_1,\xi_2)
\tag{C.5.1.31}
$$

*as elements of $(E')^*$, for every $(\xi_1,\xi_2)\in\Omega\times k^d$.*

(3) *If $f$ is Gateaux-differentiable over $\Omega$ within $(E')^*$ and the limit*

$$
\lim_{h\to 0,h\in k,h\ne 0}\frac{f(\xi_1+h\xi_2)-f(\xi_1)}{h}
\tag{C.5.1.32}
$$

*(for each $\xi_2\in k^d$ and all $h\in k-\{0\}$ such that $\xi_1+h\xi_2\in\Omega$) is $E$-valued and continuous in $\xi_1\in\Omega$ for fixed $\xi_2$ as a function with respect to the product topology on $k^d$ and the given topology on $E$ then $f$ is continuously differentiable over $\Omega$ and the directional derivative satisfies*

$$
(\partial_{\xi_1}f)(\xi_2)=(\mathrm{D}_{\xi_1}f)(\xi_2)=(\mathrm{D}f)(\xi_1,\xi_2)
\tag{C.5.1.33}
$$

*in $E$ for every $(\xi_1,\xi_2)\in\Omega\times k^d$.*

PROOF. (1) : In (C.5.1.10) from Definition C.5.1.8(2), we choose $\xi_2=e_i\in k^d\subset\mathbf C^d$ for each $1\le i\le d$. Upon evaluating the arbitrary $\varphi\in E'$ on (C.5.1.10), by linearity and continuity of $\varphi$ we obtain that $f$ is weakly differentiable in the $e_i$-direction over $\Omega$.

(2) : We let $i$ be an integer with $1\le i\le d$, and choose $\xi_2=e_i$ in (C.5.1.32). We define:

$$
(\partial_if)(\xi_1):=\lim_{h\to 0,h\in k,h\ne 0}\frac{f(\xi_1+he_i)-f(\xi_1)}{h}
$$

an element of $(E')^*$ whose formation varies continuously with respect to $\xi_1\in\Omega$. For $\varphi\in E'$ arbitrary, we have:

$$
\langle\partial_if,\varphi\rangle_{E,E'}=\left\langle\lim_{h\to 0,h\in k,h\ne 0}\frac{f(\xi_1+he_i)-f(\xi_1)}{h},\varphi\right\rangle_{E,E'}
$$

$$
=\lim_{h\to 0,h\in k,h\ne 0}\frac{\langle f(\xi_1+he_i),\varphi\rangle_{E,E'}-\langle f(\xi_1),\varphi\rangle_{E,E'}}{h}
$$

$$
=\partial_i\langle f,\varphi\rangle_{E,E'}
$$

where $\partial_i\langle f,\varphi\rangle_{E,E'}$ denotes the $i$th partial derivative of the function $\xi\mapsto\langle f(\xi),\varphi\rangle_{E,E'}$, and we have used continuity of $\varphi$ to exchange the order of formation of the limit and of the evaluation pairing, and linearity to evaluate the pairing $(f(\xi_1+he_i)-f(\xi_1)/h$. In other words, the $\mathbf C$-valued function $\xi\mapsto\langle f(\xi),\varphi\rangle_{E,E'}$ is differentiable in the $e_i$-direction with continuous partial derivative, for each $1\le i\le d$. It is therefore differentiable over $\Omega$, and hence $f$ is weakly differentiable over $\Omega$. The identity in (C.5.1.31) follows upon evaluation of both sides on an arbitrary $\varphi\in E'$.

## PDF page 730

**730** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

(3) : By (2), $f$ is weakly differentiable over $\Omega$. In particular, the weak differential $\mathrm{D}f$ is defined. We compute, for $\varphi\in E'$ arbitrary:

$$
\left\langle\lim_{h\to 0,h\in k,h\ne 0}\frac{f(\xi_1+h\xi_2)-f(\xi_1)}{h},\varphi\right\rangle_{E,E'}=\lim_{h\to 0,h\in k,h\ne 0}\frac{\langle f(\xi_1+h\xi_2),\varphi\rangle_{E,E'}-\langle f(\xi_1),\varphi\rangle_{E,E'}}{h}
\tag{C.5.1.34}
$$

$$
=\mathrm{D}_{\xi_1}\langle f,\varphi\rangle_{E,E'}(\xi_2)
$$

$$
=\langle(\mathrm{D}f)(\xi_1,\xi_2),\varphi\rangle_{E,E'}
$$

where $\mathrm{D}_{\xi_1}\langle f,\varphi\rangle_{E,E'}(\xi_2)$ is the ordinary differential of the function $\xi\mapsto\langle f(\xi),\varphi\rangle_{E,E'}$ at the point $\xi_1\in\Omega$ and evaluated on the $k$-linear tangent vector $\xi_2$. By the Hahn-Banach Theorem, $(\mathrm{D}f)(\xi_1,\xi_2)$ equals the limit in (C.5.1.33) as an element of $(E')^*$ and is also given by (C.5.1.29) , so the $E$-valued $\mathrm{D}f$ is continuous using the given topology on $E$. $\square$

We collect here for later use two important permanence properties of directional derivatives for functions valued in a Hausdorff locally convex topological $\mathbf C$-vector space:

LEMMA C.5.1.17 (Permanence properties of vector-valued differentiability). *Let $E$ be a Hausdorff locally convex topological $\mathbf C$-vector space, $k$ either one of the fields $k=\mathbf R,\mathbf C$, endowed with their Euclidean topology. Let $\Omega_1,\Omega_2\subset k^d$ be open subsets, and $f:\Omega_2\to E$ a function. Let $\phi:\Omega_1\to\Omega_2$ be a differentiable function. Then:*

(1) *If $f$ is weakly differentiable over $\Omega_2$, so is $f\circ\phi$ over $\Omega_1$.*

(2) *If $f$ is differentiable over $\Omega_2$ then so is $f\circ\phi$ and we have*

$$
\mathrm{D}(f\circ\phi)=(\mathrm{D}f)(\phi,\mathrm{D}\phi):\Omega_1\times k^d\to E
\tag{C.5.1.35}
$$

*where $\mathrm{D}\phi:\Omega_1\times k^d\to k^d$ is the ordinary differential of the smooth function $\phi$ and (as $E$-valued functions over $\Omega_1\times k^d$)*

$$
(\mathrm{D}_{\xi_1}(f\circ\phi))(\xi_2)=(\mathrm{D}_{\phi(\xi_1)}f)((\mathrm{D}_{\xi_1}\phi)(\xi_2)).
\tag{C.5.1.36}
$$

REMARK C.5.1.18. When writing $(\phi,\mathrm{D}\phi):\Omega_1\times k^d\to\Omega_2\times k^d$, it is understood that the dependency on $\Omega_1$ of $\phi$ and $\mathrm{D}\phi$ is, for both, through the same copy of $\Omega_1$. That is to say that, as a function $\Omega_1\times k^d\to\Omega_2\times k^d$, we write $(\phi,\mathrm{D}\phi)$ to mean $(\xi_1,\xi_2)\mapsto(\phi(\xi_1),(\mathrm{D}\phi)(\xi_1,xi_2)$.

PROOF. (1) : If $f$ is weakly differentiable over $\Omega_2$ then for any $\varphi\in E'$ the function $\langle f,\varphi\rangle_{E,E'}:\Omega\to k$ is differentiable and hence so is the composition $\langle f,\varphi\rangle_{E,E'}\circ\phi=\langle f\circ\phi,\varphi\rangle_{E,E'}$. Since $\varphi$ is arbitrary, $f\circ\phi$ is weakly differentiable.

(2) : By (1), $f\circ\phi$ is weakly differentiable. The weak differential $\mathrm{D}f$ is therefore defined. Let $\varphi\in E'$ be the arbitrary continuous linear form on $E$. We compute, for every $(\xi_1,\xi_2)\in\Omega_1\times k^d$:

$$
\langle\mathrm{D}(f\circ\phi)(\xi_1,\xi_2),\varphi\rangle_{E,E'}=\mathrm{D}_{\xi_1}\langle f\circ\phi,\varphi\rangle_{E,E'}(\xi_2)
$$

$$
=(\mathrm{D}_{\phi(\xi_1)}\langle f,\varphi\rangle_{E,E'})((\mathrm{D}_{\xi_1}\phi)(\xi_2))
$$

$$
=\langle(\mathrm{D}f)(\phi(\xi_1),(\mathrm{D}_{\xi_1}\phi)(\xi_2)),\varphi\rangle_{E,E'}
$$

where the last term equals $(\mathrm{D}f)\circ(\phi,\mathrm{D}\phi):\Omega_1\times k^d\to (E')^*$ pointwise on $\Omega_1\times k^d$. Moreover, since $\mathrm{D}f:\Omega_2\times k^d\to E$ is $E$-valued and continuous with respect to the given topology on $E$ and $(\phi,\mathrm{D}\phi):\Omega_1\times k^d\to\Omega_2\times k^d$ is continuous, we deduce that the left side of (C.5.1.35) is $E$-valued and continuous with respect to the product topology on $\Omega_1\times k^d$ on the source and the given topology on $E$. This proves that $f\circ\phi$ is differentiable and that (C.5.1.36) holds. $\square$

In the Lemma below, we denote by $\mathrm{d}t$ the Lebesgue measure on the real $t$-line, restricted to any interval, normalized so as to give the unit interval $[0,1]$ volume $1$.

## PDF page 731

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **731**

**Lemma C.5.1.19 (Vector-valued Fundamental Theorem of Calculus).** *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $k$ either one of the fields $k = \mathbf{R}, \mathbf{C}$, endowed with their Euclidean topology. Let $d \ge 1$ be an integer. Let $\Omega \subset k^d$ be an open subset, and $f : \Omega \to E$ a function. Let $\gamma : (a_0, b_0) \to \Omega$ a once-differentiable function, with $a_0, b_0 \in \mathbf{R}$, $a_0 < b_0$. Let $[a, b] \subset (a_0, b_0)$ be a non-empty closed interval. Assume:*

(1) *$f$ is continuously differentiable over an open neighborhood of $\gamma([a, b])$.*

(2) $E$ is quasi-complete.

*Then the $E$-valued derivative $(f \circ \gamma)'(t) = (\mathrm{D}f)(\gamma(t), \gamma'(t))$ is continuous on $[a, b]$ and integrable, and we have*

$$
\int_{[a,b]} (\mathrm{D}f)(\gamma(t), \gamma'(t))\, \mathrm{d}t = f(\gamma(b)) - f(\gamma(a)). \tag{C.5.1.37}
$$

**Remark C.5.1.20.** Recall that “integrable” in the statement of Lemma C.5.1.19 refers to integrability in the sense of Pettis, defined in Definition C.4.2.1.

*Proof.* Since $f$ is differentiable over an open neighborhood of $\gamma([a, b])$ within $\Omega$, then function $(\xi_1, \xi_2) \mapsto (\mathrm{D}_{\xi_1}f)(\xi_2)$ is continuous as a function $\Omega \times k^d \to E$, with respect to the product topology on the source and the initial topology on $E$. Since the function $t \mapsto (\gamma(t), \gamma'(t))$ is also continuous as a function $(a_0, b_0) \to \Omega \times k^d$, as $\gamma : (a_0, b_0) \to \Omega$ is differentiable, it follows that the composition $(\mathrm{D}_{\gamma(t)}f)(\gamma'(t))$ is continuous over $(a_0, b_0)$. We now note that since $f$ is differentiable in an open neighborhood of $\gamma([a, b])$, it is weakly differentiable over an open neighborhood of $\gamma([a, b])$ within $\Omega$, and hence by (C.5.1.14) from Lemma C.5.1.12 and pointwise over $\Omega \times k^d$ we have

$$(\mathrm{D}f)(\xi_1, \xi_2) = (\mathrm{D}_{\xi_1}f)(\xi_2)$$

as elements of $(E')^*$, and by differentiability both sides are in fact elements of $E$. It follows that, as $\mathrm{D}f$ is continuous over an open neighborhood of $\gamma([a, b])$ and hence $(\mathrm{D}f)(\gamma(t), \gamma'(t))$ is continuous over $[a, b]$, that, being $E$ quasi-complete, Lemma C.4.3.5 applies and it gives that $(\mathrm{D}f)(\gamma(t), \gamma'(t))$ is integrable over $[a, b]$. We now compute its integral: for the arbitrary $\varphi \in E'$, we have

$$
\left\langle \int_{[a,b]} (\mathrm{D}f)(\gamma(t), \gamma'(t))\, \mathrm{d}t, \varphi \right\rangle_{E,E'} = \int_{[a,b]} \langle (\mathrm{D}f)(\gamma(t), \gamma'(t)) \rangle_{E,E'}\, \mathrm{d}t = \int_{[a,b]} \mathrm{D}_{\gamma(t)}\langle f(\gamma(t)), \varphi \rangle_{E,E'}(\gamma'(t))\, \mathrm{d}t = \int_a^b \frac{\mathrm{d}}{\mathrm{d}t}(\langle f \circ \gamma, \varphi \rangle)\, \mathrm{d}t = \langle f(\gamma(b)), \varphi \rangle_{E,E'} - \langle f(\gamma(a)), \varphi \rangle_{E,E'}
$$

by the Fundamental Theorem of Calculus. Since the space $E'$ separates the points of $E$, (C.5.1.37) holds. $\square$

C.5.1.4. *Vector-valued differentiability criterion.* We will now discuss a differentiability criterion, extending Lemma C.5.1.13 to higher order directional derivatives. Such a criterion will hold under the additional assumption on the Hausdorff locally convex topological $\mathbf{C}$-vector space $E$ being quasi-complete. The following Lemma is the key ingredient upon which the differentiability criterion of Theorem C.5.1.24 below rests.

We record here the following consequence of Lemma C.5.1.12, Lemma C.5.1.13, Lemma C.5.1.15 and Lemma C.5.1.16:

**Theorem C.5.1.21 (Strong vector-valued differentiability).** *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $d \ge 1$ an integer, $k$ either one of the Archimedean topological fields $k = \mathbf{R}, \mathbf{C}$, endowed with their Euclidean topology. Let $\Omega \subset k^d$ be an open subset, $f : \Omega \to E$ a function. The following conditions are equivalent:*

## PDF page 732

**732** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

(1) $f$ is continuously differentiable over $\Omega$.

(2) *$f$ is weakly differentiable, the weak differential $\mathrm{D}f : \Omega \times k^d \to (E')^*$ is valued in $E$ and continuous with respect to the product topology on the source and the initial topology on the target $E$.*

(3) *$f$ is weakly differentiable in the $e_i$-direction for each $1 \le i \le d$, and each of the directional derivatives $\mathrm{D}_i f$ is valued in $E$ and continuous with respect to the Euclidean topology on $\Omega$ and the initial topology on $E$.*

(4) *$f$ is Gateaux-differentiable within $(E')^*$, and the limit*

$$
\lim_{h \to 0, h \in W} \frac{f(\xi_1 + h\xi_2) - f(\xi_1)}{h} \tag{C.5.1.38}
$$

*(with $W \subset k$ the subset $W := \{h \in k : h \ne 0, \xi_1 + h\xi_2 \in \Omega\}$) is, as a function of $(\xi_1, \xi_2) \in \Omega \times k^d$, valued in $E$ and continuous with respect to the product topology on the source and the given topology on $E$.*

*Proof.* If (1) holds then $f$ is weakly differentiable by Lemma C.5.1.12((2) $\Rightarrow$ (1)) and the weak differential $\mathrm{D}f$ agrees with the differential in (1), which implies the continuity assertion on $\mathrm{D}f$ as a function $\Omega \times k^d \to E$. Thus, (1) implies (2).

If (2) holds then $f$ is weakly differentiable in the $e_i$-direction by Lemma C.5.1.15, and by (C.5.1.14) each $\mathrm{D}_i f$ is valued in $E$ and continuous with respect to the Euclidean topology on $\Omega$ and the initial topology on $E$. This implies that (3) holds.

If (3) holds, then since $\mathrm{D}f = \sum_{1 \le i \le d} c_i \mathrm{D}_i f$, for $c_i \in (k^d)^*$ the $i$-th coordinate projection linear form, i.e. for each $(\xi_1, \xi_2) \in \Omega \times k^d$ we have:

$$\mathrm{D}f(\xi_1, \xi_2) = \sum_{1 \le i \le d} c_i(\xi_2) \mathrm{D}_i f(\xi_1)$$

and each $c_i$ is continuous, we deduce from (3) that $\mathrm{D}f$ is valued in $E$ and continuous with respect to the product topology on $\Omega \times k^d$ and the given topology on $E$. We deduce that $f$ is weakly continuously differentiable and by Lemma C.5.1.13(2) is continuously differentiable over $\Omega$, so (1) holds.

If (4) holds then by Lemma C.5.1.16(3) so does (1). If (1) holds then by Lemma C.5.1.13(2) we get (4). $\square$

We will now be discussing an important differentiability criterion in the special case $E$ is quasi-complete, due to Grothendieck (see [Gro-a, §2, Footnote 4, p. 39]) and whose proof is recorded in more detail by Schwartz in [Sch-b, Appendice, Lemma II, p. 146]. We’ll give a somewhat different proof below. Before we do so, we include below a result on removable singularities for vector-valued functions, smooth away from an isolated point, adapting an argument from [Ga-2, §15.1].

**Lemma C.5.1.22 (Removable singularities in dimension $d = 1$).** *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $k$ either one of the fields $k = \mathbf{R}, \mathbf{C}$, endowed with their Euclidean topology. Let $\Omega \subset k$ be an open subset, and $\xi_0 \in \Omega$ a point. Let $f : \Omega - \{\xi_0\} \to E$ be a function. Assume:*

(1) $E$ is quasi-complete.

(2) For every $\varphi \in E'$, the function

$$
\langle f, \varphi \rangle_{E,E'} : \Omega - \{\xi_0\} \to \mathbf{C} \tag{C.5.1.39}
$$

*defined as $\xi \mapsto \langle f(\xi), \varphi \rangle_{E,E'}$ is continuously differentiable, and it extends to a continuously differentiable scalar-valued function over $\Omega$.*

*Then there exists a unique continuous function $F : \Omega \to E$ extending $f$. Moreover, $F$ is weakly continuously differentiable over $\Omega$.*

*Proof.* By Lemma C.5.1.13, $f$ is continuous over $\Omega - \{\xi_0\}$ because it is weakly differentiable over $\Omega - \{\xi_0\}$. We let $B$ be a small open ball around $\xi_0$ whose closure is contained in $\Omega$.

## PDF page 733

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **733**

We consider the following function:

$$
G : (\Omega - \{\xi_0\}) \times (\Omega - \{\xi_0\}) - \Delta(\Omega - \{\xi_0\}) \to E \tag{C.5.1.40}
$$

defined as

$$
G(\xi_1, \xi_2) := \frac{f(\xi_1) - f(\xi_2)}{\xi_1 - \xi_2} \tag{C.5.1.41}
$$

where $\Delta(\Omega - \{\xi_0\})$ is the diagonal in $(\Omega - \{\xi_0\}) \times (\Omega - \{\xi_0\})$. Define the notation

$$U := (\Omega - \{\xi_0\}) \times (\Omega - \{\xi_0\}) - \Delta(\Omega - \{\xi_0\})$$

and

$$C := (B - \{\xi_0\}) \times (B - \{\xi_0\}) - \Delta((\Omega - \{\xi_0\}) \cap B) = U \cap (B \times B) \subset U.$$

Since $f$ is continuous on $\Omega - \{\xi_0\}$, so is $G$.

By assumption (2), for any $\varphi \in E'$ the function $\langle G, \varphi \rangle_{E,E'} : U \to \mathbf{C}$ is

$$\int_0^1 \langle f, \varphi \rangle'_{E,E'}(\xi_2 + t(\xi_1 - \xi_2))\, \mathrm{d}t,$$

which is a continuous function over $\Omega \times \Omega$ since the function $\langle f, \varphi \rangle_{E,E'}$ has a continuously differentiable extension across $\xi_0$.

It follows that $\langle G(C), \varphi \rangle_{E,E'}$ is a bounded subset of $\mathbf{C}$. Since $\varphi \in E'$ is arbitrary, $G(C)$ is bounded with respect to the $\sigma(E, E')$-topology on $E$, so it is bounded with respect to the given topology on $E$ [Scha, Ch. IV, 3.3].

We let $A$ be its (bounded!) closed convex circled hull in $E$. For any $(\xi_1, \xi_2) \in B - \{x\text{ß}_0\}$ we therefore have, in light of the design of $G$ from (C.5.1.41) (treating $\xi_1 \ne \xi_2$ separately from $\xi_1 = \xi_2$)

$$
f(\xi_1) - f(\xi_2) \in (\xi_1 - \xi_2)A \subset E. \tag{C.5.1.42}
$$

For any Cauchy sequence $\{\xi'_k\}_{k \ge 0}$ contained in $\Omega - \{\xi_0\}$ and converging to $\xi_0$, it follows from (C.5.1.42) that $\{f(\xi'_k)\}_{k \ge 0}$ is a Cauchy sequence in $E$.

Since $E$ is quasi-complete and Cauchy sequences are bounded, $\{f(\xi'_k)\}$ converges. We define $F(\xi_0)$ to be its limit. The containment in (C.5.1.42) implies that $F(\xi_0)$ does not depend on the choice of convergent Cauchy sequence $\{\xi'_k\}_{k \ge 0}$, and $F$, thus defined at $\xi_0$, is sequentially continuous at $\xi_0$ and hence over $\Omega$ upon defining $F := f$ over $\Omega - \{\xi_0\}$. Thus, $F$ is continuous.

We let $\varphi$ be the arbitrary continuous functional on $E$. Clearly the continuous function $\langle F, \varphi \rangle_{E,E'}$ is the unique continuous extension of $\langle f, \varphi \rangle_{E,E'} : \Omega - \{\xi_0\} \to \mathbf{C}$ to $\Omega$. That continuous extension is continuously differentiable by hypothesis, so $F$ is weakly differentiable. $\square$

**Definition C.5.1.23 (Order-$m$ differentiability).** Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $k$ either one of the fields $k = \mathbf{R}, \mathbf{C}$, endowed with their Euclidean topology. Let $\Omega \subset k^d$ be an open subset, and $f : \Omega \to E$ a function. Let $m \ge 1$ be an integer. If $m = 0$, we say that $f$ is continuously differentiable $0$ times if and only if $f$ is Lipschitz-continuous, i.e. for any $\xi, \xi' \in \Omega$, $\xi \ne \xi'$, such that $|\xi' - \xi| \le 1$, the ratio:

$$
\frac{f(\xi') - f(\xi)}{|\xi' - \xi|} \tag{C.5.1.43}
$$

is contained in a bounded subset of $E$.

If $m \ge 1$, we say that $f$ is continuously differentiable $m$ times if and only if:

(1) $f$ is weakly differentiable in the $e_i$-direction for $1 \le i \le d$.

(2) For every $1 \le i \le d$, the directional derivatives $\mathrm{D}_i f$ is valued in $E$ and continuous with respect to the Euclidean topology on $\Omega$ and the initial topology on $E$.

## PDF page 734

**734** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

(3) For every $1 \le i \le d$, the directional derivatives $\mathrm{D}_i f$ is continuously differentiable $m - 1$ times.

We say $f$ is infinitely differentiable, or smooth, if and only if for every integer $m \ge 0$, $f$ is continuously differentiable $m$ times.

We denote by $C^m(\Omega, E)$ the $\mathbf{C}$-vector space of $E$-valued functions continuously differentiable $m$ times, and by $C^\infty(\Omega, E)$, equivalently $\mathcal{E}(\Omega, E)$, the $\mathbf{C}$-vector space of infinitely differentiable $E$-valued functions.

The following result is due to Grothendieck, and it is recorded in [Sch-b, Appendice, Lemme II, p. 146].

**Theorem C.5.1.24.** *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $k$ either one of the fields $k = \mathbf{R}, \mathbf{C}$, endowed with their Euclidean topology. Let $\Omega \subset k^d$ be an open subset and $f : \Omega \to E$ a function. Assume that $E$ is quasi-complete. Let $m \ge 1$ be an integer. If for every $\varphi \in E'$, the function $\langle f, \varphi \rangle_{E,E'}$ is continuously differentiable $m$ times, then $f$ is differentiable $m - 1$ times.*

*Proof.* Since $m \ge 1$, from Lemma C.5.1.13(1) we deduce that $f$ is Lipschitz-continuous. This proves the case $m = 1$.

We now assume $m > 1$ and proceed by induction on $m$. We consider the function, for each $(\xi_1, \xi_2) \in \Omega \times k^d$:

$$
F(h) := \frac{f(\xi_1 + h \xi_2) - f(\xi_1)}{h} = \int_0^1 (\mathrm{D}f)(\xi_1 + th\xi_2, \xi_2)\, \mathrm{d}t \tag{C.5.1.44}
$$

(as a Pettis intgeral with weakly continuously differentiable integrant valued in $E$, with $F(0) = (\mathrm{D}f)(\xi_1, \xi_2) \in (E')^*$) defined on $h \in k - \{0\}$ such that $\xi_1 + h \xi_2 \in \Omega$. This set of elements $W \subset k$ is open since $\Omega \subset k^d$ is open.

For $\varphi \in E'$,

$$\langle F, \varphi \rangle(h) = \int_0^1 \mathrm{D}(\langle f, \varphi \rangle)(\xi_1 + th\xi_2, \xi_2)\, \mathrm{d}t$$

with integrand that is $C^1$ in $(t, h)$ since $\langle f, \varphi \rangle$ is $C^2$, so $\langle F, \varphi \rangle$ is $C^1$ in $h$ near $0$. Thus, Lemma C.5.1.22 applies to $F$, giving a continuous extension across $h = 0$ valued in $E$.

We claim $f$ satisfies the assumptions of Lemma C.5.1.16(3) with (C.5.1.32) equal to $(\mathrm{D}f)(\xi_1, \xi_2)$. Indeed, formation of the directional derivative $(\partial_{\xi_1}f)(\xi_2)$ is, for each fixed $\xi_2 \in k^d$, continuous as an $E$-valued function of $\xi_1$ with respect to the given topology on $E$ by Lemma C.5.1.13(1) applied to $\xi_1 \mapsto (\partial_{\xi_1}f)(\xi_2)$. Then Lemma C.5.1.16(3) applies to give $f$ is $C^1$ with values in $E$.

We have shown that for each integer $1 \le i \le d$, $\mathrm{D}_i f$ is valued in $E$ and continuous with respect to the Euclidean topology on $\Omega$ and the initial topology on $E$. Note that for each integer $1 \le i \le d$, the function $\mathrm{D}_i f$ is $E$-valued, continuous, and weakly continuously differentiable $m - 1$ times. By inductive hypothesis, it is continuously differentiable $m - 2$ times. We have therefore shown that $f$ is continuously differentiable $m - 1$ times. $\square$

**Corollary C.5.1.25 (On the agreement of the concepts of $E$-valued smoothness).** *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space. Let $d \ge 1$ be an integer, $k$ either one of the two Archimedean topological field $k = \mathbf{R}, \mathbf{C}$, endowed with their Euclidean topology.*

*Let $\Omega \subset k^d$ be an open subset, $f : \Omega \to E$ a function. Assume $E$ is quasi-complete. Then, the following conditions are equivalent:*

(1) $f$ is infinitely differentiable.

(2) *For every $\varphi \in E'$, the $\mathbf{C}$-valued function $\langle f, \varphi \rangle_{E,E'}$ on $\Omega$ is infinitely differentiable, i.e. an element of $C^\infty(\Omega)$.*

Note that for $d = 1$ and $k = \mathbf{C}$, this implies that the weakly infinitely differentiable $E$-valued functions on $\Omega$ are exactly the holomorphic $E$-valued functions (see Definition C.5.2.1(4)).

The concept of vector-valued infinite differentiability defined in [Tre, Def. 40.1] is the same as the one in Definition C.5.1.23. The one in force throughout [Sch-b] is the “weak” notion in Corollary C.5.1.25(2),

## PDF page 735

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **735**

so for $E$ quasi-complete the two notions are equivalent by Corollary C.5.1.25. We may define a concept of infinite differentiability in the sense of Gateaux, building on Lemma C.5.1.16 (requiring directional derivatives to be $E$-valued and weakly continuous on $\Omega$), and Corollary C.5.1.25 implies that for $E$ quasi-complete it is equivalent to infinite differentiability as defined in Definition C.5.1.23.

For the purposes of this work, $E$ will always be quasi-complete. Thus, there will be no ambiguity as to the meaning of “smooth $E$-valued function”.

C.5.1.5. *Spaces of smooth vector-valued functions.* In this subsection we record a few facts about spaces of smooth vector-valued functions with values in a Hausdorff locally convex quasi-complete topological $\mathbf{C}$-vector space $E$.

Recall that we write $\mathbf{T}$ for the 1-dimensional compact real torus $\mathbf{R}/\mathbf{Z}$, which is smoothly isomorphic to $\mathrm{U}(1)$ under the exponential function $t \mapsto \exp(2\pi i t)$.

**Definition C.5.1.26 (Vector-valued smooth function spaces).** Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $d \ge 0$ an integer. Assume $E$ is quasi-complete. We define:

(1) $\mathcal{S}(\mathbf{T}^d, E)$ to be the linear subspace of $C^\infty(\mathbf{R}^d, E)$ of those $E$-valued smooth functions that are invariant under the continuous left-translation action of the discrete co-compact closed subgroup $\mathbf{Z}^d \subset \mathbf{R}^d$.

We topologize $\mathcal{S}(\mathbf{T}^d, E)$ with the unique Hausdorff topological vector space structure for which a net $\{f_i\}_{i \in I} \subset \mathcal{S}(\mathbf{T}^d, E)$ converges to $0$ in $\mathcal{S}(\mathbf{T}^d, E)$ if and only if for every $\varphi \in E'$, the net of smooth complex-valued functions $\{\langle f_i, \varphi \rangle_{E,E'}\}_{i \in I}$ converges to $0$ with respect to the topology of uniform convergence over $\mathbf{T}^d$, uniformly as $\varphi$ varies over each equicontinuous subset of $E'$.

(2) $\mathcal{S}(\mathbf{R}^d, E)$ to be the linear subspace of those $f \in C^\infty(\mathbf{R}^d, E)$ such that for any complex-valued polynomial function $p$ on $\mathbf{R}^d$, and every integral multi-index $\alpha \in \mathbf{N}^d$, $p \cdot \mathrm{D}^\alpha f$ takes values in a bounded subset of $E$, where $\mathrm{D}^\alpha := \prod_{1 \le i \le d} \mathrm{D}_i^{\alpha_i}$ (the boundedness can be checked weakly, by [Scha, Ch. IV, 3.3]).

We topologize $\mathcal{S}(\mathbf{R}^d, E)$ with the unique Hausdorff topological vector space structure for which a net $\{f_i\}_{i \in I} \subset \mathcal{S}(\mathbf{R}^d, E)$ converges to $0$ in $\mathcal{S}(\mathbf{R}^d, E)$ if and only if for every $\varphi \in E'$, the net of smooth complex-valued functions $\{\langle f_i, \varphi \rangle_{E,E'}\}_{i \in I}$ converges to $0$ with respect to the topology of uniform convergence over $\mathbf{R}^d$, uniformly as $\varphi$ varies over each equicontinuous subset of $E'$.

**Remark C.5.1.27.** Definition C.5.1.26 makes sense for an arbitrary Hausdorff locally convex topological $\mathbf{C}$-vector space $E$ (no quasi-completeness hypothesis) by defining smooth $E$-valued functions as those that are weakly infinitely differentiable and by defining the two respective function spaces $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$ as the linear subspaces of $C^\infty(\mathbf{R}^n, E)$ of those smooth $E$-valued functions $f : \mathbf{R}^d \to E$ such that for any $\varphi \in E'$, the complex-valued smooth function $\langle f, \varphi \rangle_{E,E'}$ is $\mathbf{Z}^d$-invariant over $\mathbf{R}^d$, respectively Schwartz over $\mathbf{R}^d$.

This latter way to define $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$ is denoted in [Sch-b, §1, p. 102] by $\widetilde{\mathrm{H}}^d(E)$ for $\mathrm{H}$ either $\mathcal{S}(\mathbf{T}^d)$ or $\mathcal{S}(\mathbf{R}^d)$. By [Sch-b, Prop. 8, p. 104], for $E$ quasi-complete this definition and Definition C.5.1.26 are equivalent; see also Corollary C.5.1.25, and [Sch-b, Prop. 4, p. 97].

**Remark C.5.1.28 (Fundamental families of seminorms for $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$).** In light of Lemma C.2.2.2, the topology thus defined on $\mathcal{S}(\mathbf{T}^d, E)$, respectively $\mathcal{S}(\mathbf{R}^d, E)$, is locally convex: for $\{q_i\}_{i \in I}$ a fundamental family of continuous seminorms for $E$, a fundamental family of seminorms for $\mathcal{S}(\mathbf{T}^d, E)$ is assigned on each $f \in \mathcal{S}(\mathbf{T}^d, E)$ by

$$
\sup_{x \in \mathbf{T}^d} q_i(\mathrm{D}^\alpha f), \quad i \in I, \, \alpha \in \mathbf{N}^d \tag{C.5.1.45}
$$

and for $\mathcal{S}(\mathbf{R}^d, E)$ is assigned on each $f \in \mathcal{S}(\mathbf{R}^d, E)$ by

$$
\sup_{x \in \mathbf{R}^d} q_i(p \cdot \mathrm{D}^\alpha f), \quad i \in I \tag{C.5.1.46}
$$

## PDF page 736

**736** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

as $p$ varies over all complex-valued polynomial functions on $\mathbf{R}^d$, equivalently over all monomial functions over $\mathbf{R}^d$, and $\alpha \in \mathbf{N}^d$ is an arbitrary multi-index.

**Remark C.5.1.29.** Definition C.5.1.26 makes sense for the arbitrary Hausdorff locally convex topological $\mathbf{C}$-vector space $E$, by defining smooth $E$-valued functions as being those that are weakly infinitely differentiable, and by defining each of the two function spaces $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$ as being the linear subspaces of $C^\infty(\mathbf{R}^n, E)$ of those smooth $E$-valued functions $f : \mathbf{R}^d \to E$ such that for any $\varphi \in E'$, the complex-valued smooth function $\langle f, \varphi \rangle_{E,E'}$ is $\mathbf{Z}^d$-invariant over $\mathbf{R}^d$, respectively Schwartz over $\mathbf{R}^d$.

This latter way to define $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$ is denoted in [Sch-b, §1, p. 102] by $\widetilde{\mathrm{H}}^d(E)$ for $\mathrm{H}$ either $\mathcal{S}(\mathbf{T}^d)$ or $\mathcal{S}(\mathbf{R}^d)$. By [Sch-b, Prop. 8, p. 104], for $E$ quasi-complete this definition and Definition C.5.1.26 are equivalent; see also Corollary C.5.1.25, and [Sch-b, Prop. 4, p. 97].

Most of the following properties of $\mathcal{S}(\mathbf{R}^d, E)$ are due to Schwartz, and we further refer the reader to [Sch-b, §1, p. 93].

**Theorem C.5.1.30 (Main properties of the function spaces $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$).** *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $d \ge 1$ an integer. Assume $E$ is quasi-complete.*

(1) *The spaces $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$ are quasi-complete.*

(2) *If $E$ is complete then $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$ are complete.*

(3) *If $E$ is a Fréchet space then so are $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$.*

(4) *For $d, d' \ge 1$ two integers, and $X = \mathbf{T}^d, \mathbf{R}^d$, $Y = \mathbf{T}^{d'}, \mathbf{R}^{d'}$ respectively, the injective linear map*

$$
C^\infty(X \times Y) \to C^\infty(X, C^\infty(Y)) \tag{C.5.1.47}
$$

*defined by sending a smooth complex-valued function $f(x, y)$ on $X \times Y$ to the smooth $C^\infty(Y)$-valued function $x \mapsto f(x, \cdot)$ is bijective and it is compatible with the linear subspaces $\mathcal{S}(X \times Y)$ and $\mathcal{S}(X, \mathcal{S}(Y))$, inducing a linear topological isomorphism*

$$
\mathcal{S}(X \times Y) \to \mathcal{S}(X, \mathcal{S}(Y)). \tag{C.5.1.48}
$$

*Proof.* (1) and (2): Let $\{f_i\}_{i \in I} \subset \mathcal{S}(\mathbf{R}^d, E)$ be a bounded Cauchy net. Since $\mathcal{S}(\mathbf{R}^d)$ is complete, it converges weakly; i.e., with respect to the $\sigma(\mathcal{S}(\mathbf{R}^d, E), \mathcal{S}(\mathbf{R}^d, E)')$-topology on $\mathcal{S}(\mathbf{R}^d, E)$.

Since it is bounded by assumption, for each $x \in \mathbf{R}^d$ Remark C.5.1.28 gives that $\{f_i(x)\}_{i \in I}$ is a bounded Cauchy net in $E$, which therefore converges for each $x \in \mathbf{R}^d$ since $E$ is quasi-complete. We denote by $f : \mathbf{R}^d \to E$ the limit function. For any $\varphi \in E'$, $\langle f, \varphi \rangle_{E,E'}$ is the pointwise limit of $\langle f_i, \varphi \rangle$, yet $\langle f_i, \varphi \rangle$ is Cauchy in the complete $\mathcal{S}(\mathbf{R}^d)$ and so has a limit in $\mathcal{S}(\mathbf{R}^d)$. Hence, $\langle f, \varphi \rangle$ is that limit, so it is Schwartz.

By Corollary C.5.1.25, $f$ is smooth as an $E$-valued function. For any polynomial function $p$ on $\mathbf{R}^d$ and every multi-index $\alpha \in \mathbf{N}^d$, $p \cdot \mathrm{D}^\alpha f$ takes values in a weakly bounded subset of $E$ since each $\langle f, \varphi \rangle$ is Schwartz, so $p \cdot \mathrm{D}^\alpha f$ takes values in a bounded subset of $E$ by [Scha, Ch. IV, 3.3]. We deduce that $f \in \mathcal{S}(\mathbf{R}^d, E)$. It remains to show that $f_i \to f$ in $\mathcal{S}(\mathbf{R}^d, E)$. If $\varphi \in E'$ varies over an arbitrary equicontinuous subset $A$ of $E'$ then by equicontinuity we have $\langle f_i, \varphi \rangle_{E,E'} \to \langle f, \varphi \rangle_{E,E'}$ uniformly with respect to $\varphi \in A$. We deduce that $f_i \to f$ in $\mathcal{S}(\mathbf{R}^d, E)$, by definition of the locally convex topology on $\mathcal{S}(\mathbf{R}^d, E)$.

The same argument works if $\{f_i\}_{i \in I}$ is an arbitrary (not necessarily bounded) Cauchy net in $\mathcal{S}(\mathbf{R}^d, E)$ and $E$ is complete rather than just quasi-complete.

The case of $\mathcal{S}(\mathbf{T}^d, E)$ is seen by means of the same argument: we have only used completeness of $\mathcal{S}(\mathbf{R}^d)$ and quasi-completeness, respectively completeness, of $E$.

(3): If $E$ is a Fréchet space, then since $\mathcal{S}(\mathbf{T}^d)$ and $\mathcal{S}(\mathbf{R}^d)$ are both metrizable, the description of the topology on $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$ by means of the fundamental families of continuous seminorms from (C.5.1.45) and (C.5.1.46) shows that we may choose the index sets $I$ to be countable, which proves that $\mathcal{S}(\mathbf{T}^d, E)$ and $\mathcal{S}(\mathbf{R}^d, E)$ are complete, by (2), and metrizable, hence Fréchet spaces.

## PDF page 737

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **737**

(4): Using the formula

$$\frac{f(x + he_j, y) - f(x, y)}{h} = \int_0^1 (\partial_j f)(x + the_j, y)\, \mathrm{d}t$$

one readily checks that (C.5.1.47) makes sense (i.e., $[f] : x \mapsto f(x, \cdot)$ as a map $X \to C^\infty(Y)$ satisfies $\partial_j[f] = [\partial_j f]$ and so is $C^\infty$) and is bijective. The linear map from (C.5.1.48) is continuous, by standard properties of formation of suprema of the absolute value of a continuous complex-valued function on the product and the continuity of the inverse. Surjectivity follows by similar calculations via bijectivity of (C.5.1.47) and the bijection between the seminorm formulas on both sides. $\square$

We will be using Theorem C.5.1.30(4) in Appendix D (see the proof of Lemma D.1.3.7 and the proof of Lemma D.2.2.2(1)), to define the tensor product of tempered distributions on pairs of elementary abelian Lie groups of the form $(\mathbf{R}^d, \mathbf{R}^{d'})$, $(\mathbf{T}^d, \mathbf{T}^{d'})$ and $(\mathbf{Z}^d, \mathbf{Z}^{d'})$. The construction is identical to that of the tensor product of two distributions, discussed in [Tre, Def. 40.3], and in this form (i.e. through the use of Theorem C.5.1.30(4)) it is used only in the proof of Lemma D.1.3.7 and Lemma D.2.2.2(1) of Appendix D (we refer the reader to the proof of [Tre, Thm. 51.6(51.3)] for a similar argument and a similar use of the binary tensor product of tempered distributions, which is used to make sense of the equicontinuous subsets $A' \otimes B'$ in $\mathcal{S}(\mathbf{R}^{m+n})'$ in the proof of loc.cit.).

**C.5.2. Holomorphic vector-valued functions.** We start by defining basic concepts of continuity and holomorphy for vector-valued functions on open subsets of $\mathbf{C}$.

C.5.2.1. *Grothendieck’s criterion for holomorphy.* For a Hausdorff locally convex topological $\mathbf{C}$-vector space $E$, we will be identifying $E$ as a linear subspace of $(E')^*$ (although not topologically) under the linear map $\iota_E : E \to (E')^*$ from (C.4.1.1) and studied in Lemma C.4.1.1, when saying that certain linear forms on $E'$ are “elements of $E$”, or are “contained in $E$”. These will ordinarily be integrals in the sense of Pettis, which, recall, are defined for general $E$ as elements of $(E')^*$. The concept of integrability was defined in Definition C.4.2.1(3) via such integrals being contained in $E$.

Recall that we call $\Omega \subset \mathbf{C}$ a domain, or a complex domain, if $\Omega \subset \mathbf{C}$ is non-empty open and connected.

**Definition C.5.2.1.** Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, and $\Omega \subset \mathbf{C}$ a domain. We say a function $f : \Omega \to E$ is:

(1) weakly continuous if and only if for every continuous linear functional $\varphi \in E'$, the function $\langle f(\xi), \varphi \rangle_{E,E'}$ is continuous as a function of $\xi \in \Omega$ (equivalently, $f$ is continuous when $E$ is given the $\sigma(E, E')$-topology).

(2) weakly continuously differentiable $k$ times, for an integer $k \ge 1$, if and only if for every continuous linear functional $\varphi \in E'$, the function $\langle f, \varphi \rangle_{E,E'}$ on $\Omega$ is an element of $C^k(\Omega)$.

(3) Weakly holomorphic if and only if for every continuous linear functional $\varphi \in E'$, the function $\langle f, \varphi \rangle_{E,E'}$ on $\Omega$ is holomorphic in the sense of complex analysis.

(4) Complex-differentiable, or holomorphic, if and only if for every $\xi_0 \in \Omega$

$$
\lim_{\xi \to \xi_0} (\xi - \xi_0)^{-1}(f(\xi) - f(\xi_0)) \tag{C.5.2.1}
$$

exists in $E$ as $\xi \to \xi_0$ in the complex sense (in particular, $f : \Omega \to E$ is continuous).

**Remark C.5.2.2.** Reprising the terminology from Definition C.5.1.8, holomorphy of the $E$-valued function $f$ on $\Omega \subset \mathbf{C}$ is equivalent to differentiability, upon choosing $k = \mathbf{C}$, $d = 1$.

In [Gro-a, Thm.1], Grothendieck established the equivalence of the concept of weak holomorphy in Definition C.5.2.1(3) with seemingly stronger notions of holomorphy, showing that analogs of the Cauchy integral formula and familiar results from complex analysis, adapt to the case of $E$-valued functions with minor changes, as long as vector-valued integrals are contained in $E$.

## PDF page 738

**738** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

**Remark C.5.2.3.** In [Gro-a, Thm.1(4)], complex-differentiable functions are termed “strongly differentiable”.

We record Grothendieck’s Theorem (see [Gro-a, Thm.1]) below. Throughout this work an arc $\Gamma \subset \Omega$, for $\Omega$ a complex domain, will always refer to a continuous and piecewise-$C^1$ map $\gamma : [a, b] \to \Omega$, for $a, b \in \mathbf{R}$, $a < b$, such that $\Gamma = \gamma([a, b])$.

The following is immediate from complex analysis:

**Theorem C.5.2.4.** *Let $E$ be a Hausdorff locally convex topological $\mathbf{C}$-vector space, $\Omega \subset \mathbf{C}$ a domain. Let $f : \Omega \to E$ be a function. The following conditions are equivalent:*

(1) The function $f$ is weakly holomorphic.

(2) *The function $f$ is weakly continuous in the sense of Definition C.5.2.1(1), and for any closed positively oriented simple curve $\Gamma \subset \Omega$ whose interior is contained within $\Omega$ we have*

$$
\int_\Gamma f(\xi)\, \mathrm{d}\xi = 0 \tag{C.5.2.2}
$$

as elements of $(E')^*$.

(3) *$f$ is weakly continuous, and for any closed positively oriented simple curve $\Gamma \subset \Omega$ whose interior is contained within $\Omega$, and for any $\xi_0 \in \Omega$ enclosed in the interior of the contour $\Gamma$, we have*

$$
f(\xi_0) = \frac{1}{2\pi i} \int_\Gamma \frac{f(\xi)}{\xi - \xi_0}\, \mathrm{d}\xi \tag{C.5.2.3}
$$

as elements of $(E')^*$.

**Remark C.5.2.5.** The integrals (C.5.2.2) and (C.5.2.3) are meant in the Pettis sense, computable using a piecewise-$C^1$ parameterization of $\Gamma$ as in complex analysis.

If we assume that $E$ is quasi-complete, then the Theorem can be strengthen into the following:

**Theorem C.5.2.6 (Grothendieck’s holomorphy criterion).** *Let $E$ be a Hausdorff quasi-complete locally convex topological $\mathbf{C}$-vector space, $\Omega \subset \mathbf{C}$ a complex domain of the complex $\xi$-plane. Let $f : \Omega \to E$ be a function. The following conditions are equivalent:*

(1) $f$ is weakly holomorphic.

(2) *$f$ is weakly differentiable $k$ times for every integer $k \ge 1$.*

(3) *$f$ is complex-differentiable $k$ times for every integer $k \ge 1$, in which case for any closed positively oriented simple curve $\Gamma \subset \Omega$ whose interior is contained within $\Omega$, and for any $\xi_0 \in \Omega$ enclosed in the interior of the contour $\Gamma$, we have*

$$
f^{(k)}(\xi_0) = \frac{k!}{2\pi i} \int_\Gamma \frac{f(\xi)}{(\xi - \xi_0)^{k+1}}\, \mathrm{d}\xi \tag{C.5.2.4}
$$

*as elements of $(E')^*$ (the left side belongs to $E$).*

(4) *Around every point $\xi_0 \in \Omega$, we have the following Taylor expansion*

$$
f(\xi) = \sum_{k \ge 0} a_k (\xi - \xi_0)^k \tag{C.5.2.5}
$$

*where $a_k = (1/k!) f^{(k)}(\xi_0) \in E$ for every $k \ge 0$, where the series is uniformly convergent on every closed disc $D$ around $\xi_0$ such that $D \subset \Omega$.*

*In particular, if $f$ is weakly holomorphic then it is holomorphic.*

**Remark C.5.2.7.** On Theorem C.5.2.6, we make the following observations:

## PDF page 739

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **739**

(1) is the first part of [Gro-a, Thm.1]. Note that a priori, the derivative $f^{(k)}$ in (1) and (2) is defined as an element of $(E')^*$ by the rule

$$
\langle f^{(k)}(\xi), \varphi \rangle_{E,E'} = \frac{\mathrm{d}^k}{\mathrm{d}\xi^k} \langle f(\xi), \varphi \rangle_{E,E'} \tag{C.5.2.6}
$$

where the right side is defined and continuous in $\xi$ for all $k \ge 1$, since $f$ is weakly holomorphic. The use of quasi-completeness in the proof of Theorem C.5.2.6 from [Gro-a, Thm.1] is in that it enables the reduction of the equivalence between parts (1) and (2), on one hand, and (3) on the other, to proving continuity of $f$ (rather than merely weak continuity). Indeed, upon showing that $f$ is continuous, Theorem C.4.3.5 applies since $\Gamma$ is compact and $\mathrm{d}\xi$ is Radon, so the first two (equivalent) parts and the Cauchy Integral Formula imply that the $(E')^*$-valued integrals in (C.5.2.4) are contained in $E$ by quasi-completeness, so the equality with $f^{(k)}(\xi_0)$ as a weak derivative yields complex-differentiability of $f$. Continuity of $f$, however, has to be shown directly and without the aid of quasi-completeness, but rather by means of Lemma C.4.3.1. The argument for continuity is at the bottom of [Gro-a, p. 38].

(2) The argument at the bottom of [Gro-a, p. 38] shows that weak holomorphy implies continuity in the presence of quasi-completeness.

The problem of deciding the equivalence of weak holomorphy and the remaining conditions in Theorem C.5.2.4 goes back to Dunford, and we refer the reader to [Dunford, Thm. 76] for the special case $E$ is a Banach space.

**C.5.3. Meromorphic vector-valued functions.** Similarly as for holomorphic functions on domains of the complex plane valued in a quasi-complete Hausdorff locally convex topological $\mathbf{C}$-vector space, we now introduce the concept of meromorphic function.

**Definition C.5.3.1.** Let $\Omega \subset \mathbf{C}$ be a domain, $E$ a quasi-complete Hausdorff locally convex topological vector space, $D \subset \Omega$ a discrete subset, $f : \Omega - D \to E$ a function. We say the pair $(f, D)$ is a meromorphic function on $\Omega$ if $f$ is holomorphic on $\Omega - D$, and for every $\xi_0 \in D$ there exists an integer $k \ge 0$ and a sequence

$$
\{a_{k'}(f, \xi_0)\}_{k' \ge k} \subset E \tag{C.5.3.1}
$$

of elements of $E$ such that the series

$$
\sum_{k' \ge k} a_{k'}(f, \xi_0) (\xi - \xi_0)^{k'} \tag{C.5.3.2}
$$

converges uniformly over the compact subsets of a punctured neighborhood of $\xi_0 \in \Omega$, and its sum is $f(\xi)$ for $\xi$ in any such punctured neighborhood of $\xi_0 \in \Omega$ (equivalently, some $(\xi - \xi_0)^{N_{\xi_0}} f(\xi)$ extends holomorphically across $\xi_0$ for all $\xi_0 \in D$).

We define:

(1) the order of $(f, D)$ at $\xi_0 \in \Omega$, denoted $\operatorname{ord}_{\xi_0}(f)$, to be the minimal integer $N$ such that the conditions on the series (C.5.3.1) are met for the choice $k = N$.

(2) $\xi_0 \in \Omega$ to be a pole of $f$ if $\operatorname{ord}_{\xi_0}(f) \le -1$, in which case we say $\xi_0$ is a pole of order $-\operatorname{ord}_{\xi_0}(f)$.

We define $\mathscr{M}(\Omega, E)$ the complex vector space of meromorphic $E$-valued functions on $\Omega$.

We check the following, as an application of Theorem C.5.2.4

**Lemma C.5.3.2.** *Let $E$ be a Hausdorff quasi-complete locally convex topological vector space, $\Omega \subset \mathbf{C}$ a domain. Let $f : \Omega \to E$ be a meromorphic function. For every $\xi_0 \in \Omega$, and every closed positively oriented simple curve $\Gamma \subset \Omega$ enclosing $\xi_0$ in its interior and with no other possible poles enclosed in its interior and on*

## PDF page 740

**740** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

$\Gamma$, we have

$$
a_k(\xi_0, f) = \frac{1}{2\pi i} \int_\Gamma \frac{f(\xi)}{(\xi - \xi_0)^{k+1}}\, \mathrm{d}\xi \tag{C.5.3.3}
$$

*for every $k \in \mathbf{Z}$, the identity being as elements of $E$.*

*Proof.* The case $k \ge 0$ in (C.5.2.4), so we focus on $k < 0$. By definition of $f$ being meromorphic at $\xi_0 \in \Omega$ we have by (C.5.3.2)

$$
\sum_{k' \ge -N} a_{k'}(\xi_0, f) (\xi - \xi_0)^{k'} \tag{C.5.3.4}
$$

where the series converges uniformly on every closed disc around $\xi_0$ entirely contained in $\Omega$, and $(\xi - \xi_0)^N f(\xi)$ has a removable singularity at $\xi = \xi_0$ and extends to a holomorphic function on a neighborhood of $\xi_0 \in \Omega$. By writing

$$\frac{f(\xi)}{(\xi - \xi_0)^{k+1}} = \frac{(\xi - \xi_0)^N f(\xi)}{(\xi - \xi_0)^{(N+k)+1}},$$

we’re reduced to the settled holomorphic case. $\square$

C.5.3.1. *Vector-valued residues.* We construct the following operators on $\mathscr{M}(\Omega, E)$:

$$
\operatorname{Res}_\xi(f) := a_{-1}(\xi, f), \quad \xi \in \Omega. \tag{C.5.3.5}
$$

**Lemma C.5.3.3.** *Let $E$ be a Hausdorff quasi-complete locally convex topological $\mathbf{C}$-vector space, $\Omega \subset \mathbf{C}$ a domain, $f$ a meromorphic $E$-valued function on $\Omega$. Then:*

(1) For every $\xi \in \Omega$, the map

$$
\operatorname{Res}_\xi : \mathscr{M}(\Omega, E) \to E \tag{C.5.3.6}
$$

*assigned by the rule $f \mapsto \operatorname{Res}_\xi(f)$ as in (C.5.3.5) is $\mathbf{C}$-linear.*

(2) *For every $\xi_0 \in \Omega$, we have the identity*

$$
\operatorname{Res}_{\xi_0}(f) = \frac{1}{2\pi i} \int_\Gamma f(\xi)\, \mathrm{d}\xi \tag{C.5.3.7}
$$

*as $\mathbf{C}$-linear maps $\mathscr{M}(\Omega, E) \to E$ for every closed positively oriented simple curve contained within $\Omega$ and enclosing no further pole other than possibly $\xi_0$, neither in its interior nor on $\Gamma$ itself.*

(3) *If $\xi_0$ is a pole of $f$ of order $k \ge 1$ then*

$$
\operatorname{Res}_{\xi_0}(f) = \lim_{\xi \to \xi_0} \frac{1}{(k-1)!} \frac{\mathrm{d}^{k-1}}{\mathrm{d}\xi^{k-1}} ((\xi - \xi_0)^{k-1} f(\xi)) \tag{C.5.3.8}
$$

as $\mathbf{C}$-linear operators $\mathscr{M}(\Omega, E) \to E$.

(4) *Let $E_1, E_2$ be two Hausdorff quasi-complete complex topological vector spaces, and $T : E_1 \to E_2$ a continuous $\mathbf{C}$-linear operator. Then*

$$
\operatorname{Res}_\xi(T \circ (\cdot)) = T \circ \operatorname{Res}_\xi \tag{C.5.3.9}
$$

as $\mathbf{C}$-linear operators $\mathscr{M}(\Omega, E_2) \to E_2$, for every $\xi \in \Omega$.

*Proof.* Assertions (1) and (3) are clear. For (4), use Lemma C.4.3.8 applied to $X = \Gamma$, $\mu = \mathrm{d}\xi$. $\square$

**C.5.4. Vector-valued Residue Theorem.** We recall that by a cycle $\Gamma$ on $\Omega$, we mean a formal sum with integer coefficients of positively oriented closed simple curves contained within $\Omega$. The following is therefore the analog of Cauchy’s Residue Theorem, for $E$-valued holomorphic functions on $\Omega$.

## PDF page 741

**C.5. MEROMORPHIC FUNCTIONS VALUED IN A QUASI-COMPLETE LOCALLY CONVEX TVS** · **741**

**Theorem C.5.4.1 (Residue Theorem for vector-valued meromorphic functions).** *Let $E$ be a Hausdorff quasi-complete locally convex complex topological vector space, $\Omega \subset \mathbf{C}$ a domain. Let $f$ be a meromorphic $E$-valued function on $\Omega$. Let $\Gamma \subset \Omega$ be a cycle which is homologous to zero and does not contain any poles of $f$. Then*

$$
\frac{1}{2\pi i} \int_\Gamma f(\xi)\, \mathrm{d}\xi = \sum_{\xi_0 \in D} n(\Gamma, \xi_0) \operatorname{Res}_{\xi_0}(f) \tag{C.5.4.1}
$$

*as $\mathbf{C}$-linear operators $\mathscr{M}(\Omega, E) \to E$, where $n(\Gamma, \xi_0)$ is the winding number of $\Gamma$ around $\xi_0 \in D$.*

*Proof.* By pairing both sides of (C.5.4.1) against a general $\varphi \in E'$, we reduce to the classical case with $E = \mathbf{C}$. $\square$

We see from Theorem C.5.4.1 how it is natural to constrain $E$ so as to ensure that $f$ be integrable in the $E$-valued sense over any closed simple curve $\Gamma$. Quasi-completeness of $E$ is assumed for this reason, in light of Theorem C.4.3.5.

The following is an analog of Riemann’s Theorem on removable singularities. We refer the reader to [Kruse, Thm. 7.4].

**Lemma C.5.4.2 (On removable singularities).** *Let $E$ be a Hausdorff quasi-complete locally convex topological $\mathbf{C}$-vector space, $\Omega \subset \mathbf{C}$ a domain, $Z \subset \Omega$ a discrete subset and $f : \Omega - Z \to E$ a holomorphic function. If for every $\xi_0 \in \Omega$ there exists a disc $B \subset \Omega$ containing $\xi_0$, such that $f$ is bounded on $B - Z$, then $f$ uniquely extends to a holomorphic function $f : \Omega \to E$.*

Here too quasi-completeness is being used to know holomorphic is equivalent to weakly holomorphic. Finer analytic continuation results are available (see [Jor-b, Thms. 6, 8]) again under a local completeness assumption.

We will, throughout this work, always be able to assume quasi-completeness of the Hausdorff locally convex topological $\mathbf{C}$-vector space of values of the holomorphic and meromorphic functions of interest since these spaces will always be the strong dual of a quotient of the Schwartz-Bruhat space of the global, respectively $S$-local, adeles of a number field $F$, for $F$ a finite set of places containing all the Archimedean places. Such duals are quasi-complete, and even complete.

C.5.4.1. *Vector-valued Identity Theorem.* We record here below the following analog of the Identity Theorem from classical complex analysis:

**Lemma C.5.4.3.** *Let $E$ be a Hausdorff quasi-complete locally convex topological $\mathbf{C}$-vector space, $\Omega \subset \mathbf{C}$ a domain, $(f_1, D_1)$ and $(f_2, D_2)$ two meromorphic $E$-valued functions on $\Omega$. Let $B \subset \Omega - (D_1 \cup D_2)$ be a non-empty open disc such that*

$$
f_1|_B = f_2|_B. \tag{C.5.4.2}
$$

*Then $f_1$ and $f_2$ agree as holomorphic functions on $\Omega - (D_1 \cup D_2)$.*

*Proof.* For $\varphi \in E'$, the classical Identity Theorem applies to $\langle f_1, \varphi \rangle$ and $\langle f_2, \varphi \rangle$, so $\langle f_1, \varphi \rangle = \langle f_2, \varphi \rangle$ for all $\varphi$. Thus, $f_1 = f_2$. $\square$

For a Hausdorff quasi-complete locally convex topological $\mathbf{C}$-vector space $E$, the complex vector spaces

$$\mathscr{H}(\Omega, E), \, \mathscr{M}(\Omega, E)$$

can be topologized (the former with the topology of locally uniform convergence, the latter with a certain locally convex inductive limit topology) and are well-behaved. Their respective Hausdorff locally convex

## PDF page 742

**742** · **CHAPTER C. PREPARATIONS ON LOCALLY CONVEX TOPOLOGICAL VECTOR SPACES**

topologies are themselves quasi-complete, and promote the residue operators to continuous linear maps. They have been studied, for example, in [Jor-a, BJM], in analogy with [GE] on the case of $\mathscr{M}(\Omega, E)$ for $E = \mathbf{C}$.

We will not require a study of the complex vector spaces $\mathscr{H}(\Omega, E)$ and $\mathscr{M}(\Omega, E)$ for quasi-complete $E$: rather, we will be studying, throughout Appendix D and the main text, smaller linear subspaces of holomorphic and meromorphic vector-valued functions satisfying decay conditions uniformly over vertical strips of bounded width, topologized with stronger topologies of uniform convergence over vertical strips of bounded width.
