## PDF page 823

APPENDIX E

**Topological stacks**$^1$

E.1. Compactly generated spaces — 825

E.1.1. Preparations on compactly generated spaces — 828

E.1.2. Categorical and topological stabilities of compactly generated spaces — 833

E.2. Compactly generated weakly Hausdorff spaces — 846

E.2.1. Preparations on compactly generated weakly Hausdorff spaces — 846

E.2.2. Categorical and topological stabilities of compactly generated weakly Hausdorff spaces — 851

E.2.3. Permanence properties of compactly generated weakly Hausdorff spaces — 855

E.2.4. Counter-examples on compact generation and separation conditions — 865

E.3. Small compactly generated weakly Hausdorff spaces — 868

E.3.1. Preparations on small index categories and small compact Hausdorff spaces — 868

E.3.2. $\alpha$-small compactly generated and weakly Hausdorff spaces — 872

E.3.3. Size-bound criteria — 874

E.3.4. Closure properties of $\mathbf{CGWH}_\alpha$ — 877

E.3.5. The site of small compactly generated weakly Hausdorff spaces — 879

E.4. Topological groupoids — 883

E.4.1. Groupoids in sets and internal groupoids — 883

E.4.2. Groupoids internal to $\mathbf{CGWH}$ — 886

E.5. 2-categorical preparations — 889

E.5.1. The category of all small categories — 889

E.5.2. 2-categories — 898

E.5.3. Pseudo-functors — 903

E.5.4. Comparing $\mathbf{Cat}^*$ and $\mathbf{Cat}$ — 907

E.5.5. 2-category of 2-commutative diagrams — 910

E.5.6. 2-final objects in $\mathbf{Diagrams}(f, g)$ — 913

E.5.7. 2-fibre products and 1-fibre products — 914

E.6. Stacks on $\mathbf{CGWH}_{\alpha,\tau}$ — 920

E.6.1. Basic concepts — 920

E.6.2. Quotient stacks associated to $\alpha$-small topological groupoids — 922

E.6.3. Inertia stack and coarse space — 924

E.6.4. Equivalences — 928

$^1$Complete this Appendix, correcting it and shortening it.

823

## PDF page 824

**824** · **CHAPTER E. TOPOLOGICAL STACKS**

In this appendix we review the theory of compactly generated weakly Hausdorff spaces. Our intent is to present a comprehensive treatment in a uniform and detailed manner, also carefully handling set-theoretic aspects and including comprehensive references to the literature to build the geometric foundations required to make sense of “periodic quotient stacks” associated to primes. This provides insight into the main trace calculation upon which Refined Explicit Formulas rest. It also makes the connection of our work to Deninger’s work, though strictly speaking this is not logically needed for our main trace work (but it guided how we discovered our trace formula results).

We settle on some notation and terminology.

Notation E.0.0.1. We write:

(1) $\mathbf{Sets}$ for the large category whose objects are sets, and morphisms are functions between sets.

(2) $\mathbf{Spaces}$ for the large category whose objects are topological spaces, and morphisms are continuous functions between topological spaces.

(3) For a topological space $X$, $X^{\mathrm{set}}$ for the set underlying $X$.

(4) For topological spaces $X$, $Y$, $\mathrm{C}(X, Y)$ for the set of all continuous functions $f : X \to Y$.

Terminology E.0.0.1. We call:

(1) A *space* any object of $\mathbf{Spaces}$, i.e. any topological space. We will use this abbreviation whenever an adjective is to precede “topological space”. For instance, “compactly generated topological space” will be abbreviated to “compactly generated space”.

(2) A *map*, or *continuous map*, $f : X \to Y$ between spaces $X$ and $Y$ any continuous function $f : X \to Y$. We include the word continuous when there is potential for ambiguity.

(3) A *set-function* $f : X \to Y$ between sets $X$ and $Y$ is any function $f : X \to Y$. We denote by $\mathrm{Map}(X, Y)$ the set of all set-functions $X \to Y$.

(4) A *set-function* $f : X \to Y$ between spaces $X$ and $Y$ is any set-function $f : X^{\mathrm{set}} \to Y^{\mathrm{set}}$, not necessarily underlying a continuous function. For a continuous map $f : X \to Y$, we write $f^{\mathrm{set}}$ for its underlying set-function. We write $(\cdot)^{\mathrm{set}}$ for the resulting forgetful functor $\mathbf{Spaces} \to \mathbf{Sets}$.

(5) A *compact* space is a topological space such that every open cover of $K$ has a finite refinement.

(6) A *locally compact* space is a topological space such that every point has a fundamental system of compact neighborhoods.

Our main references for general topology throughout this appendix are [Du], [Bou-GT], [Ke], and [SP]. In particular, we refer to [Bou-GT, Ch. I ,§1, §5], [Du, Ch. III], and [SP, Tags 004O, 0405] for background material on point-set topology, to [Bou-GT, Ch. I, §8], [Du, Ch. VII, §1-3], and [SP, Tag 08ZD] for background material on separation axioms, [Bou-GT, Ch. I, §9], [Du, Ch. X, §1,6,9], [Ke, Ch. 5], and [SP, Tags 0059, 08ZQ] for background material around compactness, and [Du, Ch. XII, §1-3], and [Ke, Ch. 7] for background material on function spaces. We will further refer to [SP, Tag 005M] on proper maps, and [SP, Tags 08ZW, 0908] on profinite spaces and Stone-Čech compactifications.

We caution the reader about diverging terminologies within the above sources. Specifically, our use of the word *compact* follows [Du, Ke] but not [Bou-GT, SP], where the same adjective is replaced by *quasi-compact*. We further caution the reader that several sources within the literature that will be occasionally referred to throughout this work use the word *compact* to mean *compact and Hausdorff* (see, for example, [LGL, Rezk, Ste]). Throughout this work, we shall always clarify when a separation assumption is being made.

We further settle on the following:

Terminology E.0.0.2. We let $X, Y$ be topological spaces, and $f : X \to Y$ a continuous map.

(1) The *quotient topology* on $f(X)$ is the finest topology on $f(X)$ making the induced map $f : X \to f(X)$ continuous (i.e., $U \subset f(X)$ is open if and only if $f^{-1}(U)$ is open in $X$). This may not be the subspace

## PDF page 825

**E.1. COMPACTLY GENERATED SPACES** · **825**

topology on $f(X)$. We call a map $f$ for which it agrees with the subspace topology a *strict* map (see part (1) of [SP, Tag 0406]).

(2) The *image* of $X$ under $f$, denoted $f(X)$ or $\mathrm{Im}(f)$, is the subset $f(X)$ of $Y$ endowed with the *quotient topology* induced from the topology on $X$.

(3) The *pre-image* of a subspace $Z \subset Y$ along the continuous map $f : X \to Y$ is the subset $f^{-1}(Z) \subset X$ endowed with the subspace topology induced from the topology on $X$.

(4) We say $f$ is an *immersion* if and only if it is injective and strict.

(5) We say $f$ is *submersive* if and only if it is surjective and strict (see part (2) of [SP, Tag 0406]).

(6) We say $f$ is *étale* if and only if it is a local homeomorphism.

We further clarify that when considering more than one topology on the same underlying set of a fixed topological space $X$, we shall use the terminology *intrinsic topology* on $X$ to refer to the topology that $X$ is equipped with from the outset of the discussion.

We caution the reader on differing nomenclature choices for (4) and (5) between this work and some of the sources we shall be referring to throughout. The class of morphisms we call immersions is referred to as “inclusions” in [Rezk, Str]. Other terms used to refer to submersive maps within the literature that we shall refer to throughout are *identification maps* (see, for example, [Br4, Ch. 4]), *quotient maps* (see [Str, Def. 2.18]) or *proclusive maps/proclusions* (see, for example, [Rezk, §9.1] and [Ste, Def. 2.5]). We shall make use of the preceding “Terminology” section occasionally also to make local clarifications later throughout this appendix as the need arises, so as to remove all terminological ambiguities.

**E.1. Compactly generated spaces**

This section is devoted to collecting background material on compactly generated spaces. Its purpose is to pave the way for a discussion in §E.2 of the theory of compactly generated weakly Hausdorff spaces, whose category serves as an ambient category within which we shall construct a small site of topological spaces. When arguments are not given here, they are referenced into other sources.

The class of compactly generated weakly Hausdorff topological spaces, abbreviated “CGWH”, was introduced with the intent of constructing a large category of topological spaces that, while containing most examples of spaces of interest, such as locally compact Hausdorff topological spaces and CW complexes, also has good categorical properties, with particular emphasis on a cartesian closed monoidal category structure. Compactly generated weakly Hausdorff spaces have so far had a prominent role to play within the literature around homotopy theory; see for example [BG, Ch.8] for an account and complements on [Ste], with basic applications to homotopy theory in [BG, Ch. 9]. We refer the reader to [LMS] for an example of the foundational use of compactly generated spaces in stable homotopy theory, starting with [LMS, Ch. I, §1] on the equivariant stable category, and to J.P. May’s work [May] on iterated loop spaces. We further refer the reader to L.G. Lewis’ Ph.D. thesis [LGL] and its appendix [LGL, Appendix A] containing a comprehensive account of compactly generated weakly Hausdorff spaces, which will also serve as one of our main sources for this section and the next.

The terminology often used to refer to such a category of topological spaces is “convenient”, and the idea was axiomatized and studied systematically in the early 1960’s. We refer the reader to R. Brown’s D.Phil. thesis [Br1], with particular emphasis on [Br1, Ch. I, Thm. 2.36, Thm. 2.37] and the preceding discussion in [Br1, Ch. I, §2] on $k$-spaces where, preceding the introduction of the concept of closed monoidal categories by a few years, the author discusses exponential spaces in a manner that is a precursor to Steenrod’s article [Ste] where a candidate convenient category of topological spaces was introduced and studied, and its monoidal structure and cartesian closure discussed. To the best of the author’s knowledge, Brown’s papers [Br2] and [Br3], both following Brown’s thesis and pre-dating Steenrod’s 1967 article, are the foothold of the search for

## PDF page 826

**826** · **CHAPTER E. TOPOLOGICAL STACKS**

convenient categories of spaces and for the identification of their desired properties, whose development then gained traction after [Ste] and [Vogt].

The concept of “$k$-space”, where the letter $k$ is understood to refer to the german word “kompakt”, predates Brown’s thesis and the very idea of a convenient category. It appears to go back to Princeton lectures by Hurewicz from the late 1940’s, and was first introduced in the literature in [Ga, Definition, p. 303]. It can be found in Kelley’s book on general topology (see [Ke, Ch. 7, p. 130]) from 1955. It was after [Br1] and particularly in [Br2] that the importance of $k$-spaces, in their definition from [Ke, Ch. 7, p. 130] was observed. We refer the reader to [Br2], where the author advertised the category of $k$-spaces as a possible candidate for a convenient category, before an axiomatization of “convenience” was made in the literature (see [Br2], and [Vogt] for discussions of convenient categories and their properties). The reader is further referred to [nLab1, §6] for further historical information on the inception and development of these themes.

The defining properties of a convenient category $\mathcal{C}$ of topological spaces are usually assumed to be:

(1) $\mathcal{C}$ is a subcategory of $\mathbf{Spaces}$ that is full and replete (i.e., any object of $\mathbf{Spaces}$ isomorphic to an object of $\mathcal{C}$ is an object of $\mathcal{C}$),

(2) $\mathcal{C}$ contains all CW complexes and most examples of spaces of practical interest (see the beginning of [Ste, §1]),

(3) $\mathcal{C}$ is closed under small limits and colimits (see [Vogt, §2, Thm. 2.1]),

(4) for every object $X$ in $\mathcal{C}$, closed subspaces of $X$ are objects in $\mathcal{C}$ (see [Vogt, §2, Axiom 1]); it is sometimes required that open subspaces also satisfy this property (see [Vogt, §2, Axiom 1$^*$]).

(5) $\mathcal{C}$ is cartesian closed (see [Vogt, §2, Axiom 2] for axioms in this direction, and [Br3, §1] on the exponential law; see also [Ste, §1, (1),(2)]) with respect to its cartesian monoidal structure (see [MacL, Ch. VII, §7-8]).

The reader is especially referred to [ELS], particularly to [ELS, §3, §5], and to [ELS, Thm. 5.15], where a comprehensive treatment of convenient categories, their stability with respect to internal exponentiation, and their general construction, alongside a uniform proof of cartesian closedness, is given. We further refer the reader to [nLab1, Def. 2.1] and the discussion in [nLab1, §2] for an overview around the concept of “convenient category” of topological spaces.

We will use [ELS] to highlight the relation between some of the differing definitions of convenient categories based on compactly generated spaces.

The notion of compactly generated spaces we adopt here is the one introduced in [McC, §2, p. 275] under the term “$k$-spaces”, and in [LGL, Appendix A, §1, p. 148], which is also the notion in [Str, Def. 1.1] and [Rezk, §3.1] (in the latter, also under the term “$k$-spaces”), the only differences being with respect to terminology. The notion of $k$-space in [Ke, Ch. 7, p. 230] is defined using the immersions of compact subspaces as test continuous maps for closure of subsets and does not incorporate a Hausdorff condition on the test compact subspaces. It is therefore different from ours (see §E.2.4 and especially Lemma E.2.4.11 for an example illustrating the difference).

We further refer the reader to [LM, §1], where compact generation is also defined in terms of intersections with compact, possibly non-Hausdorff, subspaces (see the end of [LM, p. 1]), as in [Ke]. A definition is given in [Vogt, §5,(iii)] after an axiomatic development leading to a general method to construct large categories of topological spaces stable under certain categorical operations, and it is equivalent to the one adopted throughout this work. Another is introduced in [Vogt, §5, (iv)] which is related to the one in [Ke, Ch. 7, p. 230] via Lemma E.2.4.2. In Steenrod’s paper (see [Ste, p.2]), a Hausdorff condition is built into the very definition of compact generation, to arrange for all compact subspaces of compactly generated spaces to be closed. In a similar vein, we shall eventually incorporate a weak Hausdorff condition, as in [McC, §2], [LGL, p. 148], and throughout loc.cit., which is sufficient to ensure that all compact subspaces of compactly

## PDF page 827

**E.1. COMPACTLY GENERATED SPACES** · **827**

generated (weakly Hausdorff) spaces are closed. Weakening the Hausdorff condition in [Ste, §2] rendered itself necessary to arrange for better stability properties of the resulting convenient category, especially in regard to computation in $\mathbf{Spaces}$ of certain classes of colimits.

Other features of the category of (weakly Hausdorff) compactly generated spaces are the availability of a simple classification of important classes of maps (such as regular monomorphisms, which are shown to be the closed immersions, and regular epimorphisms, which are shown to be the submersive maps; see Definition E.2.3.14 for these notions of regularity), together with stability of submersive maps under arbitrary base change. Such stability leads to a transparent description of the canonical topology on small full subcategories of the category of compactly generated weakly Hausdorff spaces closed under pullbacks, contributing to rendering them a suitable choice (for our intended purposes) to underlie small sites.

The weak Hausdorff condition can be found in [McC, §2,p.275], where it is attributed to J.C. Moore. This appears to be the first source within the literature recording the concept. We refer the reader to the beginning of [McC, §2] for further motivation for the weakening of the Hausdorff condition from [Ste].

We may summarize the differences between the various concepts of compact generation for topological spaces as being mostly in regard to whether or not the test spaces for openness, equivalently closedness, of subsets is assumed to satisfy a non-trivial separation condition or just be compactness.

The main divergences between the theories are discernible from a number of features, such as the fact that the notion of compact generation adopted throughout this appendix is stable under passage to arbitrary open subspaces, which does not hold in other theories and especially without a separation condition on the compact test spaces (see §E.2.4 and especially Lemma E.2.4.12 for an example of this discrepancy). Stability of compact generation under passage to open subspaces of a space $X$ may not hold when the compact test spaces are assumed to be compact subspaces of $X$, even under a Hausdorff assumption, as is done in [Ste]. It does hold for *regular* open subspaces (see [Ste, 2.4]).

The approach we adopt throughout this work is the approach of [LGL, Appendix A], [McC, §2], [Str, §1, §2], and [Rezk, §3.1] (we recall for the sake of clarity that in this latter reference, “compact spaces” is equivalent to “compact Hausdorff spaces” here, insofar as “quasi-compactness” is used in loc.cit. to refer to compact spaces in this work). The notion of compactly generated space in [McC, §2] and [Rezk, §5] is equivalent to our notion of compactly generated weakly Hausdorff space. Weakly Hausdorff spaces throughout this appendix, and “$k$-Hausdorff” spaces in [Rezk, §4] are different concepts, but they are equivalent conditions on compactly generated spaces (see [Rezk, Prop.11.4]) and so most results in loc.cit. can be referred to throughout this appendix with only minor terminological caveats for the reader, which will be stated as the need arises.

The advantages of using the category of compactly generated weakly Hausdorff spaces are several. As an instance, the fact that the categories of compactly generated spaces and of compactly generated weakly Hausdorff spaces are cartesian-closed monoidal categories implies that product functors have right-adjoints, and as such commute with all small colimits (see [LGL, Cor. 5.6]). This implies, in particular, compatibility of submersive maps with finite products (see [LGL, Prop. 5.8]), which does not hold in the category of all topological spaces (see Example E.1.2.18). We establish this here with and without separation assumptions, as a consequence of cartesian closure (Lemma E.2.2.10, respectively Lemma E.1.2.13), combined with the characterization of submersive maps as the effective epimorphisms in each category (Lemma E.2.3.8, respectively Lemma E.1.2.14); see Definition E.2.3.14 for this notion of effectivity. Within such categories, CW complexes are examples of objects, and products of CW complexes are again CW complexes.

The properties we are most interested in arranging for a convenient category of topological spaces are:

(1) stability of all objects under passage to closed subspaces,

(2) stability of all objects under passage to open subspaces,

(3) existence of finite limits and finite colimits,

(4) stability of submersive maps under arbitrary pull-backs,

## PDF page 828

**828** · **CHAPTER E. TOPOLOGICAL STACKS**

(5) computability in $\mathbf{Spaces}$ of certain push-outs.

Arranging all of the above properties requires a delicate balancing act, which leads to the combination of compact generation with the weak Hausdorff separation condition in a natural manner. We will show by example how compact generation is sufficient to arrange for (1), (2), (3) and (5) to hold (see Lemma E.1.2.25 for (1) and (2), Lemma E.1.2.2 for (3) and (5)), but not for (4) (see Example E.1.2.16).

Imposing a Hausdorff condition on all objects, in combination with compact generation, as is done in [Ste], is sufficient to arrange for (1), (3), and (4) to hold (see [Ste, §2,2.4] for (1), see Lemma E.2.2.5 combined with the fact that finite limits and finite colimits of Hausdorff spaces are Hausdorff for (3), and see Lemma E.2.3.6 combined with (3) for (4)), but not for (2) (although see [Ste, §2,2.4]) and most importantly not for (5) (see Example E.2.3.12).

Combining compact generation with the weak Hausdorff separation condition arranges for all five properties to hold, and upon arriving at the category of compactly generated weakly Hausdorff spaces, in §E.3 we shall be selecting small full subcategories with enough closure properties to serve as small sites.

Our main sources throughout this section concerning compactly generated spaces are [LGL, §4, §5], [McC, §2], [Str, §2], [Rezk, §8, §11], and occasionally [ELS, §3, §5]. As mentioned in the incipit of [Str], the unpublished Ph.D. thesis of J. McClure contains an account of the theory of CGWH spaces as well.

**E.1.1. Preparations on compactly generated spaces.** We begin with a definition:

Definition E.1.1.1. Let $X$ be a topological space.

(1) Let $Z \subset X$ be a subspace. We say $Z$ is *$k$-closed* if and only if for every$^2$ compact Hausdorff topological space $K$ and continuous map $g : K \to X$, $g^{-1}(Z)$ is a closed subspace of $K$.

(2) We denote by $k(X)$ the topological space whose underlying set is $X^{\mathrm{set}}$ and whose topology is the coarsest topology such that all the $k$-closed subsets of $X$ are closed in $k(X)$. We call the topology on $k(X)$ the *compactly generated topology*, or *$k$-topology*, on $X$.

Remark E.1.1.2. On Definition E.1.1.1, we make the following observations.

(1) We note that the identity set-function $k(X) \to X$ is always continuous, which is to say that the topology of $k(X)$ is finer than the topology of $X$. Indeed, for any $Z \subset X$ closed, any compact Hausdorff space $K$, and any continuous map $g : K \to X$, the subspace $g^{-1}(Z) \subset K$ is closed. The closed subspaces of $X$ are therefore closed in $k(X)$ as well.

(2) We note that, as a direct consequence of part (2) of Definition E.1.1.1, a subspace $Z \subset X$ is $k$-closed if and only if $Z \subset k(X)$ is closed.

Our definition of “compactly generated” space will rest on:

Lemma E.1.1.3. *Let $X$ be a topological space. The following four conditions are equivalent:*

(1) *For all topological spaces $Y$ and any set-function $f : X \to Y$, the following conditions are equivalent:*

(a) $f$ is continuous.

(b) *For every compact Hausdorff space $K$ and every continuous map $g : K \to X$, the composition $f \circ g$ is continuous.*

(2) *There exists a set $S_X$ of compact Hausdorff spaces such that for all topological spaces $Y$ and any set-function $f : X \to Y$, the following conditions are equivalent:*

(a) $f$ is continuous.

(b) *For every element $K \in S_X$, and every continuous function $g : K \to X$, the composition $f \circ g$ is continuous.*

$^2$Need to address, maybe with cross-reference, why no set-theoretic issues with this definition being over “all” pairs $(K, g)$.

## PDF page 829

**E.1. COMPACTLY GENERATED SPACES** · **829**

(3) *A subspace $U \subset X$ is open if and only if for every compact Hausdorff space $K$ and every continuous function $g : K \to X$, the pre-image $g^{-1}(U)$ is open in $K$.*

(4) *There exists a set $I$, a compact Hausdorff space $K_i$ for each $i \in I$, and for $Y := \coprod_{i \in I} K_i$ the $I$-indexed co-product a submersive map $q : Y \to X$.*

Before we can prove Lemma E.1.1.3, we need the following preparation:

Lemma E.1.1.4 (On bouquets of traits and discrete two-point sets). Let $X$ be a topological space.

(1) *Assume that there exist $x, y \in X$, with $x \ne y$, such that for every subset $A \subset X$ containing $x$, respectively $y$, $A$ is closed. Then $X$ is discrete and satisfies all four conditions in Lemma E.1.1.3.*

(2) *Assume that there exists a unique point $x \in X$ such that every subset $A \subset X$ containing $x$ is closed in $X$.*

(a) *The subspace $X - \{x\} \subset X$ is open and has the discrete topology.*

(b) *Let $Z \subset X$ be the connected component of $x$, and $V$ the closure of $X - Z$ in $X$. Then:*

(i) the natural continuous surjective map

$$
f : Z \coprod V \to X \tag{E.1.1.1}
$$

*is submersive (i.e., topologically a surjective quotient map);*

(ii) *for any compact Hausdorff space $K$ and continuous map $g : K \to V$, the image $g(K) \subset V$ is compact Hausdorff and closed in $V$, with $K \to g(K)$ submersive;*

(iii) *there exists a compact Hausdorff space $K$ and a submersive map $K \to Z$.*

(c) *If $X$ satisfies condition (1) in Lemma E.1.1.3 then it also satisfies condition (2).*

Proof. (1) : Note that $U := X - \{x\}$ is open in $X$ since $\{x\}$ is closed. We first show $U$ is discrete, by proving all subsets of $U$ are closed in $U$. Let $B$ be any subset of $U$ and $C$ be its closure in $X$. Since $B \cup \{x\}$ is closed (as it contains $x$), either $C = B$ or $C = B \cup \{x\}$. Either way, this closure meets $U$ in $B$, so $B$ is closed in $U$. It follows that $X - \{x\}$ is discrete. The same holds for $X - \{y\}$, and since $x \ne y$ we have that $X$ is covered by the open subsets $X - \{x\}$ and $X - \{y\}$ each of which has all points open, so all points of $X$ are open; i.e., $X$ is discrete. Discrete spaces are easily seen to satisfy all four conditions in Lemma E.1.1.3 (since any continuous map to such a space from a compact Hausdorff space has finite image and clopen fibers, and all maps from a discrete space are continuous).

(2.a) is a consequence of the proof of (1). We prove (2.b). Let $Z$ be the connected component of $X$ containing $x$. Then $Z$ is closed in $X$, and since $Z$ and $V$ are two closed subsets of $X$ which cover $X$ clearly (i) holds. Before we prove (ii) and (iii), we make a couple of observations about $Z$ and $V$.

Firstly, we claim the only open subset $U \subset Z$ that is open in $Z$ and contains $x$ is $Z$ itself. Indeed, any such $U$ is closed in $X$ (as all subsets of $X$ containing $x$ are closed by hypothesis) and so closed in $Z$, so $U$ is clopen in the connected $Z$ and non-empty (as it contains $x$), forcing $U = Z$ as desired.

Next consider the closure $V$ of $X - Z$. Similarly to the argument in (1), since $(X - Z) \cup \{x\}$ is closed in $X$ we see that either $V = X - Z$ (in which case the closed $Z$ is also open and $f$ from (E.1.1.1) is a homeomorphism) or $V = (X - Z) \cup \{x\}$. In particular, $V$ meets $X - \{x\}$ in exactly $X - Z$.

(ii): We denote by $K_0$ the (quasi-)compact continuous image of $K$ in $V$. We claim this image is closed in $V$. If $K_0$ contains $x$ then $K_0$ is closed in $X$, hence in $V$. If not then $K_0$ is compact within $V - \{x\}$ which is discrete by (2.a). It follows that $K_0$ is finite, and since every point of $V$ is closed in $V$ it follows again that $K_0$ is closed in $V$ (and even finite discrete). This says $V$ is weakly Hausdorff: for every compact Hausdorff space $K$ and continuous map $g : K \to V$, the image $g(K)$ is closed in $V$ (see Definition E.2.1.1). We now make two (non-circular) forward references to §E.2: by Remark E.2.1.2 the subspace $K_0 \subset V$ is then also weakly Hausdorff, and by Lemma E.2.1.4 it is Hausdorff since it is a continuous image of a compact Hausdorff space. In particular, $K_0$ is compact Hausdorff. Since $g : K \to K_0$ is a continuous surjection between compact Hausdorff spaces, it is submersive.

## PDF page 830

**830** · **CHAPTER E. TOPOLOGICAL STACKS**

(iii): We let $S^1$ be the unit circle, and $0 \in S^1$ a marked point (which we assume, upon parametrizing $S^1$ as $\mathbf{R}/\mathbf{Z}$ under the exponential submersion $\exp(2\pi i t) : \mathbf{R} \to S^1$, to correspond to the image of $t = 0$). We consider the quotient of the set-theoretic coproduct $\coprod_{i \in I} S^1_i$, where $S^1_i$ is $S^1$ and $I$ is the index set $Z - \{x\}$, by the equivalence relation identifying all the marked points of the $S^1_i$’s. We call $0$ the image of each, equivalently any, of the marked points $0_i \in S^1_i$ in the quotient.

We call $\mathbf{H}_I$ the resulting quotient set, which we topologize as follows. For a subset $U \subset \mathbf{H}_I$ containing $0$, we say it is open if and only if it is the union of all but finitely many of the images in $\mathbf{H}_I$ of the $S^1_i$’s along with open subsets $U_i \subset S^1_i$ containing $0_i$ for the remaining finitely many $i \in I$. We say that a subset $U \subset \mathbf{H}_I$ which does not contain $0$ is open if and only if it is a union of the images of open subsets $U_i \subset S^1_i$ for every $i \in I$ (the notation $\mathbf{H}_I$ intends to refer to the Hawaiian earring, which is the special case $I = \mathbf{N}$).

Then $\mathbf{H}_I$ is compact Hausdorff. The map $g$ sending $0$ to $x$ and $S_i - \{0_i\}$ to $i \in Z - \{x\}$ is surjective and we claim it is continuous. Let $U \subset Z$ be an open subset. We want to show $g^{-1}(U)$ is open in $\mathbf{H}_I$. If $U$ contains $x$ then $U = Z$ (recall from the proof of (2.a) that $Z$ has no proper open subset containing $x$), so we may focus on $U$ not containing $x$. But then $g^{-1}(U)$ inside $\mathbf{H}_I$ is the union of the punctured circles $S_i - \{0_i\}$ for $i \in U$, and that is also open in $\mathbf{H}_I$.

To show $g$ is submersive, let $C \subset Z$ be a subset whose pre-image $g^{-1}(C)$ is closed in $\mathbf{H}_I$. We want to show $C$ is closed in $Z$, or equivalently in $X$. If $C \subset \{x\}$ then $C$ is closed. If not, $C$ meets the complement $Z - \{x\}$ of $x$. In particular, $g^{-1}(C)$ contains the image of $S^1_i - \{0_i\}$ for some $i \in I$. But $g^{-1}(C)$ is closed so it contains the closure in $\mathbf{H}_I$ of that $i$th punctured circle, hence it contains $0$. It follows that $C = g(g^{-1}(C))$ contains $g(0) = x$, and hence $C$ is closed in $X$ (as is every subset of $X$ containing $x$, by hypothesis).

(2.c) : For the purposes of proving that (1) implies (2) in Lemma E.1.1.3, by (2.i) and closedness of $Z$ and $V$ in $X$ it is enough to separately treat $Z$ and $V$ in place of $X$. The implication holds for $V$ by (2.ii) (by using the set of closed compact Hausdorff subspaces of $V$), and for $Z$ by (2.iii). $\square$

Remark E.1.1.5. Let $W$ be a trait: the finite topological space $\{0, 1\}$ with $0$ closed and $1$ a generalization of $0$ (equivalently, $W$ is the spectrum of a discrete valuation ring). The proof of (2.iii) from Lemma E.1.1.4 shows that $Z$ is homeomorphic to the glueing along $x \in Z$ of copies of $W$ indexed by the set $Z - \{x\}$. It is a bouquet of traits bundled at $x$, indexed by $Z - \{x\}$.

Proof of Lemma E.1.1.3. We assume (1) and will deduce (4) holds. First we show that naturally $X = k(X)$. Let $Y$ be the topological space $Y := k(X)$; i.e., the set $X^{\mathrm{set}}$ endowed with the $k$-topology on $X$. By (1) applied to this choice of $Y$ and to $f = \mathrm{id} : X \to Y$ the identity set-function on the shared underlying set, $f$ is continuou by design of the topology on $Y$. On the other hand, the topology of $Y$ is finer than that of $X$ by part (1) of Remark E.1.1.2. It follows that $f^{-1}$ (also the identity as a set-function) is continuous, and hence the identity set-function is a homeomorphism; i.e., the two topologies on the set underlying $X$ are the same.

If $X$ is discrete, then the four conditions in Lemma E.1.1.3 all hold for $X$. By Lemma E.1.1.4, it is enough to treat the cases in which either $X$ contains exactly one point $x \in X$ such that any subset $A \subset X$ containing $x$ is closed, or contains no such point. In the former case, by Lemma E.1.1.4(2.c) all four conditions in Lemma E.1.1.3 hold for $X$. We therefore may and do now assume without loss of generality that for any point $x \in X$, there exists a non-closed subset $A \subset X$ such that $x \in A$ holds.

We now call $\Sigma \subset 2^X \times X$ the set of pairs $(A, x)$ such that $A$ is a non-closed subspace of $X$, $x \in A$ is a point. We claim that for every element $(A, x)$ of $\Sigma$, there exists a compact Hausdorff space $K$ and a continuous map $g : K \to X$, such that $g^{-1}(A)$ is not closed in $K$, and $g^{-1}(\{x\}) \ne \varnothing$. Indeed, as $A$ is not closed in $X$, there exists $K$ compact Hausdorff and $g : K \to X$ a continuous map, such that $g^{-1}(A)$ is not closed in $K$ since $X$ has the $k$-topology. If $g^{-1}(\{x\})$ is non-empty we are done, and otherwise define $K' := K \coprod \{x\}$, also compact Hausdorff, and extend $g$ to a continuous map $g' : K' \to X$ defined as $g$ on the $K$ component and sending $x$ to $x$. The pair $(K', g')$ satisfies the required properties.

## PDF page 831

**E.1. COMPACTLY GENERATED SPACES** · **831**

For any fixed element $(A, x) \in \Sigma$, we denote by $\mathscr{C}_{(A,x)}$ the class of all pairs $(K, g)$, such that $K$ is a compact Hausdorff space and $g : K \to X$ is a continuous map such that $g^{-1}(A)$ is not closed in $K$ and $g^{-1}(\{x\})$ is non-empty. Since, by the foregoing, $\mathscr{C}_{(A,x)}$ is non-empty for every $(A, x) \in \Sigma$, by [Jech, Part I, §6, Lemma 6.3, p. 64] and specifically construction (6.4) in loc.cit. (see Remark E.1.1.6) there exists an ordinal $\alpha$ such that $\mathscr{C}_{(A,x)} \cap V_\alpha$ is also non-empty where $V_\alpha$ is the “von Neumann universe” associated to $\alpha$. As $V_\alpha$ is a set, so is $\mathscr{C}_{(A,x)} \cap V_\alpha$. We define

$$
\alpha_{(A,x)} := \inf\{\alpha \mid \mathscr{C}_{(A,x)} \cap V_\alpha \ne \varnothing\}, \quad \alpha := \sup_{(A,x) \in \Sigma} \alpha_{(A,x)} \tag{E.1.1.2}
$$

Both ordinals in (E.1.1.2) exist, as the infimum and the supremum are both defined over *sets* of ordinals. Define

$$
S'_X := \bigcup_{(A,x) \in \Sigma} \mathscr{C}_{(A,x)} \cap V_\alpha, \tag{E.1.1.3}
$$

a non-empty set whose elements are pairs $(K, g)$ with $K$ compact Hausdorff and $g : K \to X$ continuous such that for every $(A, x) \in \Sigma$ there exists some $(K, g) \in S'_X$ such that $g^{-1}(A)$ is not closed in $K$ and $g^{-1}(\{x\})$ is non-empty. We denote by $\sigma := (K, g)$ the elements of $S'_X$, and for every $\sigma \in S'_X$ we denote by $K_\sigma$ the associated compact Hausdorff space and by $g_\sigma : K_\sigma \to X$ the associated continuous map. We further denote by:

$$
q : \coprod_{\sigma \in S'_X} K_\sigma \to X \tag{E.1.1.4}
$$

the map defined on $K_\sigma$ to be $g_\sigma$, for each $\sigma \in S'_X$.

The map $q$ is continuous, as for every $\sigma \in S'_X$, each $g_\sigma$ is a continuous map $K_\sigma \to X$ by design of $S'_X$. We now check that $q$ is surjective. Let $x \in X$ be a point, and $A$ any non-closed subset of $X$ containing $x$. Then $(A, x)$ is an element of $\Sigma$. There exists some $\sigma \in S'_X$ such that $g^{-1}_\sigma(A)$ is not closed in $K_\sigma$, and $g^{-1}_\sigma(\{x\})$ is non-empty. It follows that $x$ is in the image of $g_\sigma$, and hence $q$ is surjective.

Suppose $U \subset X$ is a subspace such that $q^{-1}(U)$ is open in $\coprod_{\sigma \in S'_X} K_\sigma$. We have, setting $U_\sigma := g^{-1}_\sigma(U) \subset K_\sigma$,

$$
q^{-1}(U) = \coprod_{\sigma \in S'_X} U_\sigma. \tag{E.1.1.5}
$$

By assumption on $U$, $q^{-1}(U)$ is open and hence (E.1.1.5) forces $U_\sigma = g^{-1}_\sigma(U)$ to be open in $K_\sigma$ for every $\sigma \in S'_X$. If $U$ is not open in $X$ then the complement $B := X - U$ would be non-closed. For any point $x \in B$, $(B, x)$ is an element of $\Sigma$ and so there exists some $(K, g)$ in $\mathscr{C}_{(B,x)}$. As $\mathscr{C}_{(B,x)}$ is non-empty, by design of $\alpha$ from (E.1.1.2) we have $\mathscr{C}_{(B,x)} \cap V_\alpha \subset S'_X$ is also non-empty. There therefore exists $\sigma = (K, g)$ in $S'_X$ such that $g^{-1}(B)$ is not closed in $K$, contradicting the openness of $g^{-1}(X - B) = U_\sigma$.

Now that $q$ is submersive, a function $f : X \to Y$ is continuous if and only if $f \circ q$ is continuous. This assertion is in turn equivalent to $f \circ g_\sigma : K_\sigma \to Y$ being continuous for all $\sigma \in S'_X$ by the universal property of topological co-products. Hence, also (1) implies (3), and similarly (4) implies (3).

Next we show (1) implies (2). We now write $\mathscr{C}$ for the class of all compact Hausdorff spaces, and we define the class function $\phi : S'_X \to \mathscr{C}$ by $\phi(\sigma) = K_\sigma$. This is a class function (see [Kunen, Ch. I, §6]) since it is a binary relation on $S'_X \times \mathcal{C}$ such that $(\sigma, K) = (\sigma, K')$ implies $K = K'$. By the Axiom of Replacement (see [Jech, Part I, §1, (1.7)] and [Kunen, Ch. I, §6, Axiom 6]) the image of $\phi$ is a set, which we denote $S_X$. By design of $S'_X$, for every $K \in S_X$ there exists a continuous map $g_K : K \to X$ such that a set-function $f : X \to Y$ is continuous if and only if $f \circ g_K$ is continuous for all $K \in S_X$. In particular, for any set-function $f : X \to Y$, $f$ is continuous if and only if $f \circ g$ is continuous for all $K \in S_X$ and all continuous maps $g : K \to X$. The set $S_X$ therefore satisfies the requirements of part (2) of the Lemma.

## PDF page 832

**832** · **CHAPTER E. TOPOLOGICAL STACKS**

Conversely, suppose that (2) holds. If part (a) of (1) holds, then so does part (b) of (1). Conversely, if part (b) of (1) holds then part (b) of (2) also holds and so by (2) we deduce that $f$ is continuous, implying that part (a) of (1) holds. Part (1) therefore follows from part (2). We now show the equivalence of (2) and (4). If (2) holds then we choose $I = S'_X \coprod X$ where $S'_X$ is the set of pairs $(K, g)$ for $K \in S_X$ and $g : K \to X$ continuous. For every $i \in I$, either $i \in S'_X$, in which case $i = \sigma = (K_\sigma, g_\sigma)$, and we define $K_i := K_\sigma$ and $g_i := g_\sigma$. Otherwise, we have $i \in X$, in which case $i = x$ for a point $x \in X$, and we define $K_i := \{x\}$ and $g_i$ the unique continuous map sending $x$ to the point $x \in X$. We may therefore define the map $q : \coprod_{i \in I} K_i$ as the co-product of the $g_i$ for all $i \in I$. The resulting map:

$$
q : \coprod_{i \in I} K_i \to X
$$

is a submersive map by [Bou-GT, Ch. I, §2, Prop. 6] or part (1) of [SP, Tag 08ZK], as it is surjective by design and, by (2) and the universal property of topological co-products, a function $f : X \to Y$ is continuous if and only if $f \circ q$ is. This proves (2) implies (4). The converse is obvious (using $S_X = I$), so (2) and (4) are equivalent.

If (4) holds then (3) does since it is enough to test openness of $U$ on those compact Hausdorff spaces indexed by $I$. It remains to prove (3) implies (1). Irrespective of assuming that (3) holds, we see that part (b) of (1) follows from part (a). Assuming that (3) holds, we may further assume that part (b) of (1) holds. We let $V \subset Y$ be an open subspace, and call $U := f^{-1}(V)$, and observe that for any compact Hausdorff space $K$ and any continuous map $g : K \to X$, $g^{-1}(U) = (f \circ g)^{-1}(V)$. As $f \circ g$ is continuous and $V$ is open, we deduce that $g^{-1}(U)$ is open in $K$. As $K$ and $g$ are arbitrary, we deduce from (3) that $U$ is open, and hence $f$ is continuous. $\square$

Remark E.1.1.6. Construction (6.4) from [Jech, Part I, §6] can be found on p. 65 of loc.cit. after [Jech, Part I, §6, Lemma 6.3] upon which it rests, and it is credited to Dana Scott and often referred to as “Scott’s trick”. It rests on the Axiom of Regularity. In particular, the construction of the set $S_X$ in the proof of Lemma E.1.1.3 does not use any stronger version of the Axiom of Choice, and is therefore valid within ZFC, which is what this Remark is aimed at highlighting (in fact, it does not use the Axiom of Choice either).

Definition E.1.1.7. We define:

(1) a topological space $X$ to be a *compactly generated space* if and only if it satisfies the equivalent conditions of Lemma E.1.1.3.

(2) the category $\mathbf{CG}$ whose objects are compactly generated spaces, and morphisms are continuous maps of topological spaces. We shall refer to $\mathbf{CG}$ as the *category of compactly generated spaces*.

Remark E.1.1.8. On the construction of $k(X)$ from Definition E.1.1.1 we observe that we can use the terminology introduced in Definition E.1.1.1 to rephrase Definition E.1.1.7. Specifically, a topological space $X$ is compactly generated if and only if $k(X) = X$. Since $k(X)$ and $X$ share the same underlying set, it makes sense to compare their topologies.

The following example exhibits compact generation as a non-vacuous condition on topological spaces.

Example E.1.1.9. Let $X$ be an uncountable set equipped with the co-countable topology (i.e., the open subsets are $\emptyset$ and complements of countable subsets, so the closed subsets are $X$ and the countable subsets). We claim $X$ is not compactly generated. Indeed, we claim that $k(X)$ is discrete.

To see this, let $Z$ be any subset of $X$ and $K$ any compact Hausdorff space, with $g : K \to X$ an arbitrary continuous map, so $g(K)$ is a compact subspace of $X$ and inherits the co-countable topology from $X$. It is therefore finite discrete, and $Z \cap g(K)$ is open in $g(K)$. As such, its pre-image in $K$, which agrees with $g^{-1}(Z)$, is also open. This proves that any subset of $X$ is $k$-open in $X$, and hence $k(X)$ is discrete.

## PDF page 833

**E.1. COMPACTLY GENERATED SPACES** · **833**

If $X$ was compactly generated then it would have to be discrete. As $X$ is uncountable, the co-countable topology on it is not discrete. Any non-closed subspace $Z \subset X$ is therefore a $k$-closed non-closed subspace. For further discussion of examples for the co-countable topology, we refer to [StSe, Part II, 29, 21].

We refer to §E.2.4 for an example-driven illustration of the relations between the various definitions of compact generation present within the literature. This is located after §E.2.3 so as to facilitate the construction of examples resting on results discussed up to and including §E.2.3.

**E.1.2. Categorical and topological stabilities of compactly generated spaces.** Before moving forward, we recall several facts about the large category $\mathbf{CG}$ of compactly generated spaces and some important closure properties it enjoys. Our main sources for the materials collected in this subsection are [LGL, §2, §3, §5], [McC, §2], [Str, §1, §2], [Rezk, §8]. We shall refer to [ELS, §5] as well, concerning arguments towards the cartesian closure of $\mathbf{CG}$ as a cartesian monoidal category.

We first recall the relation between the large categories $\mathbf{CG}$ and $\mathbf{Spaces}$. This latter, recall, is the category whose objects are topological spaces, and morphisms are continuous maps between topological spaces (see part (2) of Notation E.0.0.1). The forgetful functor

$$
u_{\mathrm{cg}} : \mathbf{CG} \to \mathbf{Spaces} \tag{E.1.2.1}
$$

sends a compactly generated space to itself as a topological space, and continuous maps to continuous maps.

**Lemma E.1.2.1.** *The assignment $X \rightsquigarrow k(X)$ is a functor*

$$
k : \mathbf{Spaces} \to \mathbf{CG} \tag{E.1.2.2}
$$

*that satisfies the following properties:*

(1) *$k$ is right-adjoint to the forgetful functor $u_{\mathrm{cg}} : \mathbf{CG} \to \mathbf{Spaces}$. Explicitly, any continuous $f : X \to Y$ with $k$-closed $X$ uniquely factors continuously through the natural continuous bijection $k(Y) \to Y$.*

(2) *The unit $\eta : \mathrm{id} \to k \circ u_{\mathrm{cg}}$ of the adjunction $(u_{\mathrm{cg}}, k)$ is a natural isomorphism of functors; this is the inverse $X \to k(X)$ to the natural homeomorphism $k(X) \to X$ for $k$-closed $X$.*

*Proof.* We check functoriality of the formation of $k(\cdot)$, from which the rest is clear (as $k(X) \to X$ via $\mathrm{id}_X$ is a homeomorphism for $k$-closed $X$). We have to show that if $f : X \to Y$ is a continuous map of topological spaces then any $k$-closed subset $Z$ of $Y$ has $k$-closed pre-image in $X$. For any continuous map $g : K \to X$ from a compact Hausdorff space $K$, the pre-image $g^{-1}(f^{-1}(Z))$ of $f^{-1}(Z)$ in $K$ agrees with the pre-image $(f \circ g)^{-1}(Z)$ of $Z$ to $K$ under the composition with $f$, and it is therefore closed in $K$ by continuity of the composition $f \circ g$. It follows $f^{-1}(Z)$ is $k$-closed. $\square$

We now discuss stability properties of $\mathbf{CG}$ under several categorical operations, starting with formation of small limits and small colimits:

**Lemma E.1.2.2.** *The category $\mathbf{CG}$ contains all small limits and all small colimits. Moreover, for any small category $I$ and diagram $P : I \to \mathbf{CG}$:*

(1) $\lim_I P$ in $\mathbf{CG}$ is computed as

$$
\lim_I P = k(\lim_I u_{\mathrm{cg}} \circ P) \tag{E.1.2.3}
$$

*upon evaluating $k(\cdot)$ on the limit of the small diagram $u_{\mathrm{cg}} \circ P$ in $\mathbf{Spaces}$.*

(2) *$\operatorname{colim}_I P$ in $\mathbf{CG}$ is computed in $\mathbf{Spaces}$, i.e. the forgetful functor $u_{\mathrm{cg}}$ reflects and commutes with small colimits.*

*Proof.* Assertion (1) is immediate from the universal property of $\lim_I$ in $\mathbf{Spaces}$ and Lemma E.1.2.1(1). For (2), the task amounts to showing that the topological colimit $\operatorname{colim}_I(u_{\mathrm{cg}} \circ P)$ is compactly generated. A

## PDF page 834

**834** · **CHAPTER E. TOPOLOGICAL STACKS**

small colimit in $\mathbf{Spaces}$ is constructed as a quotient of a small co-product, so it is enough to check that small co-products and quotient maps preserve compact generation. For each $i \in I$, let $J_i$ be a set as in part (4) of Lemma E.1.1.3 applied to the compactly generated space $(u_{\mathrm{cg}} \circ P)(i)$ and let $q_i : \coprod_{j \in J_i} K_j \to (u_{\mathrm{cg}} \circ P)(i)$ be a submersive map. Then

$$
q := \coprod_{i \in I} q_i : \coprod_{i \in I} \coprod_{j \in J_i} K_j \to \coprod_{i \in I} (u_{\mathrm{cg}} \circ P)(i)
$$

is a submersive map, and hence $\coprod_I(u_{\mathrm{cg}} \circ P)$ is compactly generated by Lemma E.1.1.3(4). Moreover, if $f : X \to Z$ is a quotient map with $X$ compactly generated then $Z$ inherits (4) in Lemma E.1.1.3 from $X$ via composing with $f$ since $f$ is submersive. $\square$

**Remark E.1.2.3.** On limits and colimits in $\mathbf{CG}$, we make the following observations. Contrary to small colimits, small limits in $\mathbf{CG}$ are generally not computed in $\mathbf{Spaces}$. This does not hold already for products: see Lemma E.2.4.9.

Both $\mathbf{Spaces}$ and $\mathbf{CG}$ contain finite products (by direct construction in $\mathbf{Spaces}$, or by [SP, Tag 08ZT], and by Lemma E.1.2.2 for $\mathbf{CG}$). The topology on the product $X \times Y$ internal to $\mathbf{CG}$ of two compactly generated spaces is not generally the product of the topologies on $X$ and $Y$, as noted in Remark E.1.2.3. It is therefore our preference to introduce notation to distinguish the two products, and derivative functorial constructions.

**Definition E.1.2.4.** Let $X, Y$ be compactly generated spaces. Upon writing:

$$
X' := u_{\mathrm{cg}}(X), \quad Y' := u_{\mathrm{cg}}(Y)
$$

for their underlying topological spaces, we define:

(1) $X \times Y$ to be the product of $X$ and $Y$ internal to $\mathbf{CG}$.

(2) We define $X \times_0 Y$ to be the product of $X'$ and $Y'$ internal to $\mathbf{Spaces}$, i.e. the set $X^{\mathrm{set}} \times Y^{\mathrm{set}}$ endowed with the product topology.

(3) For $Z$ a compactly generated space and $f : X \to Z$, $g : Y \to Z$ continuous maps, upon writing $Z' := u_{\mathrm{cg}}(Z)$, and denoting by $f, g$ the same continuous maps, we define $X \times^0_{f,Z,g} Y$ to be the fibre product $X' \times_{f,Z',g} Y'$ in $\mathbf{Spaces}$, i.e. the pre-image $(f,g)^{-1}(\Delta_{Z'}(Z')) \subset X \times_0 Y$ of the continuous map:

$$
(f,g) : X \times_0 Y \to Z \times_0 Z.
$$

We refer to $X \times^0_{f,Z,g} Y$ as the *topological fibre product*.

(4) For $I$ a set, and $P : I \to \mathbf{CG}$ a diagram, we denote by $\prod^0_I P$ the $I$-indexed product of $u_{\mathrm{cg}} \circ P$ in $\mathbf{Spaces}$. We refer to $\prod^0_I P$ as the *topological product*.

**Remark E.1.2.5.** On Definition E.1.2.4, we make the following observations.

(1) Part (2) of Definition E.1.2.4 follows [Str, Def. 2.3]. We note that no notation has been introduced in Definition E.1.2.4 for $I$-indexed co-products since (by Lemma E.1.2.2(2)) the topological co-product $\coprod_I u_{\mathrm{cg}} \circ P$ of any $I$-indexed diagram $P : I \to \mathbf{CG}$ is compactly generated and computes the co-product in $\mathbf{CG}$. The notation $\coprod_I$ is, therefore, un-ambiguous.

(2) For compactly generated $X, Y$, we have $X \times Y = k(X \times_0 Y)$ by Lemma E.1.2.2(1). More generally, for any set $I$ and $I$-indexed diagram $P : I \to \mathbf{CG}$, the product $\prod_I P(i)$ in $\mathbf{CG}$ is computed as:

$$
k\left(\prod_I (u_{\mathrm{cg}} \circ P)(i)\right)
$$

by Lemma E.1.2.2(1).

An important property of $\mathbf{CG}$ is that it has an internal Hom-space bifunctor endowing $\mathbf{CG}$ with a cartesian-closed monoidal structure (we refer the reader to [Kel, §1.5], and [MacL, Ch. VII, §7, §8], for

## PDF page 835

**E.1. COMPACTLY GENERATED SPACES** · **835**

foundational material on monoidal categories; the term “cartesian” refers to the $\otimes$ bifunctor, denoted $\square$ in [MacL, Ch. VII, §7, §8], being the cartesian product). We briefly discuss this aspect and some consequences of direct use for this appendix, with a view towards the next section on compactly generated weakly Hausdorff spaces, where the weak Hausdorff condition on objects will strengthen consequences of cartesian closure. Our standard references for closed symmetric monoidal categories are [MacL, Ch. VII, §1] for monoidal categories in general, [MacL, Ch. VII, §7] and [EK, Ch. III] for closed categories and closed symmetric monoidal categories, and [MacL, Ch. VII, §8] for the category of compactly generated Hausdorff spaces. We do not incorporate any separation condition into the definition of the objects of $\mathbf{CG}$, and we will impose only a weakening of the Hausdorff separation condition when we introduce the full subcategory of weakly Hausdorff compactly generated spaces, but the proof we give for cartesian closedness of $\mathbf{CG}$ follows the same general pattern of [Ste, §5] and [MacL, Ch. VII, §8].

A reference pinpointing the general structures underlying cartesian closedness of convenient categories of spaces is [ELS, §5]. We further refer the reader to Mac Lane's paper [MacL2] where associativity and commutativity coherences in monoidal categories are derived from the basic defining axioms of coherence within a monoidal category (see diagrams (3), (4), (7) in [MacL, Ch. VII, §1]). The theme of how to derive general coherences from (3),(4) and (7) of [MacL, Ch. VII, §1] is reprised in [MacL, Ch. VII, §2] and developed in [MacL2], with particular emphasis on [MacL2, Thm. 4.2], where coherence of the associativity and commutativity natural isomorphisms of a monoidal category are reduced to the pentagonal [MacL2, §3, 3.5] and hexagonal [MacL2, §4, 4.5] axioms. We discuss the closed monoidal category structure on $\mathbf{CG}$ so as to include self-contained arguments for $\mathbf{CG}$, compatibly with the definition of compact generation in Definition E.1.1.7. Our main references for results on function spaces within $\mathbf{CG}$ and the resulting closed monoidal category structure on $\mathbf{CG}$ (and later $\mathbf{CGWH}$) are [LGL, §5], [ELS, §5], [Str, §2], and [Rezk, §8].

**Definition E.1.2.6.** Let $X$ and $Y$ be compactly generated spaces.

(1) For any compact Hausdorff space $K$, continuous map $g : K \to X$, and open subspace $U \subset Y$, let $N(g,K,U)$ denote the subset of $\mathrm{C}(X,Y)$ consisting of continuous maps $f : X \to Y$ such that $(f \circ g)(K) \subseteq U$:

$$
N(g,K,U) = \mathrm{C}(X,Y) \times_{g^*,\mathrm{C}(K,Y),j_*} \mathrm{C}(K,U) \tag{E.1.2.4}
$$

where $g^*: \mathrm{C}(X,Y) \to \mathrm{C}(K,Y)$ is $f \mapsto f \circ g$ and $j_*: \mathrm{C}(K,U) \to \mathrm{C}(K,Y)$ is $f \mapsto j \circ f$ for $j : U \to Y$ the open immersion. (Note that $N(g,\emptyset,\emptyset) = \mathrm{C}(X,Y)$ for the unique $j : \emptyset \to X$.)

We denote by $\mathcal{B}$ the set of subsets $N \subset \mathrm{C}(X,Y)$ of the form $N = N(g,K,U)$ for some compact Hausdorff space $K$, continuous map $g : K \to X$, and open subspace $U \subset Y$.

(2) The *compact-open topology* on $\mathrm{C}(X,Y)$ is the unique topology on $\mathrm{C}(X,Y)$ admitting $\mathcal{B}$ as a sub-base (see [SP, Tag 08ZI] and [SP, Tag 08ZJ], as well as [Du, Ch. III, Thm. 3.1] and the discussion after [Ke, Ch. 1, Thm. 12, p. 48]). In other words, finite intersection among members of $\mathcal{B}$ are a base for the topology. We call the sub-base $\mathcal{B}$ the *standard sub-base* for the compact-open topology on $\mathrm{C}(X,Y)$. (In Lemma E.1.2.8 we give a set-theoretic consistency check, showing that the compact-open topology can be defined using a set of triples $(g,K,U)$ rather than just a class.)

**Remark E.1.2.7.** We note that the compact-open topology referred to above is not the usual notion of topology on function spaces under the same name. Indeed, for topological spaces $X$ and $Y$, one usually defines the compact-open topology on $\mathrm{C}(X,Y)$ as the topology having as sub-base the collection of subsets $N(g,K,U)$ for $g : K \to X$ an immersion of a compact space $K$. Throughout this appendix, the terminology “compact-open topology” will solely be referring to the topology introduced in Definition E.1.2.6(2), generating a finer topology. The topology defined in Definition E.1.2.6 is a topology on $\mathrm{C}(X,Y)$, for compactly generated $X$ and $Y$, such that $k(\mathrm{C}(X,Y))$ defines an internal mapping functor promoting $\mathbf{CG}$ to a closed monoidal category with respect to the cartesian monoidal structure (we refer the reader to [MacL, Ch. VII] for background on cartesian monoidal categories, and to [MacL, Ch. III, §1, Prop. 5] for the construction of a canonical monoidal structure

## PDF page 836

**836** · **CHAPTER E. TOPOLOGICAL STACKS**

on categories with finite products and a final object). Proving this fact is the purpose of the next results (see Lemma E.1.2.12 and Proposition E.1.2.13).

The reader may wonder whether the $k$-topology on the compact-open topology on $\mathrm{C}(X,Y)$ is the only topology promoting the set-valued bifunctor of continuous maps between compactly generated spaces to an internal Hom-functor promoting $\mathbf{CG}$ to a cartesian closed monoidal category. We refer the reader to [ELS, §5] for a discussion pertaining uniqueness aspects of the $k$-topology associated to the compact-open topology being considered (see especially [ELS, §5, Thm. 5.15]). We follow [LGL, §5] throughout the discussion on function spaces of compactly generated spaces, and later on compactly generated spaces incorporating a separation condition (see Proposition E.2.2.10).

**Lemma E.1.2.8.** *Let $X$ and $Y$ be compactly generated spaces. There exists a set $S_{X,Y}$, and for any $\sigma \in S_{X,Y}$ a triple $(g_\sigma,K_\sigma,U_\sigma)$ with $K_\sigma$ a compact Hausdorff space, $g_\sigma : K_\sigma \to X$ a continuous map, and $U_\sigma \subset Y$ an open subspace such that the coarsest topology on $\mathrm{C}(X,Y)$ with the property that every element of the set*

$$
\{N(g_\sigma,K_\sigma,U_\sigma), \sigma \in S_{X,Y}\} \tag{E.1.2.5}
$$

*is open in $\mathrm{C}(X,Y)$ is the compact-open topology on $\mathrm{C}(X,Y)$.*

*Proof.* We fix a subset $N \subset \mathrm{C}(X,Y)$ of the form $N = N(g,K,U)$ as in (E.1.2.4) for a compact Hausdorff space $K$, a continuous map $g : K \to X$, an open subspace $U \subset Y$. We call $\mathscr{C}_N$ the class of those triples $(g,K,U)$ such that $K$ is a compact Hausdorff space, $g : K \to X$ is a continuous map, and $U \subset Y$ is an open subspace satisfying

$$
N(g,K,U) = N.
$$

By the choice of $N$, $\mathscr{C}_N$ is non-empty. There therefore exists an ordinal $\alpha$ such that $\mathscr{C}_N \cap V_\alpha$ is non-empty. By [Jech, Part I, §6, Lemma 6.3] (see construction (6.4) in [Jech, Part I, §6, p. 65]), upon defining

$$
\alpha_N := \inf\{\alpha \mid \mathscr{C}_N \cap V_\alpha \ne \varnothing\}, \quad \alpha := \sup\{\alpha_N \mid N \in \mathcal{B}\} \tag{E.1.2.6}
$$

we have $\mathcal{C}_N \cap V_\alpha \ne \varnothing$ for every $N \in \mathcal{B}$, where $\mathcal{B}$ is the standard sub-base for the compact-open topology on $\mathrm{C}(X,Y)$ (see Definition E.1.2.6(2)). We note that the ordinals $\alpha_N$ and $\alpha$ from (E.1.2.6) indeed exist, as the infimum and supremum are defined over *sets* of ordinals. We call $S_N := \mathcal{C}_N \cap V_\alpha$, a set. We further call $S_{X,Y}$ the set:

$$
S_{X,Y} := \bigcup_{N \in \mathcal{B}} S_N.
$$

By design of $\alpha$, for every $N \in \mathcal{B}$ there exists $(g,K,U) \in S_{X,Y}$ such that $N = N(g,K,U)$. $\square$

**Construction E.1.2.9.** We let $X, Y$ be compactly generated spaces, and endow the set $\mathrm{C}(X,Y)$ with the compact-open topology of Definition E.1.2.6. Define:

$$
\mathscr{C}ont_k(X,Y) := k(\mathrm{C}(X,Y)).
$$

We now check that $\mathscr{C}ont_k$ is bifunctorial on $\mathbf{CG}$ (in analogy with [LGL, §5, Thm. 5.5], see especially the discussion after [LGL, §5, Lemma 5.2], [MacL, Ch. VIII, Thm. 3], [Str, Lemma 2.10] and [Rezk, Prop. 8.2]).

**Lemma E.1.2.10.** *Let $X, Y$ be compactly generated spaces. Then formation of:*

$$
\mathscr{C}ont_k(X,Y)
$$

*is contravariantly functorial in $\mathbf{CG}$ with respect to $X$, and covariantly functorial in $\mathbf{CG}$ with respect to $Y$.*

*Proof.* For $f : Y \to Y'$ a continuous map in $\mathbf{CG}$, $U \subset Y'$ an open subspace with $j' : U \to Y'$ the open immersion, $K$ a compact Hausdorff space, and $a : K \to X$ a continuous map, we claim

$$
f_* : \mathrm{C}(X,Y) \to \mathrm{C}(X,Y'), \quad g \rightsquigarrow \phi_f(g) := f \circ g \tag{E.1.2.7}
$$

## PDF page 837

**E.1. COMPACTLY GENERATED SPACES** · **837**

is continuous. Clearly it is enough to check that the pre-image under $f_*$ of every element of the standard sub-base for the compact-open topology on $\mathrm{C}(X,Y')$ is an element of the standard sub-base for the compact-open topology on $\mathrm{C}(X,Y)$. By design of $N(a,K,U)$, we have

$$
(f_*)^{-1}(N(a,K,U)) = N(a,K,f^{-1}(U)). \tag{E.1.2.8}
$$

Applying $k$ then gives a continuous map

$$
\mathscr{C}ont_k(X,Y) \to \mathscr{C}ont_k(X,Y')
$$

This proves that $\mathscr{C}ont_k(X,Y)$ is covariantly functorial with respect to $Y$.

Now for $f : X' \to X$ be a continuous map in $\mathbf{CG}$, $K$ a compact Hausdorff space, $a : K \to X'$ a continuous map, and $U \subset Y$ an open subspace, let $f^* : \mathrm{C}(X,Y) \to \mathrm{C}(X',Y)$ be $g \mapsto g \circ f$. By a similar token as in the foregoing we have

$$(f^*)^{-1}(N(a,K,U)) = N(f \circ a,K,U),$$

giving continuity of $f^*$ with respect to the compact-open topology on source and target. Applying $k$ to $f^*$ gives

$$f^* : \mathscr{C}ont_k(X,Y) \to \mathscr{C}ont_k(X',Y)$$

as a continuous map. This proves that $\mathscr{C}ont_k(X,Y)$ is contravariantly functorial with respect to $X$. $\square$

The conclusion of Lemma E.1.2.10 is that $\mathscr{C}ont_k$ is a bifunctor:

$$
\mathscr{C}ont_k : \mathbf{CG}^{\mathrm{opp}} \times \mathbf{CG} \to \mathbf{CG}.
$$

Our aim is to now prove that $\mathscr{C}ont_k$ is compatible with the internal product in $\mathbf{CG}$, and, specifically, satisfies a natural Hom-$\otimes$ adjunction, analogously to [MacL, Ch. VII, §8, (2)] and [Ste, Thm. 5.6], and as proved in [LGL, Thm. 5.5], [Str, Prop. 2.20], and [Rezk, Prop. 8.8]. We provide an argument here as well for the sake of completeness, and to further highlight relations among the various approaches within the literature. We will mostly rely upon [LGL, §5], [Str, §2] and [Rezk, §8].

**Remark E.1.2.11.** We highlight here how the approaches to compactly generated function spaces in the above sources relate to one another. Throughout this work, we proceed as in [LGL, §5], and, specifically, we define the compact-open topology on function spaces in the sense of Definition E.1.2.6, following [LGL, §5, p. 160]. This is the approach adopted in [Str, §2] as well. We caution the reader that the topology defined on function spaces in [Rezk, §8, 8.1] is not generally equivalent to the compact-open topology as defined in [LGL, §5, p. 160] and [Str, Def. 2.8], and throughout this appendix. It is in fact finer (see [Rezk, Lemma 8.4]). However, applying $k$ removes this discrepancy: by [ELS, Thm. 5.15], the compactly generated function spaces associated to either topology are the same. Equivalently, the functor $k(\cdot)$ identifies the topology defined in [Rezk, §8, 8.1] on function spaces with the $k$-topology on the compact-open topology defined in [LGL, §5, p. 160], [Str, Def. 2.8], and this appendix.

We have the following:

**Lemma E.1.2.12.** *Let $X, Y, Z$ be compactly generated spaces. The natural set-map*

$$\theta_{X,Y,Z} : \mathscr{C}ont_k(X \times Y,Z) \to \mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,Z))$$

*defined by $f \mapsto (x \mapsto f(x,\cdot))$ is a homeomorphism. In particular,*

$$\theta^{-1}_{\mathscr{C}ont_k(X,Y),X,Y}(\mathrm{id})$$

*is the evaluation map*

$$\mathscr{C}ont_k(X,Y)^{\mathrm{set}} \times X^{\mathrm{set}} \to Y^{\mathrm{set}}$$

*sending a pair $(f,x)$ to $f(x)$.*

## PDF page 838

**838** · **CHAPTER E. TOPOLOGICAL STACKS**

*Proof.* We define the “evaluation” set-function

$$
\mathrm{ev} : \mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}}) \times Y^{\mathrm{set}} \to Z^{\mathrm{set}}, \quad (f,y) \mapsto \mathrm{ev}(f,y) := f(y) \tag{E.1.2.9}
$$

and the set-function:

$$
\psi : \mathrm{Map}(X^{\mathrm{set}},\mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}})) \to \mathrm{Map}(X^{\mathrm{set}} \times Y^{\mathrm{set}},Z^{\mathrm{set}}), \quad f \mapsto \psi(f) := \mathrm{ev} \circ (f,\mathrm{id}_Y) \tag{E.1.2.10}
$$

natural with respect to $X, Y$ and $Z$. Explicitly, $\psi(f)(x,y) = f(x)(y)$.

We check that

$$
\psi(\mathrm{C}(X,\mathrm{C}(Y,Z)) \subset \mathrm{C}(X \times Y,Z) \tag{E.1.2.11}
$$

as subsets of $\mathrm{Map}(X^{\mathrm{set}} \times Y^{\mathrm{set}},Z^{\mathrm{set}})$. To this end, define the set-function

$$
\eta : \mathrm{Map}(X^{\mathrm{set}},\mathrm{Mat}(Y^{\mathrm{set}},Z^{\mathrm{set}})) \to \mathrm{Map}(X^{\mathrm{set}} \times Y^{\mathrm{set}},\mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}}) \times Y^{\mathrm{set}}) \tag{E.1.2.12}
$$

by

$$f \mapsto \eta(f) := (f,\mathrm{id}_Y).$$

If $f \in \mathrm{C}(X,\mathrm{C}(Y,Z))$, where continuity of $f$ is with respect to the intrinsic topology on $X$ and the compact-open topology on $\mathrm{C}(Y,Z)$ then $f$ factors uniquely through $k(\mathrm{C}(Y,Z)) \to \mathrm{C}(Y,Z)$ since $X$ is in $\mathbf{CG}$, so $\eta(f)$ is continuous as a map

$$X \times Y \to k(\mathrm{C}(Y,Z)) \times Y = k(\mathrm{C}(Y,Z) \times_0 Y)$$

by functoriality of the $k$-topology. As $\psi$ from (E.1.2.10) is by definition $\psi = \mathrm{ev} \circ \eta$, with $\mathrm{ev}$ the evaluation set-function from (E.1.2.9), to prove the containment in (E.1.2.11) it is enough to check that the restriction of $\mathrm{ev}$ to the set-theoretic product $\mathrm{C}(Y,Z) \times Y^{\mathrm{set}}$ is continuous with respect to the topology of $k(\mathrm{C}(Y,Z) \times_0 Y)$ and the intrinsic topology on $Z$.

We therefore let $U \subset Z$ be an open subspace, $K$ a compact Hausdorff space, and $a : K \to k(\mathrm{C}(Y,Z) \times_0 Y)$ a continuous map. It is enough to check that $(\mathrm{ev} \circ a)^{-1}(U)$ is open in $K$. We define the continuous composition

$$
a_1 : K \xrightarrow{a} k(\mathrm{C}(Y,Z) \times_0 Y) \xrightarrow{\mathrm{id}} \mathrm{C}(Y,Z) \times_0 Y \xrightarrow{\mathrm{pr}_1} \mathrm{C}(Y,Z) \tag{E.1.2.13}
$$

We further define the continuous composition

$$
a_2 : K \xrightarrow{a} k(\mathrm{C}(Y,Z) \times_0 Y) \xrightarrow{\mathrm{id}} \mathrm{C}(Y,Z) \times_0 Y \xrightarrow{\mathrm{pr}_2} Y \tag{E.1.2.14}
$$

We have:

$$
\begin{aligned}
(\mathrm{ev} \circ a)^{-1}(U) &= a^{-1}(\mathrm{ev}^{-1}(U)) \\
&= \{t \in K \mid (a_1(t),a_2(t)) \in \mathrm{ev}^{-1}(U)\} \\
&= \{t \in K \mid a_1(t)(a_2(t)) \in U\}. \tag{E.1.2.15}
\end{aligned}
$$

Let $t_0$ be an element in $a^{-1}(\mathrm{ev}^{-1}(U)) \subset K$. The map $a_1(t_0) : Y \to Z$ is continuous, and upon composing it with $a_2 : K \to Y$ we obtain a continuous map $g := a_1(t_0) \circ a_2 : K \to Z$. As $g^{-1}(U)$ is open in $K$ and contains $t_0$, and $K$ is compact Hausdorff, there exists open $V \subset g^{-1}(U)$ containing $t_0$ and having compact closure $K' := \overline{V}$ in $K$. It follows that

$$
a_1(t_0) \in N(a_2,K',U) \subset \mathrm{C}(Y,Z). \tag{E.1.2.16}
$$

Since $a_1 : K \to \mathrm{C}(Y,Z)$ is continuous with respect to the compact-open topology on $\mathrm{C}(Y,Z)$ and the topology on $K$, the subset $a_1^{-1}(N(a_2,K',U))$ is open in $K$. We claim that

$$
a_1^{-1}(N(a_2,K',U)) \cap K' \subset (\mathrm{ev} \circ a)^{-1}(U). \tag{E.1.2.17}
$$

Let $t \in a_1^{-1}(N(a_2,K',U)) \cap K'$ be an element. Then $a_1(t)(a_2(t))$ is an element of $U$, and hence

$$t \in \{t' \in K \mid a_1(t')(a_2(t')) \in U\} = (\mathrm{ev} \circ a)^{-1}(U)$$

## PDF page 839

**E.1. COMPACTLY GENERATED SPACES** · **839**

by (E.1.2.15). This proves the containment claimed in (E.1.2.17).

We have found the open neighborhood $a_1^{-1}(N(a_2,K',U)) \cap V$ of $t_0$ in $K$ contained in $(\mathrm{ev} \circ a)^{-1}(U)$. Indeed, $t_0$ is contained in $V$ by design of $V$ and is contained in $a_1^{-1}(N(a_2,K',U))$ by (E.1.2.16). As $t_0$ is an arbitrary element of $(\mathrm{ev} \circ a)^{-1}(U)$, we deduce that $(\mathrm{ev} \circ a)^{-1}(U)$ is open as desired. We have shown $\psi$ defines a visibly injective set-function:

$$
\psi_{X,Y,Z} : \mathrm{C}(X,\mathrm{C}(Y,Z)) \to \mathrm{C}(X \times Y,Z). \tag{E.1.2.18}
$$

To show that $\psi_{X,Y,Z}$ is surjective, we build a continuous inverse as follows. We define the set-function

$$
i : X^{\mathrm{set}} \to \mathrm{Map}(Y^{\mathrm{set}},X^{\mathrm{set}} \times Y^{\mathrm{set}}), \quad x \mapsto (y \mapsto (x,y)) \tag{E.1.2.19}
$$

and

$$
\psi' : \mathrm{Map}(X^{\mathrm{set}} \times Y^{\mathrm{set}},Z^{\mathrm{set}}) \to \mathrm{Map}(X^{\mathrm{set}},\mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}})), \quad h \mapsto \psi'(h) := h_{**}(i) \tag{E.1.2.20}
$$

where $h_*$ is the set-function

$$h_* : \mathrm{Map}(Y^{\mathrm{set}},X^{\mathrm{set}} \times Y^{\mathrm{set}}) \to \mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}}), \quad g \mapsto h_*(g) := h \circ g$$

and $h_{**}$ is the set-function

$$
h_{**} : \mathrm{Map}(X^{\mathrm{set}},\mathrm{Map}(Y^{\mathrm{set}},X^{\mathrm{set}} \times Y^{\mathrm{set}})) \to \mathrm{Map}(X^{\mathrm{set}},\mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}})), \quad g \mapsto h_{**}(g) := h_* \circ g. \tag{E.1.2.21}
$$

It is clear that $\psi \circ \psi' = \mathrm{id}$ on $\mathrm{Map}(X^{\mathrm{set}} \times Y^{\mathrm{set}},Z^{\mathrm{set}})$ and $\psi' \circ \psi = \mathrm{id}$ on $\mathrm{Map}(X^{\mathrm{set}},\mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}}))$. To check that $\psi_{X,Y,Z}$ is surjective, it is enough to check the containment

$$\psi'(\mathrm{C}(X \times Y,Z)) \subset \mathrm{C}(X,\mathrm{C}(Y,Z))$$

as subsets of $\mathrm{Map}(X^{\mathrm{set}},\mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}}))$.

In other words, we must check that for any $h : X \times Y \to Z$ continuous with respect to the compactly generated topologies on $X \times Y$ and $Z$, the set-function $\psi'(h) : X^{\mathrm{set}} \to \mathrm{Map}(Y^{\mathrm{set}},Z^{\mathrm{set}})$ takes values in $\mathrm{C}(Y,Z)$ and $\psi'(h)$ is continuous with respect to the compactly generated topology on $X$ and the compact-open topology on $\mathrm{C}(Y,Z)$.

For any $x \in X$, $\psi'(h)(x) = h(x,\cdot) = h \circ i_x$ as a set-function $Y \to Z$ for the visibly continuous $x$-insertion map $i_x : Y \to X \times_0 Y$. Since $Y$ is compactly generated, $i_x$ is also continuous as a map $Y \to X \times Y$ by Lemma E.1.2.1(1). Since $h$ is itself a continuous map $X \times Y \to Z$, the composition $h \circ i_x : Y \to Z$ is continuous, and hence $\psi'(h)(x) \in \mathrm{C}(Y,Z)$. We now check $\psi'(h) : X \to \mathrm{C}(Y,Z)$ is continuous upon endowing $X$ with its intrinsic compactly generated topology and $\mathrm{C}(Y,Z)$ with the compact-open topology. By Lemma E.1.2.10, $h_*$ is continuous as a map

$$k(\mathrm{C}(Y,X \times Y)) \to k(\mathrm{C}(Y,Z)).$$

Upon writing

$$
W_1 := k(\mathrm{C}(Y,X \times Y)), \quad W_2 := k(\mathrm{C}(Y,Z)) \tag{E.1.2.22}
$$

we similarly get

$$
h_{**} : \mathrm{C}(X,W_1) \to \mathrm{C}(X,W_2) \tag{E.1.2.23}
$$

induced by (E.1.2.21) with this map $h_{**}$ also continuous. Provided that $i : X^{\mathrm{set}} \to \mathrm{Map}(Y^{\mathrm{set}},X^{\mathrm{set}} \times Y^{\mathrm{set}})$ is valued in $\mathrm{C}(Y,X \times Y)$ and continuous with respect to the intrinsic topology on $X$ and the compact-open topology on $\mathrm{C}(Y,X \times Y)$, $i$ is also continuous with respect to the intrinsic compactly generated topology on $X$ and the $k$-topology $W_1$ associated to the compact-open topology on $\mathrm{C}(Y,X \times Y)$. Then $\psi'(h) = h_{**}(i)$ is continuous as desired. It is therefore enough to check that $i : X^{\mathrm{set}} \to \mathrm{Map}(Y^{\mathrm{set}},X^{\mathrm{set}} \times Y^{\mathrm{set}})$ is valued in $\mathrm{C}(Y,X \times Y)$ and continuous with respect to the compactly generated topology on $X$ and the compact-open topology on $\mathrm{C}(Y,X \times Y)$.

## PDF page 840

**840** · **CHAPTER E. TOPOLOGICAL STACKS**

The containment $i(X) \subset \mathrm{C}(Y,X \times Y)$ is a consequence of continuity of $i_x$ for every $x \in X$ as discussed above. We now prove that $i : X \to \mathrm{C}(Y,X \times Y)$ is itself continuous. To this end, we let $K$ be a compact Hausdorff space, $a : K \to Y$ a continuous map, and $U \subset X \times Y$ an open subspace, and check that $i^{-1}(N(a,K,U))$ is open in $X$. Since $X$ is compactly generated, it is enough to show that for any compact Hausdorff space $K'$ and continuous map $b : K' \to X$, $b^{-1}(i^{-1}(N(a,K,U)))$ is open in $K'$. We have:

$$
b^{-1}(i^{-1}(N(a,K,U))) = \{t \in K' \mid b(t) \in i^{-1}(N(a,K,U))\} = \{t \in K' \mid \{t\} \times K \subset (b,a)^{-1}(U)\}. \tag{E.1.2.24}
$$

Since $(b,a) : K' \times K \to X \times Y$ is continuous, $W := (b,a)^{-1}(U)$ is open in $K' \times K$. We caution the reader that in this last assertion the product $X \times Y$ is the one for $\mathbf{CG}$. However, as $K' \times_0 K$ is compact Hausdorff, it is compactly generated by Lemma E.1.1.3(4), and hence $K' \times K = K' \times_0 K$. We now apply [SP, Tag 005M] to $A := \{t\}$ for $t \in b^{-1}(i^{-1}(N(a,K,U)))$ and $B := K$ to get an open $V \subset K'$ containing $t$ such that $V \times_0 K \subset W$. This means that $V$ is contained in $(i \circ b)^{-1}(N(a,K,U))$. We have found an open neighborhood $V$ of $t \in (i \circ b)^{-1}(N(a,K,U))$ entirely contained in $(i \circ b)^{-1}(N(a,K,U))$. As $t$ is arbitrary, we deduce that $(i \circ b)^{-1}(N(a,K,U))$ is open in $K'$, as desired. This proves continuity of $i$, which is what we needed to show to prove continuity of $\psi'(h) = h_{**}(i)$.

We have built the desired set-theoretic bijection

$$
\psi_{X,Y,Z} : \mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,Z)) \to \mathscr{C}ont_k(X \times Y,Z) \tag{E.1.2.25}
$$

between objects in $\mathbf{CG}$ and it remains to show this bijection or its inverse

$$\psi'_{X,Y,Z} : \mathscr{C}ont_k(X \times Y,Z) \to \mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,Z))$$

is a homeomorphism. It suffices to show this inverse map is continuous, since then applying $\mathrm{C}(T,\cdot)$ makes sense for any compactly generated $T$ and yields the set-map $\psi'_{T \times X,Y,Z}$ that we know a bijection (so by Yoneda's Lemma, the map $\psi'_{X,Y,Z}$ in $\mathbf{CG}$ is an isomorphism).

We proved in the discussion after (E.1.2.10) that the evaluation morphism from (E.1.2.9) induces a continuous map

$$
\mathrm{ev}_{Y,Z} : \mathscr{C}ont_k(Y,Z) \times Y \to Z. \tag{E.1.2.26}
$$

for $Y, Z$ compactly generated. Retaining the notation from (E.1.2.22), for a continuous $h : X \times Y \to Z$ we have a continuous map $h_{**} : \mathscr{C}ont_k(X,W_1) \to \mathscr{C}ont_k(X,W_2)$ from (E.1.2.23) and for $W'_1 := \mathscr{C}ont_k(X,W_1)$ and $W'_2 := \mathscr{C}ont_k(X,W_2) = \mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,Z))$ and can write $\psi'(h) = \mathrm{ev}_{W'_1,W'_2}(h_{**},i)$ exhibiting the point $\psi'(h) \in W'_2$ as a continuous function of $h_{**}$ (since $i \in \mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,X \times Y)) = W'_1$).

More precisely, $\psi'_{X,Y,Z}$ is the composition of three set-maps

$$
\mathscr{C}ont_k(X \times Y,Z) \to \mathscr{C}ont_k(W_1,W_2) \to \mathscr{C}ont_k(W'_1,W'_2) \to W'_2 = \mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,Z)) \tag{E.1.2.27}
$$

where the first two steps are respectively $h \mapsto \mathscr{C}ont_k(Y,h) = h_*$ and $f \mapsto \mathscr{C}ont_k(X,f)$ and the last step is the continuous $\mathrm{ev}_{W'_1,W'_2}(\cdot,i)$ (with $i \in W'_1$). Thus, for continuity of $\psi'_{X,Y,Z}$ it suffices to show for all compactly generated $X_1, X_2, X_2$ that

$$
\mathscr{C}ont_k(X_2,X_3) \to \mathscr{C}ont_k(\mathscr{C}ont_k(X_1,X_2),\mathscr{C}ont_k(X_1,X_3)) \tag{E.1.2.28}
$$

defined by $g \mapsto g_* := \mathscr{C}ont_k(X_1,g)$ makes sense (i.e., $g_*$ is continuous) and is continuous, since the first step in (E.1.2.27) is recovered by using $X_1 = Y$, $X_2 = X \times Y$, $X_3 = Z$ and the second step in (E.1.2.27) is recovered by using $X_1 = X$, $X_2 = W_1$, $X_3 = X_2$. For continuity of $g_*$, so (E.1.2.28) makes sense, by functoriality of $k(\cdot)$ it suffices to show $\mathrm{C}(X_1,X_2) \to \mathrm{C}(X_1,X_3)$ is continuous for the compact-open topologies; this holds because $g^{-1}_*(N(a,K,U)) = N(a,K,g^{-1}(U))$. $^3$ $\square$

$^3$The continuity of (E.1.2.28) requires explanation, and was not justified before: all that was said was “a similar argument” to the continuity of $\psi'(h)$ in $h_{**}$ works, but that is too breezy.

## PDF page 841

**E.1. COMPACTLY GENERATED SPACES** · **841**

We recall, as a consequence of [MacL, Ch. III, §1, Prop. 5], that the internal product in $\mathbf{CG}$, alongside the final object of $\mathbf{CG}$ (a point endowed with the discrete topology), determine a canonical (cartesian) symmetric monoidal structure on $\mathbf{CG}$, whose structure morphisms are provided by the cited Proposition. We refer to it via the succint notation $(\mathbf{CG}, \times, *)$, where $*$ denotes the final object of $\mathbf{CG}$, expecting no confusion to arise.

**Proposition E.1.2.13.** *The bifunctor:*

$$
\mathscr{C}ont_k : \mathbf{CG}^{\mathrm{opp}} \times \mathbf{CG} \to \mathbf{CG}
$$

*endows the symmetric monoidal category $(\mathbf{CG}, \times, *)$ with the structure of a cartesian closed symmetric monoidal category enriched over itself.*

The Proposition is proved in [Str, Prop. 2.12], resting on [Str, Prop. 2.11] which is in turn a consequence of the Tube Lemma (recalled in [Str, Lemma 2.5]) that was used in the proof of Lemma E.1.2.12 (for the continuity of $i$).

*Proof.* By Lemma E.1.2.12 there exists a natural homeomorphism

$$\theta_{X,Y,Z} : \mathscr{C}ont_k(X \times Y,Z) \to \mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,Z)).$$

By the very definition of closed monoidal category (see [MacL, Ch. VII, §1] and [EK, Ch. III]), the cartesian (symmetric) monoidal structure $(\times,*)$ uniquely determined on $\mathbf{CG}$ by [MacL, Ch. III, §1, Prop. 5] is therefore closed, the internal-Hom bifunctor being given by $\mathscr{C}ont_k(\cdot,\cdot)$. $\square$

As a direct application of Proposition E.1.2.13, we now prove that products in $\mathbf{CG}$ of submersive maps are submersive. We begin with a characterization of submersive maps in $\mathbf{CG}$, and further refer the reader to [LGL, §5, Lemma 5.7] and its proof:

**Lemma E.1.2.14.** *Let $X, Y$ be compactly generated spaces, and $f : X \to Y$ a continuous map. The following conditions are equivalent:*

(1) *There exists a compactly generated space $R$, two maps $s, t : R \rightrightarrows X$, and a homeomorphism $c : \mathrm{coeq}(s,t) \to Y$, such that the canonical map $p : X \to \mathrm{coeq}(s,t)$ satisfies $c \circ p = f$.*

(2) *$f$ is the co-equalizer in $\mathbf{CG}$ of the diagram $p_1, p_2 : X \times_{f,Y,f} X \rightrightarrows X$, where $p_1, p_2$ are the two projections.*

(3) *$f$ is a submersive map.*

*Proof.* We have (1) $\Rightarrow$ (3) since $p$ is submersive in (1). We now assume that (3) holds, and prove that (2) holds. We choose $R := X \times_{f,X,f} X$, with the two maps to $X$ defined to be the two projections $p_1, p_2 : R \rightrightarrows X$. We check that if $f$ is submersive then $f : X \to Y$ is the co-equalizer of $p_1, p_2$ in $\mathbf{CG}$. By Lemma E.1.2.2(2), we may compute the co-equalizer of the two projections $p_1, p_2$ in $\mathbf{Spaces}$. We call $X' := u_{\mathrm{cg}}(X)$ and $Y' = u_{\mathrm{cg}}(Y)$, and retain the notation $f$ for the continuous map $u_{\mathrm{cg}}(f)$, and $R'$ the topological fibre product $R' := (f,f)^{-1}(\Delta_X(X))$. Its topology is the subspace topology of the product topology on $X \times_0 X$. We denote the two projections by $p'_1, p'_2 : R' \rightrightarrows X'$. The quotient $X'/R'$ is the topological co-equalizer of $p'_1, p'_2$. Part (2) of Lemma E.1.2.2 implies that we have $X'/R' = k(X'/R') = \mathrm{coeq}(p_1,p_2)$, where $p_1 := k(p'_1)$ and $p_2 := k(p'_2)$. This latter co-equalizer is the co-equalizer in $\mathbf{CG}$. The evident map $c' : X'/R' \to Y'$ is a homeomorphism by design of $R'$ since $f$ is submersive. Since $X \times_{f,Y,f} X = k(X' \times^0_{f,Y',f} X') = k(R')$ by Lemma E.1.2.2(1), then $c := k(c')$ is a homeomorphism $\mathrm{coeq}(p_1,p_2) \to Y$ such that $c \circ k(\varphi) = f$ for the natural map $\varphi : X' \to X'/R'$, and so (2) is proved. If (2) holds, then we may set $R := X \times_{f,Y,f} X$, and $(s,t) = (p_1,p_2)$, with $p_1, p_2 : R \rightrightarrows X$ the two projections, to deduce that (1) holds. $\square$

**Remark E.1.2.15.** We have shown in Lemma E.1.2.14 that submersive maps are exactly the regular epimorphisms in $\mathbf{CG}$, and the effective epimorphisms in $\mathbf{CG}$. We caution the reader that, despite the Lemma, $\mathbf{CG}$ is not a regular category. We refer the reader to [Bor2, Ch. 2] for the foundational material on regular categories, and specifically for [Bor2, Ch. 2, Def. 2.1.1]. Stability of regular epimorphisms under arbitrary

## PDF page 842

**842** · **CHAPTER E. TOPOLOGICAL STACKS**

pull-backs is a defining requirement of regularity. For regularity to hold for $\mathbf{CG}$, regular epimorphisms should therefore be stable under arbitrary base change internally in $\mathbf{CG}$. This does not hold, as Example E.1.2.16 below shows. To obtain a *regular* large category of topological spaces we will be incorporating a separation condition on objects in the next section, §E.2. Nonetheless, Lemma E.1.2.17 on preservation of submersiveness under direct products in $\mathbf{CG}$ holds with no separation conditions (see also [LGL, §5, Prop. 5.8]).

The following example is [Bor2, Counterexample 2.4.5], as a counterexample to regularity for the category $\mathbf{Spaces}$. It can be adapted as below to serve the same purpose for $\mathbf{CG}$:

**Example E.1.2.16.** Let $X := \{1,2,3,4\}$ endowed with the topology $\tau_X := \{\varnothing,\{1,2\},X\}$, $Y := \{a,b,c\}$ endowed with the topology $\tau_Y := \{\varnothing,Y\}$, and $Z := \{\alpha,\beta,\gamma\}$ endowed with the topology $\tau_Z := \{\varnothing,\{\alpha,\beta\},Z\}$. We define $f : X \to Y$ to be $f(1) = a$, $f(2) = b = f(3)$, $f(4) = c$, and $g : Z \to Y$ to be $g(\alpha) = a$, $g(\beta) = c = g(\gamma)$. We have $P := X \times^0_{f,Y,g} Z = \{(1,\alpha),(4,\beta),(4,\gamma)\}$ endowed with the topology $\tau := \{\varnothing,\{(1,\alpha)\},\{(1,\alpha),(4,\beta)\},P\}$. The map $f$ is submersive, whereas the first projection $f_Z : P \to Z$ is not, since $f_Z^{-1}(\{\alpha\}) = \{(1,\alpha)\}$ is open, while $\{\alpha\}$ is not. Since $X, Y, Z$ and $P$ are finite topological spaces, they are all compactly generated (for example by [Str, Prop. 1.6], and the topological fibre product $P$ is therefore a fibre product in $\mathbf{CG}$ by Lemma E.1.2.2(1). This is an example of a submersive map in $\mathbf{CG}$ which is not stable under arbitrary base change internally in $\mathbf{CG}$.

Here is the promised result on stability of submersive maps under products in $\mathbf{CG}$:

**Lemma E.1.2.17.** *Let $X, Y, X', Y'$ be compactly generated spaces, and $f : X \to X'$, $g : Y \to Y'$ submersive maps. Then:*

$$(f,g) : X \times Y \to X' \times Y'$$

*is a submersive map.*

*Proof.* We may factor $(f,g)$ as $(f,\mathrm{id}) : X \times Y \to X' \times Y$, followed by $(\mathrm{id},g) : X' \times Y \to X' \times Y'$. It is therefore enough to treat the case $Y = Y'$ and $g = \mathrm{id}$. By Lemma E.1.2.14, $X'$ is the co-equalizer of the two projections $X \times_{f,X',f} X \rightrightarrows X$ in $\mathbf{CG}$. Lemma E.1.2.12 implies that the product functor $(\cdot) \times Y$ is a left-adjoint, and hence commutes with representable colimits. As co-equalizers are small colimits, all representable by Lemma E.1.2.2(2), we conclude. $\square$

The above Lemma E.1.2.17 does not hold in $\mathbf{Spaces}$, as the following example shows. The existence of examples in $\mathbf{Spaces}$ such as Example E.1.2.18 is one of the reasons why we shall be relying on the category of compactly generated spaces (and its variant incorporating a weak Hausdorff condition on objects, to be discussed in §E.2) to select better categories of topological spaces to serve as a small site.

**Example E.1.2.18.** We let $X := \mathbf{Q}$ be endowed with the subspace topology inherited from the Euclidean topology on $\mathbf{R}$, and we let $X'$ be the quotient of $X$ obtained by identifying the subset of integers $\mathbf{Z} \subset \mathbf{Q}$ to $\{0\}$. The continuous map $f : X \to X'$ is submersive by construction. On the other hand, the map $(f,\mathrm{id}) : X \times_0 X \to X' \times_0 X$ of topological products is not submersive (see [Br4, Ch. 4, Example 4] for a proof of this assertion).

**E.1.2.1. *Examples and permanence properties of compactly generated spaces.*** Building on the previous section and especially on Lemma E.1.2.1, Lemma E.1.2.2, Lemma E.1.2.10 and Proposition E.1.2.13, we collect here results that exhibit familiar classes of topological spaces to be compactly generated, and will establish when formation of products and, on occasion, passage to subspaces, preserves compact generation by preserving some stronger property of topological spaces. In particular, we will collect sufficient conditions for constructions in $\mathbf{CG}$ to be computable in $\mathbf{Spaces}$, for special classes of compactly generated spaces. This includes all topological spaces of interest for using this appendix to study periodic orbits in our main work.

## PDF page 843

**E.1. COMPACTLY GENERATED SPACES** · **843**

**Proposition E.1.2.19.** *We have:*

(1) *all locally compact Hausdorff spaces are compactly generated,*

(2) *the product in $\mathbf{Spaces}$ of a compactly generated space and a locally compact Hausdorff space is compactly generated (so it computes the product in $\mathbf{CG}$).*

We refer the reader to [Str, Prop. 2.6].

*Proof.* We call $I$ the set of all compact Hausdorff subspaces of $X$, and for $i \in I$ let $K_i$ be the compact Hausdorff subspace $i \subset X$. Since $X$ is locally compact Hausdorff, the interiors of the $K_i$ cover $X$. Upon calling $g_i : K_i \to X$ the immersion, we have $g_i^{-1}(Z) = Z \cap K_i$ for every subspace $Z \subset X$. It follows from the local nature of closedness that a subspace $Z$ such that $g_i^{-1}(Z)$ is closed in $K_i$ for every $i \in I$ is itself closed in $X$. We now consider the continuous map:

$$
q := \coprod_{i \in I} g_i : \coprod_{i \in I} K_i \to X \tag{E.1.2.29}
$$

We have shown that every subspace $Z$ of $X$ such that $q^{-1}(Z)$ is closed in $\coprod_{i \in I} K_i$, is closed in $X$. This proves (1). To prove (2), we use a related method along with Lemma E.1.1.3(3) to reduce to checking the product against a compact Hausdorff space is compactly generated.$^4$ Hence, (E.1.2.29) is submersive and so $X$ is compactly generated. $\square$

**Remark E.1.2.20.** On the above Lemma E.1.2.19, we observe that the Hausdorff assumption in both part (1) and part (2) of the Lemma cannot be dropped altogether. We refer the reader to Lemma E.2.4.9, for a counter-example, given by the one-point compactification of the rationals endowed with their subspace topology inherited from the Euclidean topology on $\mathbf{R}$. We refer the reader to [StSe, Part II, 35]. This is an example of a compact topological space (in fact, even weakly Hausdorff, as will be discussed in Lemma E.2.4.9; we refer the reader to Definition E.2.1.1 for the weak Hausdorff separation condition and to §E.2 for the related material) such that its compact topological self-product is not compactly generated.

Another class of topological spaces that can be seen to be compactly generated, is that of sequential spaces. We recall that a topological space $X$ is *sequential* if and only if any sequentially closed subset $Z \subset X$ (i.e. such that for any sequence $\{z_n\}_{n \ge 0} \subset Z$ converging to a point $x \in X$, we have $x \in Z$) is closed in $Z$ (see [Fr, Prop. 1.1] and the definition on [Fr, §1, p. 109] before [Fr, Prop. 1.2]). Examples of sequential spaces are all topological spaces satisfying the first axiom of countability. In fact, any sequential space receives a submersive map from a first-countable topological space (see [Fr, Cor. 1.14]).

We have the following:

**Proposition E.1.2.21.** *We have:*

(1) *all sequential topological spaces are compactly generated,*

(2) *the product in $\mathbf{Spaces}$ of two first-countable topological spaces is compactly generated and computes the product in $\mathbf{CG}$.*

*Proof.* We prove (1). We let $X$ be a sequential space, and $Z \subset X$ a $k$-closed subset. We are to show that $Z$ is sequentially closed, hence closed, in $X$. Let $\{z_n\}_{n \ge 0} \subset Z$ be a sequence converging to a point $x \in X$. We endow $\mathbf{N}$ with the discrete topology, and call $K$ the one-point compactification of $\mathbf{N}$. This $K$ is compact Hausdorff, and we may define the set-function $g : K \to X$ by assigning $g(n) := z_n$ for all integers $n \ge 0$, and $g(\infty) := x$. Since the sequence $\{z_n\}_{n \ge 0}$ is convergent to $x$, $g$ is continuous. It follows that $g^{-1}(Z)$ is closed in $K$. Since $\{z_n\}_{\ge 0}$ is contained in $Z$, we deduce the containment $\mathbf{N} \subset g^{-1}(Z)$. As $\mathbf{N} \subset K$ is dense and $g^{-1}(Z)$ is closed in $K$, we deduce that we have $K = g^{-1}(Z)$, and hence $\infty \in g^{-1}(Z)$. It follows $x \in Z$, and $Z$ is sequentially closed, hence closed in $X$. By part (3) of Lemma E.1.1.3, $X$ is compactly generated, proving (1).

$^4$The compact generatedness has to be justified; was not explained.

## PDF page 844

**844** · **CHAPTER E. TOPOLOGICAL STACKS**

Part (2) follows from the fact that, for first-countable spaces $X, Y$, and any $(x,y) \in X \times_0 Y$, the set of open subspaces $U \times_0 V$ as $U$ ranges over the elements of a countable base at $x$, and $V$ ranges over the elements of a countable local base at $y$, is a countable base at $(x,y)$, therefore proving that $X \times_0 Y$ is first-countable. As first-countable topological spaces are sequential (see part (2) of [Fr, Cor. 1.14]), part (1) applies and implies that $X \times_0 Y$ is compactly generated. It follows that we have $k(X \times_0 Y) = X \times_0 Y$, and hence $X \times_0 Y$ computes in $\mathbf{Spaces}$ the product $X \times Y$ in $\mathbf{CG}$ by part (1) of Lemma E.1.2.2. $\square$

**Remark E.1.2.22.** Another way to see that a sequential space $X$ is compactly generated is to directly exhibit a submersive map from a locally compact Hausdorff space. To do this, we consider the set $I$ of all convergent sequences in $X$. For $i \in I$, we denote by $\mathbf{x}(i)$ the associated sequence $\mathbf{x}(i) = \{x_n(i), n \ge 0\} \subset X$. We call $K$ the one-point compactification of $\mathbf{N}$ (with $\mathbf{N}$ endowed with the discrete topology), we define $K_i := K$ for every $i \in I$, and we define:

$$q : \coprod_{i \in I} K_i \to X$$

by sending any non-negative integer $n \in K_i$ to $x_n(i)$ and $\infty \in K_i$ to a choice of limit $\lim_{n \to \infty} x_n(i)$ in $X$. As every point of $X$ is the limit of a constant sequence in $X$, $q$ is surjective. The argument at the beginning of the proof of Proposition E.1.2.21 shows that a subspace $Z \subset X$ is closed if and only if $q^{-1}(Z)$ is, and hence $q$ is submersive.

**Remark E.1.2.23.** We note that the topological product of two sequential spaces may not be sequential. We refer the reader to Example E.1.2.24 below for an example. Another example exhibiting this phenomenon can be found in [ABM, §2] (see, specifically, [ABM, §2, Property IV]). This is the reason for the stronger assumption in part (2) of Proposition E.1.2.21.

**Example E.1.2.24.** As in Example E.1.2.18, we let $X := \mathbf{Q}$ be endowed with the subspace topology inherited from the Euclidean topology on $\mathbf{R}$, and we let $X'$ be the quotient of $X$ obtained by identifying the subset of all integers $\mathbf{Z} \subset \mathbf{Q}$ to $\{0\}$. The product space $X' \times_0 X$ is an example of:

(1) a product of compactly generated spaces which is not compactly generated,

(2) a product of sequential spaces which is not sequential (see [Fr, §1, p. 109] before [Fr, Prop. 1.2]).

Indeed, we note that $X \times_0 X$ is compactly generated by Lemma E.1.2.21. Moreover, Lemma E.1.2.17 implies that $X' \times_0 X$ is not compactly generated: if it were then the topological product map $(f,\mathrm{id})$ would be submersive by the Lemma, contradicting Example E.1.2.18.

We prove the following basic permanence properties for the condition of compact generation for topological spaces.

**Lemma E.1.2.25.** *Let $X$ be a compactly generated topological space, and $T \subset X$ be a subspace. Assume that one of the following conditions holds:*

(1) *$T$ is closed in $X$ with respect to the subspace topology.*

(2) *$T$ is open in $X$ with respect to the subspace topology.*

(3) *$T$ is locally closed in $X$ with respect to the subspace topology.*

*Then $T$ is compactly generated.*

The Lemma is also proved in [Str, Lemma 2.26].

*Proof.* By Lemma E.1.1.3, there exists a set $I$, compact Hausdorff topological spaces $K_i$ for every $i \in I$, and a submersive map:

$$q : \coprod_{i \in I} K_i \to X.$$

## PDF page 845

**E.1. COMPACTLY GENERATED SPACES** · **845**

If $T$ is closed, then $q' : q^{-1}(T) \to T$ is a submersive map. As $q^{-1}(T)$ is a closed subspace of $\coprod_{i \in I} K_i$, it is of the form $\coprod_{i \in I} C_i$ for closed subspaces $C_i \subseteq K_i$. As each $K_i$ is compact Hausdorff, so is each $C_i$, so $T$ is compactly generated, proving (1). If $T$ is open in $X$, then $q' : q^{-1}(U) \to U$ is also a submersive map and since $q^{-1}(U) \subseteq \coprod_{i \in I} K_i$ is open, it is locally compact Hausdorff. As every locally compact Hausdorff topological space is compactly generated by Proposition E.1.2.19, proving part (2) is now accomplished as follows. As $q^{-1}(U)$ is compactly generated, we may find, by part (4) in Lemma E.1.1.3, a set $I$, for every $i \in I$, a compact Hausdorff space $K'_i$, and a submersive map $p : \coprod_{i \in I} K'_i \to q^{-1}(U)$. Since $q' \circ p$ is submersive for $q' = q|_{q^{-1}(U)} : q^{-1}(U) \to U$, Lemma E.1.1.3 implies that $U$ is compactly generated, as desired. Part (3) follows by combining (1) and (2). $\square$

We complement the above result with a stability result for closed immersions under products, which we can now prove upon combining Lemma E.1.2.17 and the above Lemma E.1.2.25:

**Lemma E.1.2.26.** *Let $X, Y, X', Y'$ be compactly generated spaces, and $f : X \to X'$, $g : Y \to Y'$ closed immersions. Then:*

$$(f,g) : X \times Y \to X' \times Y'$$

*is a closed immersion.*

*Proof.* We may factor $(f,g)$ as $(f,\mathrm{id}) : X \times Y \to X' \times Y$, followed by $(\mathrm{id},g) : X' \times Y \to X' \times Y'$. It is therefore enough to treat the case $Y = Y'$ and $g = \mathrm{id}$. Thus, we are reduced to the case $f$ is the inclusion of a closed subspace of $X'$. The subspace $X \times_0 Y \subset X' \times_0 Y$ is closed with respect to the subspace topology. By part (2) of Remark E.1.1.8, $X \times_0 Y$ is closed with respect to the subspace topology of the $k$-topology on $k(X' \times_0 Y) = X' \times Y$ as well, and by part (2) of Lemma E.1.2.25, $X \times_0 Y$ is compactly generated and hence computes $X \times Y$, exhibiting $X \times Y$ as a closed subspace of $X' \times Y$, as desired. $\square$

Here is a criterion to detect immersions of compactly generated spaces, for later use:

**Lemma E.1.2.27.** *Let $X, Y$ be compactly generated topological spaces, and $f : X \to Y$ a continuous injective map. The following are equivalent:*

(1) *$f$ is an immersion.*

(2) *For any compactly generated topological space $T$ and any set-function $g : T \to X$, $g$ is continuous if and only if the composition $f \circ g$ is continuous.*

*Proof.* That (1) $\Rightarrow$ (2) is obvious. Conversely, suppose for all continuous $g : T \to X$ that $f \circ g$ is continuous. We will deduce (1). Let $i : X \to f(X)$ be the continuous bijective map induced by $f$, with $f(X)$ being endowed with the subspace topology from the topology of $Y$. We call $i' : f(X) \to Y$ the immersion, and we have $i' \circ i = f$ and $f \circ i^{-1} = i'$. By the foregoing (especially (2)), both $i$ and $i^{-1}$ are continuous. Hence $f$ is an immersion. $\square$

As an application of Lemma E.1.2.27, we conclude this subsection by determining when the continuous push-forward between function spaces along an immersion is an immersion.

**Lemma E.1.2.28.** *Let $X, Y$ be compactly generated spaces, $i : Z \to Y$ an immersion. Then the induced map*

$$i_* : \mathscr{C}ont_k(X,Z) \to \mathscr{C}ont_k(X,Y)$$

*is an immersion. If $i$ is a closed immersion then $i_*$ is a closed immersion.*

*Proof.* Let $g : T \to \mathscr{C}ont_k(X,Z)$ be an arbitrary set-function from a compactly generated topological space $T$ such that $i_* \circ g$ is continuous. By Lemma E.1.2.12, the associated set-map $h : T \times X \to Y$ is continuous, and the associated set-map corresponding to $g$ satisfies $i \circ h' = h$. As $i$ is an immersion, $g$ is continuous. By Lemma E.1.2.27, we deduce that $i_*$ is an immersion.

## PDF page 846

**846** · **CHAPTER E. TOPOLOGICAL STACKS**

We now assume that $i$ is a closed immersion. We may assume $Z=i(Z)$. We now observe that in this case we have:

$$
\mathscr{C}ont_k(X,Z)=\bigcap_{x\in X}(\mathscr{C}ont_k(X,Y)-N(i_x,\{x\},Y-Z))
$$

with $i_x:\{x\}\to X$ the inclusion in $X$ of the point $x$, which is an infinite intersection of closed subspaces, hence closed in $\mathscr{C}ont_k(X,Y)$. As the image of $i_*$ is, therefore, closed, $i_*$ is a closed immersion. $\square$

E.2. Compactly generated weakly Hausdorff spaces

In this section we introduce a weakening of the Hausdorff separation condition, and discuss its effects on compactly generated spaces. Specifically, we shall establish improved closure properties for the resulting full subcategory of CG. Sources for this section are [LGL, §3], [McC, §2], [Rezk, §4] and [Str, §1].

E.2.1. Preparations on compactly generated weakly Hausdorff spaces. We begin with a definition, introducing the weak Hausdorff separation condition:

Definition E.2.1.1. A topological space $X$ is weakly Hausdorff if and only if for every compact Hausdorff topological space $K$ and continuous map $f:K\to X$, $f(K)$ is a closed subspace of $X$.

Remark E.2.1.2. Clearly subspaces of weakly Hausdorff spaces are weakly Hausdorff.

Remark E.2.1.3. We recall that if $X$ is Hausdorff then any compact subspace is closed. In particular, Hausdorff spaces are weakly Hausdorff. For an example of a weakly Hausdorff (compact) topological space that is not Hausdorff, we refer the reader to Lemma E.2.4.9.

Lemma E.2.1.4. *Let $K$ be a compact weakly Hausdorff topological space. Assume that there exists a compact Hausdorff topological space $K'$ and a surjective continuous map $q:K'\to K$. Then $K$ is Hausdorff.*

Proof. Since $K$ is weakly Hausdorff, every point of $K$ is closed and so $q$ has compact fibers over $K$. Indeed, for every $x\in K$, $q^{-1}(\{x\})$ is closed in $K'$, and this latter is a compact Hausdorff topological space. It follows $q^{-1}(\{x\})$ is compact. It is moreover Hausdorff. For any $C\subset K'$ closed, $C$ is compact Hausdorff in $K'$ and so $q(C)$ is compact in $K$, and closed since $K$ is weakly Hausdorff by assumption. We deduce that $q$ is a closed map, and so $q$ is submersive. Let $x,x'\in K$ be distinct points. Since $K$ is weakly Hausdorff, its points are closed. As $K'$ is normal and $q^{-1}(\{x\})$ and $q^{-1}(\{x'\})$ are closed, there exist disjoint open subspaces $U,U'\subset K'$ such that $q^{-1}(\{x\})\subset U$ and $q^{-1}(\{x'\})\subset U'$. The subspaces of $K'$ given by $K'-U$ and $K'-U'$ are closed, and as $q$ is a closed map, then $C:=q(K'-U)$ and $C':=q(K'-U')$ are closed. It follows that $K-C$ and $K-C'$ are disjoint open subspaces of $K$ containing $x$ and $x'$ respectively. We deduce that $K$ is Hausdorff. $\square$

Lemma E.2.1.5. *If $X$ is a weakly Hausdorff topological space then so is $k(X)$.*

Proof. Let $K$ be a compact Hausdorff topological space, and $g':K\to k(X)$ a continuous map. Compose with the continuous bijection $k(X)\to K$ to define a continuous $g:K\to X$. Since $X$ is weakly Hausdorff, $g(K)$ is closed in $X$. By continuity of $k(X)\to X$, it follows that $g'(K)$ is closed in $k(X)$. We deduce $k(X)$ is weakly Hausdorff. $\square$

Lemma E.2.1.6. *Let $X$ be a topological space. We consider the following conditions:*

(1) $X$ is weakly Hausdorff,

(2) *the image $\Delta\subset X\times_0 X$ of the diagonal morphism $\Delta_X:X\to X\times_0 X$, is $k$-closed,*

(3) *for every compact Hausdorff space $K$ and every continuous map $g:K\to X$, the topological fibre product $K\times^0_{g,X,g}K$ is closed in $K\times_0 K$.*

*Then (1) $\Rightarrow$ (2) and (2) $\Leftrightarrow$ (3). Moreover, if $X$ is compactly generated then (1) $\Leftrightarrow$ (2).*

## PDF page 847

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **847**

We refer the reader to [Str, Prop. 2.14] and to [Rezk, Prop. 4.2]. We further refer the reader to Lemma E.2.4.9, exhibiting an example of a weakly Hausdorff and compactly generated space $X$ whose topological diagonal subspace is not closed.

Proof. Suppose $X$ is weakly Hausdorff. For any compact Hausdorff topological space $K$ and continuous map $g:K\to X\times_0 X$, we call $g_1,g_2:K\rightrightarrows X$ the composition of $g$ with the first and second projection, respectively. We claim that

$$
g^{-1}(\Delta)=\{x\in K\mid g_1(x)=g_2(x)\}
\tag{E.2.1.1}
$$

is closed.

As $g_1(K)$ and $g_2(K)$ are compact subspaces in $X$, since $X$ is weakly Hausdorff their union $C:=g_1(K)\cup g_2(K)$ is therefore closed in $X$, and $g(K)$ is contained in $C\times_0 C\subset X\times_0 X$. We call $D$ the image of the topological diagonal $\Delta_C:C\to C\times_0 C$. Clearly

$$
g^{-1}(D)=g^{-1}(\Delta)
\tag{E.2.1.2}
$$

as subspaces of $K$. Since $K\coprod K$ is compact and Hausdorff, defining $h:K\coprod K\to C$ to be $g_1$ on the first copy of $K$ and $g_2$ on the second makes $h$ a continuous surjection from a compact Hausdorff space. By Lemma E.2.1.4, $C$ is compact Hausdorff. Thus, $D$ is a closed subspace of $C$, so by (E.2.1.2) the subspace $g^{-1}(\Delta)$ of $K$ from (E.2.1.1) is a closed subspace of $K$ since $g$ is continuous. This proves the claim, which in turn proves that $\Delta$ is $k$-closed in $X\times_0 X$, establishing (2) from (1).

We now assume that (2) holds, and prove (3). Let $K$ be a compact Hausdorff space, $g:K\to X$ a continuous map. Then we have:

$$
K\times^0_{g,X,g}K=(g,g)^{-1}(\Delta)\subset K\times_0 K
\tag{E.2.1.3}
$$

as subspaces of $K\times_0 K$. Since $\Delta$ is $k$-closed in $X\times_0 X$ and $(g,g):K\times_0 K\to X\times_0 X$ is continuous with $K\times_0 K$ compact Hausdorff (hence its topology is its $k$-topology), we see $(g,g)^{-1}(\Delta)$ is closed, which proves (3).

We now assume (3) and prove that (2) holds. Let $K$ be a compact Hausdorff space and $g:K\to X\times_0 X$ a continuous map. Upon denoting $g_1$ and $g_2$ the compositions of $g$ with the first, respectively the second, projections $p_1,p_2:X\times_0 X\rightrightarrows X$, the map $g$ factors as a composition of the continuous maps $\Delta_K:K\to K\times_0 K$, and $(g_1,g_2):K\times_0 K\to X\times_0 X$. We need to show that $(g_1,g_2)^{-1}(\Delta)$ is a closed subspace of $K\times_0 K$. Let $K':=K\coprod K$ and define $h:K'\to X$ to be $g_1$ on the first copy of $K$, and $g_2$ on the second copy of $K$. Clearly $K'$ is compact and Hausdorff. Then by (3) we have $K'\times^0_{h,X,h}K'$ is closed in $K'\times_0 K'$. Clearly $K\times^0_{g_1,X,g_2}K$ splits off as an open and closed subspace of $K'\times^0_{h,X,h}K'$, and as such recovers its natural embedding into $K\times_0 K$ as an open and closed subspace of $K'\times_0 K'$. We conclude that $K\times^0_{g_1,X,g_2}K$ is closed in $K\times_0 K$.

We have:

$$
(g_1,g_2)^{-1}(\Delta)=K\times^0_{g_1,X,g_2}K
$$

as subspaces of $K\times_0 K$, and so indeed $(g_1,g_2)^{-1}(\Delta)$ is closed in $K\times_0 K$.

It remains to check that (2) implies (1) when $X$ is compactly generated. Suppose $K$ is a compact Hausdorff space and $g:K\to X$ a continuous map. Then for any compact Hausdorff space $K'$ and $g':K'\to X$ any continuous map,

$$
(g')^{-1}(g(K))=p_2((g,g')^{-1}(\Delta))
$$

as subspaces of $K'$ where $p_2:K\times_0 K'\to K'$ is the second projection. As $\Delta$ is $k$-closed by (2), $(g,g')^{-1}(\Delta)\subset K\times_0 K'$ is closed, and its image in $K'$ under $p_2$ is closed, as $p_2$ is a closed map by [SP, Tag 005P]. This proves that $g(K)$ is $k$-closed in $X$. As $X$ is compactly generated, $g(K)$ is closed by Remark E.1.1.8. $\square$

Remark E.2.1.7. We note that part (2) of Lemma E.2.1.6 suggests a weakening of the notion of weakly Hausdorff space. Spaces whose diagonal subspace is $k$-closed are called $k$-Hausdorff. Weakly Hausdorff and $k$-Hausdorff are not equivalent concepts (see Example E.2.1.10). However, they are for compactly generated

## PDF page 848

**848** · **CHAPTER E. TOPOLOGICAL STACKS**

spaces, which is the content of the last assertion in Lemma E.2.1.6. We refer the reader to [Rezk, §4] for background material on $k$-Hausdorff spaces and how it relates to compactly generated weakly Hausdorff spaces. Throughout this appendix, we limit ourselves to the weak Hausdorff property, as it is equivalent to the correct separation condition to impose on compactly generated spaces (namely, the $k$-Hausdorff separation condition) to obtain the desired improvements to the category $\mathbf{CG}$, and because it can be directly compared to other separation axioms. It is stronger than $T_1$ (see Example E.2.1.8) and weaker than $T_2$ (see Example E.2.1.9 below, which can be arranged to be compactly generated: see Lemma E.2.4.5). As a separation axiom, it is sometimes referred to as $t_2$.

Example E.2.1.8. Let $X$ be an infinite set endowed with the co-finite topology. Then $X$ is $T_1$, but not weakly Hausdorff (it violates Lemma E.2.1.6(2)).

Example E.2.1.9. Let $Y$ be any Hausdorff space that is not locally compact. Then the one-point compactification $X:=Y^+$ is an example of a weakly Hausdorff topological space that is not Hausdorff. Examples are [StSe, Part II, 35], which is also Example E.2.4.4, or a product of an uncountable number of copies of $\mathbf R$, respectively of $[0,1]$. Another example is [StSe, Part II, 99].

Example E.2.1.10. We let $X$ be the one-point compactification of the Arens-Fort space (see [StSe, Part II, 26]). Then $X$ is not weakly Hausdorff. Indeed, we let $(0,0)$ be the origin in the Arens-Fort space, the unique non-isolated point in the Arens-Fort space. Then $X-\{(0,0)\}$ is homeomorphic to the one-point compactification of a discrete space (see [StSe, Part II, 26,(8)]) and it is compact Hausdorff. It is, however, non-closed in $X$. The space $X$ is, nonetheless, $k$-Hausdorff. This is [PB, Space S000165].

The following lemma concludes the preparations:

Lemma E.2.1.11. *Let $X$ be a compactly generated space, and $R\subset X\times X$ an equivalence relation. Then the following conditions are equivalent:*

(1) *the quotient space $X/R$ is weakly Hausdorff,*

(2) $R$ is a closed subspace of $X\times X$.

We refer the reader to [Str, Prop. 2.17, Prop. 2.20], and [Str, Cor. 2.21].

Proof. We call $\overline{\Delta}$ the diagonal subspace in $(X/R)\times_0 (X/R)$. Since $X/R$ inherits compact generatedness from $X$, the map $q:X\times X\to (X/R)\times (X/R)$ is a submersive map by Lemma E.1.2.17 applied to $X=Y$, $X'=Y'=X/R$, and $f=g$ chosen to be the quotient map $X\to X/R$. As $q^{-1}(\overline{\Delta})=R\subset X\times X$, we see that (2) is equivalent to the statement that $\overline{\Delta}$ is closed in $(X/R)\times (X/R)$, since $q$ is a submersive map. This latter assertion is in turn equivalent to $\overline{\Delta}$ being $k$-closed in $(X/R)\times_0 (X/R)$. By the equivalence of part (1) and part (2) of Lemma E.2.1.6, which holds since $X$ is compactly generated, we conclude. $\square$

Example E.2.1.12. As a simple example of a non-closed $R\subset X\times X$ resulting in a non-weakly Hausdorff (compactly generated) quotient, we take $X$ to be the real line $\mathbf R$ endowed with its Euclidean topology, and $R$ to be the subset of $\mathbf R\times_0\mathbf R$ of those elements $(x,y)$ such that $x=0$ if and only if $y=0$, and if $y\ne 0$ then $x/y\in\mathbf Q^{\times}$. Then $R$ is not closed in the compactly generated Hausdorff $\mathbf R\times_0\mathbf R$. We note that $\mathbf R\times_0\mathbf R=\mathbf R\times\mathbf R$ (Proposition E.1.2.19(2)). The quotient $X/R$ is homeomorphic to the quotient of $\mathbf R$ by the left-multiplication action by $\mathbf Q^{\times}$, with $\mathbf Q^{\times}$ being endowed with the subspace topology inherited from the Euclidean topology on $\mathbf R$. This quotient is then not weakly Hausdorff.

The following important structural result holds specifically for compactly generated weakly Hausdorff spaces.

Proposition E.2.1.13. *Let $X$ be a compactly generated topological space. The following conditions are equivalent:*

## PDF page 849

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **849**

(1) *There exists a subset $I$ of the set of all closed compact Hausdorff subspaces of $X$ such that upon denoting by $i_K:K\to X$ the closed immersion of $K$ in $X$ for each $K\in I$, the continuous map*

$$
q:=\coprod_{K\in I}i_K:\coprod_{K\in I}K\to X
$$

is a submersive map.

(2) $X$ is weakly Hausdorff.

Remark E.2.1.14. By Lemma E.1.1.3(4), condition (1) above characterizes the combined property “compactly generated and weakly Hausdorff” without needing to assume compact generatedness.

Proof. We assume (1). Upon calling $Y:=\coprod_{K\in I}K$, then $Y\times^0_{q,X,q}Y=\coprod_{(K,K')\in I\times I}K\times^0_{i_K,X,i_{K'}}K'$.

We note that as subspaces of $K\times_0 K'$,

$$
K\times^0_{i_K,X,i_{K'}}K'=(i_K,i_{K'})^{-1}(\Delta_X(X))
$$

and since $(i_K,i_{K'}):K\times_0 K'\to X\times_0 X$ is a closed immersion (as $K,K'\subset X$ are closed by hypothesis) $K\times^0_{i_K,X,i_{K'}}K'$ is a closed subspace of $\Delta_X(X)$. As the topological diagonal $\Delta_X$ is an immersion, it is a homeomorphism of $X$ onto the diagonal subspace in $X\times_0 X$. We call $\delta:X\to\Delta_X(X)$ the homeomorphism induced by the topological diagonal morphism $\Delta_X$. Under $\delta^{-1}$, $K\times^0_{i_K,X,i_{K'}}K'$ is mapped homeomorphically onto $K\cap K'$ as a subspace of $X$. As both $K$ and $K'$ are closed in $X$, $K\cap K'$ is a closed subspace of $X$, and hence a closed subspace of both $K$ and $K'$ by [Bou-GT, Ch. I, §3, Prop. 1]. As $K$ and $K'$ are compact Hausdorff, so is $K\cap K'$. It follows that $K\times^0_{i_K,X,i_{K'}}K'$ is compact Hausdorff, and the immersion

$$
K\times^0_{i_K,X,i_{K'}}K'\to K\times_0 K'
$$

is closed. We deduce that $Y\times^0_{q,X,q}Y$ is a closed subspace of

$$
Y\times_0 Y=\coprod_{(K,K')\in I\times I}(K\times_0 K').
$$

Since $Y$ is locally compact Hausdorff, Lemma E.1.2.19 implies that $k(Y\times_0 Y)=Y\times_0 Y$; since $Y\times^0_{q,X,q}Y$ is a closed subspace of $Y\times_0 Y$, it is compactly generated by Lemma E.1.2.25(1). By Lemma E.2.1.11, the quotient of $Y$ by the closed equivalence relation $R:=Y\times^0_{q,X,q}Y=Y\times Y$ is weakly Hausdorff. By Lemma E.1.2.14, such a quotient is homeomorphic to $X$. This proves (2).

Conversely, we assume that (2) holds. We let $I$ be the set of all closed compact Hausdorff subspaces of $X$. We call:

$$
q:=\coprod_{K\in I}i_K:Y:=\coprod_{K\in I}K\to X
\tag{E.2.1.4}
$$

the continuous topological co-product of the closed immersions $i_K:K\to X$. We claim that $q$ from (E.2.1.4) is a submersive map. By Lemma E.1.1.3(4), there exists a set $J$ of compact Hausdorff spaces, and continuous maps $g_K:K\to X$ for every $K\in J$, such that the induced continuous map

$$
q':\coprod_{K\in J}g_K:Y':=\coprod_{K\in J}K\to X
\tag{E.2.1.5}
$$

is submersive. As $g_K(K)$ endowed with the subspace topology is weakly Hausdorff since $X$ is, and it receives a continuous surjection from the compact Hausdorff space $K$, it is itself compact Hausdorff by Lemma E.2.1.4. We define the set-function $J\to I$ by sending $K\in J$ to $g_K(K)\in I$. This induces a continuous map

$$
g:\coprod_{K\in J}K\to\coprod_{K\in I}K
$$

defined as the identity on every $K\in J$, and such that $q\circ g=q'$. As $q'$ is submersive, so is $q$ from (E.2.1.4). $\square$

## PDF page 850

**850** · **CHAPTER E. TOPOLOGICAL STACKS**

In light of Proposition E.2.1.13, we see that compactly generated weakly Hausdorff spaces are closely related to locally compact Hausdorff spaces. As for general compactly generated spaces, they are quotients of locally compact Hausdorff spaces, and the Proposition shows that the weak Hausdorff condition on an object $X$ means that we may choose, as the set $S_X$ from Lemma E.1.1.3 of those compact Hausdorff spaces that compactly generate $X$, the set of compact Hausdorff subspaces. We can further characterize those objects of $\mathbf{CGWH}$ that are locally compact Hausdorff by rephrasing the locally compact condition on $X$ as a stronger smallness condition on $S_X$.

We need the following:

Lemma E.2.1.15. *Let $\{X_n\}_{n\ge 0}$ be a directed sequence of topological spaces. Assume:*

(1) for every integer $n\ge 0$, $X_n$ is a $T_1$-space;

(2) *for $X=\operatorname{colim}_{n\ge 0}X_n$ in $\mathbf{Spaces}$, the canonical maps $f_n:X_n\to X$ have finite fibres.*

*Then for every compact subspace $K\subset X$, there exists an integer $n\ge 0$ such that $K$ is contained in the image of $X_n$.*

We also refer the reader to [VLH, Lemma 2.4].

Proof.$^5$ We let $K\subset X$ be a compact subspace. For every integer $n\ge 1$ such that $(f_n(X_n)-f_{n-1}(X_{n-1}))\cap K\ne\varnothing$, we choose $x_n$ in the intersection. The sequence $F:=\{x_n\}_{n\ge 0}$ is such that for every subset $E\subset F$, $E\cap f_n(X_n)$ is a finite$^6$ set for every $n\ge 0$. As $f:X_n\to f_n(X_n)$ has finite fibres, $f_n^{-1}(E)$ is a finite set, hence closed in $X_n$ since $X_n$ is $T_1$. By design of the topology on $X$, $E$ is closed as a subspace of $X$. Since $E$ was an arbitrary subset of $F$, we deduce that the subspace topology on $F$ inherited from the topology of $X$ is the discrete topology. As $K$ is a subspace of $X$ and $F$ is contained in $K$, $F$ is discrete as a subspace of $K$. Since $K$ is compact, $F$ is finite$^7$ and therefore entirely contained in $f_N(X_N)$ for large enough $N\ge 0$. In particular, we have $(X-f_N(X_N))\cap K=\varnothing$, and hence $K\subset f_N(X_N)$, as desired. $\square$

We recall that a topological space is hemicompact if the set of all of its compact subspaces has a countable co-final subset.

Lemma E.2.1.16. Let $X$ be a topological space. Assume:

(1) $X$ is hemicompact.

(2) $X$ is first-countable.

Then $X$ is locally compact.

Proof. We let $\{K_n\}_{n\ge 0}$ be a sequence of compact subspaces such that every compact subspace $K\subset X$ is contained in $K_n$ for some integer $n\ge 0$. Let $x\in X$ be a point, and $\{U_m\}_{m\ge 0}$ a countable local base at $x$. We may and do assume that $U_{m+1}\subseteq U_m$ holds for every $m\ge 0$. Suppose that for every integer $n\ge 0$, $(X-K_n)\cap U_n\ne\varnothing$. We choose $x_n$ in the intersection and consider the union of the sequence and its limit point $F:=\{x_n\}_{n\ge 0}\cup\{x\}$. Then $F\subset X$ is compact, and hence contained in $K_N$, for some integer $N\ge 0$. However, since $x_N\in F$ is an element of $U_N$, it cannot be an element of $K_N$, a contradiction. It follows that there exists an integer $n\ge 0$ such that $U_n$ is contained in $K_n$, and hence $K_n$ is a compact neighborhood of $x$ in $X$. As $x\in X$ is arbitrary, $X$ is locally compact. $\square$

Corollary E.2.1.17. *Let $X$ be a weakly Hausdorff space. If $X$ is first-countable and countably compactly generated$^8$ then it is locally compact.*

$^5$This proof needs correction; either make a simple fix or give a literature reference for a correct proof.

$^6$why?

$^7$False: $\{1/2^n\}_{n\ge 1}$ as a subspace of $[0,1]$ has the discrete topology but is infinite

$^8$Need to remind the reader what “countably compactly generated” means

## PDF page 851

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **851**

Proof. By Proposition E.2.1.13, we may find a rising sequence $\{K_n\}_{n\ge 0}$ of compact Hausdorff subspaces such that $X=\operatorname{colim}_{n\ge 0}K_n$. By Lemma E.2.1.15, $X$ is hemicompact. By Lemma E.2.1.16, it is locally compact. $\square$

E.2.2. Categorical and topological stabilities of compactly generated weakly Hausdorff spaces.

We now define the category of compactly generated weakly Hausdorff spaces, as a full subcategory of $\mathbf{CG}$, the category of compactly generated spaces.

Definition E.2.2.1. We call $\mathbf{CGWH}$ the category whose objects are compactly generated weakly Hausdorff topological spaces, and morphisms are continuous maps of topological spaces. We refer to $\mathbf{CGWH}$ as the category of compactly generated weakly Hausdorff spaces.

Our aim is to now collect results that show that the full subcategory $\mathbf{CGWH}$ of $\mathbf{CG}$ retains many of the good properties of $\mathbf{CG}$, such as closure under small limits and small colimits, and the cartesian-closed monoidal structure, and has additional features that will become convenient later. One disadvantage of $\mathbf{CGWH}$ is that small colimits in $\mathbf{CGWH}$ cannot be computed in $\mathbf{Spaces}$. In other words, the forgetful functor to $\mathbf{Spaces}$ does not reflect small colimits. However, all the small colimits of interest for the purposes of this appendix will indeed be reflected by the forgetful functor, and can be computed by their topological counterpart. One important advantage of $\mathbf{CGWH}$ is that submersive maps will turn out to be exactly the universally effective epimorphisms of $\mathbf{CGWH}$, therefore providing a direct and concrete description of the canonical topology on $\mathbf{CGWH}$, and rendering the development of a theory of stacks in groupoids over a site of compactly generated weakly Hausdorff spaces efficient.

In this subsection, we study analogs for $\mathbf{CGWH}$ of the closure properties of $\mathbf{CG}$. We begin by comparing the two categories. We consider the forgetful functor:

$$
u_{\mathrm{wh}}:\mathbf{CGWH}\to\mathbf{CG}
\tag{E.2.2.1}
$$

sending a compactly generated weakly Hausdorff topological space to itself as a compactly generated space, and sending continuous maps to continuous maps. We further define:

$$
u_{\mathrm{cgwh}}:\mathbf{CGWH}\to\mathbf{Spaces}
\tag{E.2.2.2}
$$

to be the forgetful functor sending a compactly generated weakly Hausdorff space to itself as an ordinary topological space, and sending continuous maps to continuous maps. Since $u_{\mathrm{cg}}\circ u_{\mathrm{wh}}=u_{\mathrm{cgwh}}$, the notation being used should be un-ambiguous.

We now discuss the existence of a left-adjoint

$$
h:\mathbf{CG}\to\mathbf{CGWH}
$$

to the forgetful functor. In other words, $h(X)\in\mathbf{CGWH}$ is an initial object receiving a continuous map from $X\in\mathbf{CG}$. Its construction and properties are briefly recalled below. (We refer the reader to [Str, Prop. 2.22].)

Definition E.2.2.2. Let $X$ be a compactly generated space. We define:

$$
R_X\subset X\times X
\tag{E.2.2.3}
$$

to be the intersection of all closed equivalence relations on $X$ (for the $k$-topology on $X\times X$). We define the topological space:

$$
h(X):=X/R_X
\tag{E.2.2.4}
$$

endowed with the quotient topology. We call:

$$
q_X:X\to h(X)
\tag{E.2.2.5}
$$

the quotient map.

## PDF page 852

**852** · **CHAPTER E. TOPOLOGICAL STACKS**

Remark E.2.2.3. For $X$ a compactly generated space, since the equivalence relation $R_X\subset X\times X$ from (E.2.2.3) is closed, the quotient space $h(X)$ is compactly generated weakly Hausdorff by Lemma E.2.1.11.

We now check that formation of $R_X$ from (E.2.2.3) is natural in $X$, and therefore $h(X)$ defines a functor:

$$
h:\mathbf{CG}\to\mathbf{CGWH}.
\tag{E.2.2.6}
$$

We begin by proving an analog of Lemma E.1.2.1; see [Str, Prop. 2.22] and [Str, Cor. 2.23].

Lemma E.2.2.4. *Let $X$ be a compactly generated space, and $\Sigma\subset 2^{X\times X}$ the set of all subspaces $R\subset X\times X$ such that:*

(a) $R^{\mathrm{set}}$ is an equivalence relation on $X^{\mathrm{set}}\times X^{\mathrm{set}}$.

(b) $R$ is closed in $X\times X$.

Then, upon calling:

$$
R_X:=\bigcap_{R\in\Sigma}R
\tag{E.2.2.7}
$$

*we have that $R_X^{\mathrm{set}}$ is an equivalence relation on $X^{\mathrm{set}}\times X^{\mathrm{set}}$, and $R_X$ is closed in $X\times X$. Moreover:*

(1) formation of $h(X)$ is natural in $X$,

(2) *the functor $h:\mathbf{CG}\to\mathbf{CGWH}$ is left-adjoint to the forgetful functor $u_{\mathrm{wh}}:\mathbf{CGWH}\to\mathbf{CG}$,*

(3) *the natural map $\varepsilon_X:X\to h(X)$ is an isomorphism when $X$ is also weakly Hausdorff,*

(4) *applying $h$ to the natural map $Y\to u_{\mathrm{wh}}(h(Y))$ for $Y\in\mathbf{CG}$ yields $\varepsilon_{h(Y)}$ and so is an isomorphism.*

Proof. We note that, as $X\times X$ is closed in itself, $\Sigma$ is non-empty. The set-theoretic intersection of equivalence relations on a set is an equivalence relation, so $R_X$ is a closed equivalence relation in $X\times X$. We now check part (1) and part (2).

Let $Y$ be a compactly generated weakly Hausdorff space, and $f:X\to Y$ a morphism in $\mathbf{CG}$. We claim that $X\times_{f,Y,f}X$ is closed in $X\times X$. Indeed, we have:

$$
X\times^0_{f,Y,f}X=(f,f)^{-1}(\Delta_Y(Y))
\tag{E.2.2.8}
$$

and $\Delta_Y(Y)\subset Y\times_0 Y$ is $k$-closed by part (2) of Lemma E.2.1.6. As $f$ is continuous, $(f,f)^{-1}(\Delta_Y(Y))$ is $k$-closed by functoriality of the $k$-topology (see Lemma E.1.2.1). Moreover, $(f,f)^{-1}(\Delta_Y(Y))$ is an equivalence relation on $X\times_0 X$, since $\Delta_Y(Y)$ is in $Y$. From (E.2.2.8) we deduce that

$$
X\times_{f,Y,f}X=k(X\times^0_{f,Y,f}X)=k((f,f)^{-1}(\Delta_Y(Y)))
$$

is closed in $X\times X$, since $(f,f)^{-1}(\Delta_Y(Y))$ is $k$-closed, as seen in the foregoing. It follows that we have the containment $R_X\subset X\times_{f,Y,f}X$, which gives a unique map:

$$
\psi:h(X)\to\operatorname{coeq}(p_1,p_1:X\times_{f,Y,f}X\rightrightarrows X)
\tag{E.2.2.9}
$$

with $p_1,p_2$ the two projections, the co-equalizer being formed in $\mathbf{CG}$, and such that $\psi\circ q_X$ agrees with the canonical submersive map:

$$
f':X\to\operatorname{coeq}(p_1,p_2)
\tag{E.2.2.10}
$$

that $\operatorname{coeq}(p_1,p_2)$ receives from $X$.

The space $Y$ further receives a unique map $\phi$ from $\operatorname{coeq}(p_1,p_1)$ such that the submersive map from (E.2.2.10) satisfies

$$
q\circ f'=f
\tag{E.2.2.11}
$$

In light of (E.2.2.11) and since the map $\psi$ from (E.2.2.9) satisfies $\psi\circ q_X=f'$, we deduce:

$$
q\circ\psi\circ q_X=f
$$

## PDF page 853

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **853**

which means that $f$ factors through $q_X$. We further observe that both $q$ and $\psi$ are unique: $q$ by universality of topological quotients and Lemma E.1.2.14, and $\psi$ by the universal property of co-equalizers and the definition of the map $f'$ of (E.2.2.10). We have shown that for any compactly generated spaces $X,Y$ with $Y$ weakly Hausdorff, and any continuous map $f:X\to Y$, $f$ factors uniquely through $q_X:X\to h(X)$ from (E.2.2.5). This proves functoriality of $h(\cdot)$ and part (2). Part (3) is clear from the universal property, and (4) is part of the formalism of adjunction. $\square$

Lemma E.2.2.5. *The category $\mathbf{CGWH}$ contains all small limits and all small colimits. Moreover, for any small category $I$ and diagram $P:I\to\mathbf{CGWH}$:*

(1) *$\lim_I P$ in $\mathbf{CGWH}$ is computed in $\mathbf{CG}$, i.e. the forgetful functor $u_{\mathrm{wh}}$ reflects and commutes with small limits.*

(2) $\operatorname{colim}_I P$ in $\mathbf{CGWH}$ is computed as:

$$
\operatorname{colim}_I P=h(\operatorname{colim}_I u_{\mathrm{wh}}\circ P)
\tag{E.2.2.12}
$$

*upon evaluating $h(\cdot)$ on the colimit of the small diagram $u_{\mathrm{wh}}\circ P$ in $\mathbf{CG}$.*

Proof. Assertion (2) is immediate from $h$ being a left-adjoint to $u_{\mathrm{wh}}$. For (1), we just have to show that the limit in $\mathbf{CG}$ of the diagram $u_{\mathrm{wh}}\circ P$ is weakly Hausdorff. To see this, we use Lemma E.2.1.6. We observe that the diagonal subspace $\Delta\subset(\lim_I(u_{\mathrm{wh}}\circ P))\times_0(\lim_I(u_{\mathrm{wh}}\circ P))$, as a subspace of $\prod^0_{i\in I}(u_{\mathrm{wh}}\circ P)(i)$, is the intersection:

$$
\bigcap_{i\in I}p_i^{-1}(\Delta_i)
$$

where $p_i:\lim_I(u_{\mathrm{wh}}\circ P)\to (u_{\mathrm{wh}}\circ P)(i)$ is the projection, and $\Delta_i\subset (u_{\mathrm{wh}}\circ P)(i)\times_0 (u_{\mathrm{wh}}\circ P)(i)$ is the diagonal subspace. This latter is $k$-closed by Lemma E.2.1.6(2), as $(u_{\mathrm{wh}}\circ P)(i)$ is weakly Hausdorff. It follows that $p_i^{-1}(\Delta_i)$ is also $k$-closed within $\prod^0_{i\in I}(u_{\mathrm{wh}}\circ P)(i)$. The intersection $\Delta=\bigcap_{i\in I}p_i^{-1}(\Delta_i)$ is therefore also $k$-closed, and by Lemma E.2.1.6 we conclude. $\square$

The following remark is the analog for $\mathbf{CGWH}$ of Remark E.1.2.3.

Remark E.2.2.6. On the construction and properties of $h(X)$, we observe:

(1) the functor $h(\cdot)$, by its very design, generally does not preserve underlying sets, contrary to the functor $k(\cdot)$ that only modifies the topology on spaces,

(2) small limits in $\mathbf{CGWH}$ can be computed in $\mathbf{CG}$ by Lemma E.2.2.5(1), and by Lemma E.1.2.2(1) their underlying set is the limit of the underlying sets of the objects within the diagram in $\mathbf{CGWH}$,

(3) if $P:I\to\mathbf{CGWH}$ is a diagram such that the limit of the induced diagram $u_{\mathrm{cg}}\circ u_{\mathrm{wh}}\circ P=u_{\mathrm{cgwh}}\circ P$ in $\mathbf{Spaces}$ is compactly generated weakly Hausdorff then $\lim_I(u_{\mathrm{cg}}\circ u_{\mathrm{wh}}\circ P)=\lim_I(u_{\mathrm{cgwh}}\circ P)$ computes $\lim_I P$ in $\mathbf{CGWH}$,

(4) contrary to the case of colimits in $\mathbf{CG}$, the underlying set of a small colimit in $\mathbf{CGWH}$ is not the colimit of the underlying sets of the objects within the diagram in $\mathbf{CGWH}$ unless the colimit computed in $\mathbf{CG}$ is already weakly Hausdorff; see Example E.2.2.7 below.

Example E.2.2.7. The following is an example of a small (filtered) colimit in $\mathbf{CGWH}$ of a small diagram $P:I\to\mathbf{CGWH}$, such that the set-theoretic colimit $\operatorname{colim}_{i\in I}P(i)^{\mathrm{set}}$ is not the set underlying $\operatorname{colim}_I P$. We let $I:=\mathbf N_{>0}$ be the positive integers with their natural order, defining $\operatorname{Map}_I(i,j)$ to be the singleton set if $i\le j$, and the empty set otherwise. We define $P(i):=S^1$, the unit circle, and for any morphism $i\to j$ in $I$, we set $P(i\to j)$ to be the the map raising $z\in S^1$ to the $2^{j-i}$-th power. Then the colimit in $\mathbf{Spaces}$ of the resulting diagram of underlying topological spaces is not $T_1$, even though each $P(i)$ is compact Hausdorff. In particular, the colimit $\operatorname{colim}_I P$ in $\mathbf{CGWH}$ will have as its underlying set a non-trivial quotient of the set-theoretic colimit of the underlying sets of the $P(i)$'s. The reader is referred to [Du, Appendix 2, Example 2, p. 422].

## PDF page 854

**854** · **CHAPTER E. TOPOLOGICAL STACKS**

Remark E.2.2.8. In Definition E.1.2.4, we introduced notation to distinguish arbitrary small topological products, and topological fibre products, from the internal products and fibre products formed in $\mathbf{CG}$. The definition omits any mention of co-products, because of part (2) of Lemma E.1.2.2, asserting that colimits in $\mathbf{CG}$ can be computed in $\mathbf{Spaces}$, leaving no ambiguity to the meaning of the notation $\coprod$. However, the analog for compactly generated weakly Hausdorff spaces of part (2) of Lemma E.1.2.2 does not hold. In other words, not all colimits in $\mathbf{Spaces}$ of compactly generated weakly Hausdorff spaces will compute colimits internal to $\mathbf{CGWH}$, a phenomenon witnessed by Example E.2.2.7. Co-products in $\mathbf{Spaces}$, however, do, leaving once again no ambiguity to the use of the notation $\coprod$. We will therefore continue to have no necessity for dedicated notation for topological co-products. This is (2) in the next lemma.

We have the following:

Corollary E.2.2.9. *Let $I$ be a small category, and $P:I\to\mathbf{CGWH}$ a diagram. Then:*

(1) *The product $\prod_I u_{\mathrm{wh}}\circ P$ in $\mathbf{CG}$ computes the product $\prod_I P$ in $\mathbf{CGWH}$.*

(2) *The co-product $\coprod_I u_{\mathrm{cgwh}}\circ P$ in $\mathbf{Spaces}$ computes the co-product $\coprod_I P$ in $\mathbf{CGWH}$.*

Proof. Part (1) is a consequence of Lemma E.2.2.5(1). To see part (2), we observe that $\coprod_I u_{\mathrm{cgwh}}\circ P$ in $\mathbf{Spaces}$ computes the co-product $\coprod_I u_{\mathrm{wh}}\circ P$ in $\mathbf{CG}$ by Lemma E.1.2.2(2). We need to check that the compactly generated (Lemma E.1.2.2(2))

$$
X=\coprod_I u_{\mathrm{wh}}\circ P
\tag{E.2.2.13}
$$

is weakly Hausdorff. This is clear from (2) $\Rightarrow$ (1) in Lemma E.2.1.6 for $X\in\mathbf{CG}$. $\square$

Notation E.2.2.1. When $X$ and $Y$ are compactly generated weakly Hausdorff spaces, we will, henceforth, denote by $\mathscr{C}ont(X,Y)$ the compactly generated function space $\mathscr{C}ont_k(X,Y)$.

The above change in notation is justified by the following Lemma, for which we refer the reader to [Str, Prop.2.24].

Proposition E.2.2.10. *If $X$ and $Y$ are compactly generated topological spaces and $Y$ is weakly Hausdorff, then $\mathscr{C}ont_k(X,Y)$ is a compactly generated weakly Hausdorff topological space. The cartesian symmetric monoidal category $(\mathbf{CGWH},\times,*)$ inherits from the cartesian symmetric monoidal category $(\mathbf{CG},\times,*)$ the cartesian-closed monoidal category structure.*

Proof. As $(\mathbf{CGWH},\times,*)$ is a full symmetric monoidal subcategory of $(\mathbf{CG},\times,*)$, the last assertion follows from the first. It is therefore enough to check that for $X$ and $Y$ compactly generated spaces, with $Y$ weakly Hausdorff, then the compactly generated function space $\mathscr{C}ont_k(X,Y)$ is weakly Hausdorff. We now let $W:=\mathscr{C}ont_k(X,Y)$, and for any $x\in X$ let $e_x:W\to Y$ be given by $e_x(f):=f(x)$. Since $e_x$ is obtained by $\mathscr{C}ont_k$-functoriality with respect to $\{x\}\to X$, $e_x$ is continuous. We now observe that as subspaces of $W\times_0 W$:

$$
(e_x,e_x)^{-1}(\Delta_Y(Y))=\{(f,g)\in W\times W\mid f(x)=g(x)\}\subset W\times_0 W
\tag{E.2.2.14}
$$

We claim $(e_x,e_x)^{-1}(\Delta_Y(Y))$ is $k$-closed. Since $Y$ is weakly Hausdorff, $\Delta_Y(Y)$ is $k$-closed in $Y\times_0 Y$ by Lemma E.2.1.6(2). By functoriality of the $k$-topology (Lemma E.1.2.1), $(e_x,e_x)^{-1}(\Delta_Y(Y))$ is also $k$-closed. It follows from (E.2.2.14) that $(e_x,e_x)^{-1}(\Delta_Y(Y))$ is closed in $W\times W$ for every $x\in X$, and hence $\bigcap_{x\in X}(e_x,e_x)^{-1}(\Delta_Y(Y))$ is also closed in $W\times W$, being an intersection of closed subspaces. We now observe that

$$
\Delta_W(W)=\bigcap_{x\in X}(e_x,e_x)^{-1}(\Delta_Y(Y))
$$

so by Lemma E.2.1.6(2) we get $\mathscr{C}ont_k(X,Y)$ is weakly Hausdorff. $\square$

## PDF page 855

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **855**

**E.2.3. Permanence properties of compactly generated weakly Hausdorff spaces.** Examples of compactly generated weakly Hausdorff topological spaces are all locally compact Hausdorff topological spaces by (1) in the next lemma.

**Proposition E.2.3.1.** *We have:*

*(1) all locally compact Hausdorff topological spaces $X$ are compactly generated weakly Hausdorff,*

*(2) the product in $\mathbf{Spaces}$ of a compactly generated weakly Hausdorff space and a locally compact Hausdorff space is compactly generated weakly Hausdorff and computes the product in $\mathbf{CGWH}$.*

*Proof.* By Lemma E.1.2.19(1), $X$ is compactly generated; it is weakly Hausdorff since it is Hausdorff. By Lemma E.1.2.19(2), $X \times_0 Y$ is compactly generated and the product $X \times Y$ in $\mathbf{CG}$ can be computed in $\mathbf{Spaces}$. By Lemma E.2.2.5(1), the product $X \times Y$ in $\mathbf{CG}$ computes the product in $\mathbf{CGWH}$, and the Proposition is proved. $\square$

**Remark E.2.3.2.** On the above Lemma E.2.3.1, we make the following observations:

(1) it will allow us to compute internal products of the locally compact Hausdorff topological spaces intervening in our constructions of topological stacks of interest by working within $\mathbf{Spaces}$, therefore leaving no ambiguity as to where products are being formed and allowing access to product topologies of the spaces involved.

(2) The Hausdorff assumption in part (2) of the Lemma cannot be dropped altogether. We refer the reader to Lemma E.2.4.9, for a counter-example.

We conclude this subsection by reviewing a number of permanence properties enjoyed by $\mathbf{CGWH}$, and with a result providing a concrete description of the (regular) monomorphisms and (regular) epimorphisms in $\mathbf{CGWH}$. We first prove the following analog of Lemma E.1.2.27, now characterizing immersions in $\mathbf{CGWH}$ rather than in $\mathbf{CG}$:

**Lemma E.2.3.3.** *Let $X, Y$ be compactly generated weakly Hausdorff spaces and $f : X \to Y$ a continuous injective map. The following are equivalent:*

*(1) $f$ is an immersion.*

*(2) For any compactly generated weakly Hausdorff topological space $T$ and any set-function $g : T \to X$, $g$ is continuous if and only if $f \circ g$ is continuous.*

For the proof of this result, also see [Str, Cor. 2.29].

*Proof.* By Lemma E.1.2.27, $f$ is an immersion if and only if for any compactly generated space $T$ and any set-function $g : T \to X$, $f \circ g$ is continuous if and only if $g$ is. We claim that it is enough to verify this condition when $T$ is, in addition, weakly Hausdorff. Indeed, let $T$ be any compactly generated space and $g : T \to X$ any set-function. If $g$ is continuous, it factors through the continuous quotient map $T \to h(T)$ by Lemma E.2.2.4(2), as $X$ is weakly Hausdorff. If $f \circ g$ is continuous, then $f \circ g$ factors through $h(T)$ by Lemma E.2.2.4(2), as $Y$ is weakly Hausdorff. In this latter case, $g$ itself factors through $h(T)$, as $f$ is continuous and injective. Either way, we may replace $T$ with $h(T)$ and assume that $T$ is weakly Hausdorff. $\square$

**Lemma E.2.3.4.** *Let $g : X \to Y$ be a continuous map of compactly generated weakly Hausdorff topological spaces. If $f$ is a continuous section to $g$, then $f$ is a closed immersion and $g$ is a submersive map.*

*Proof.* Since $g$ is a continuous surjection, the existence of $f$ clearly implies that $g$ is a quotient map, hence submersive, and $f$ is an immersion. We now observe that we have $f(Y) = \{x \in X \mid f(g(x)) = x\}$. It follows that we have:

$$
f(Y) = (f \circ g, \mathrm{id})^{-1}(\Delta_X(X)),
$$

## PDF page 856

**856** · **CHAPTER E. TOPOLOGICAL STACKS**

and as $\Delta_X(X) \subset X \times_0 X$ is $k$-closed in $X \times_0 X$ by part (2) of Lemma E.2.1.6, $f(Y)$ is also $k$-closed in $X$, hence closed, as $X$ is compactly generated. It follows that $f$ is a closed immersion. $\square$

We now prove permanence properties for (closed) immersions under composition.

**Lemma E.2.3.5.** *Let $f : X \to Y$ and $g : Y \to Z$ be continuous maps of compactly generated weakly Hausdorff topological spaces.*

*(1) If $g \circ f$ is an immersion then so is $f$.*

*(2) If $g \circ f$ is a closed immersion then so is $f$.*

*(3) If $g \circ f$ is an open immersion then $f$ is a locally closed immersion.*

*Proof.* Assertion (1) holds with general topological spaces (for each open $U \subset X$ and an open $V \subset Z$ such that $(g \circ f)^{-1}(V) = U$, we have $f^{-1}(W) = U$ for the open $W = g^{-1}(V) \subset Y$). For (2) and (3), we can replace $Z$ with the subspace $(g \circ f)(X) \subset Z$ to reduce to the case that $Z = X$; i.e., $f$ is a section to $g$. Then we are done by Lemma E.2.3.4. $\square$

We now survey a number of permanence properties of certain classes of morphisms in $\mathbf{CGWH}$. For the proof of the following lemma, we refer the reader to [Str, Prop. 2.32].

**Lemma E.2.3.6.** *The following classes of morphisms in $\mathbf{CGWH}$ are stable under finite compositions and arbitrary base-change, and are local on the target:*

*(1) Injective maps.*

*(2) Surjective maps.*

*(3) Immersions.*

*(4) Closed immersions.*

*(5) Open immersions.*

*(6) Submersive maps.*

We note that by Example E.1.2.16, part (6) of the Lemma does not hold if we drop the weak Hausdorff assumption. Stability of submersive maps under arbitrary base change is an advantage of the category $\mathbf{CGWH}$ over the category $\mathbf{CG}$.

*Proof.* As fibre products in $\mathbf{CGWH}$ can be computed in $\mathbf{CG}$ by part (1) of Lemma E.2.2.5, and since the forgetful functor $\mathbf{CG} \to \mathbf{Sets}$ preserves fibre products by Lemma E.1.2.2(1), checking (1) and (2) is reduced to showing that injective, respectively surjective, set-functions remain injective, respectively surjective, after arbitrary set-theoretic fibre product, and are stable under finite compositions, which is indeed the case.

Obviously immersions, closed immersions, open immersions, and submersions are stable under finite compositions. Being an injective, respectively surjective, continuous map is local on the target, and being an immersion is also local on the target. Closed, respectively open, immersions are also local on the target because closed, respectively open maps are. Submersiveness is also local on the target. We are now to check that immersions, closed immersions, open immersions and submersive maps are stable under arbitrary base change in the category $\mathbf{CGWH}$. To this end, we consider the following cartesian diagram in $\mathbf{CGWH}$:

(E.2.3.1)

```latex
\begin{tikzcd}
X_T := X \times_{f,Y,g} T \arrow[r, "f_T"] \arrow[d, "p"'] & T \arrow[d, "g"] \\
X \arrow[r, "f"'] & Y
\end{tikzcd}
```

where we assume that $f$ is an immersion. We let $P$ be an arbitrary compactly generated weakly Hausdorff space, with $h : P \to X_T$ an arbitrary set-function such that $f_T \circ h$ is continuous. It follows that $g \circ f_T \circ h = f \circ p \circ h$ is

## PDF page 857

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **857**

continuous. As $f$ is an immersion, we deduce that $p \circ h$ is continuous. Since $f_T \circ h$ is continuous by assumption and $p \circ h$ is continuous by the foregoing, the universal property of fibre products yields continuity of the unique map $h' : P \to X_T$. The underlying set-functions of $h$ and $h'$ are the same set-function, so $h$ is continuous. By Lemma E.2.3.3, $f_T$ is an immersion. Set-theoretically, we have:

$$
f_T(X_T) = g^{-1}(f(X)). \tag{E.2.3.2}
$$

As a subspace of $T$, $g^{-1}(f(X))$ is closed, respectively open when $f$ is a closed, respectively open immersion. It follows by (E.2.3.2) that closed immersions, respectively open immersions, are stable under arbitrary base-change in $\mathbf{CGWH}$.

We now prove that submersive maps are stable under arbitrary base-change. To this end, we consider the cartesian diagram from (E.2.3.1), where $f$ is now assumed to be a submersive map. By Lemma E.1.2.17, combined with part (1) of Lemma E.2.2.5, asserting that products in $\mathbf{CGWH}$ can be computed in $\mathbf{CG}$, the map $(f, \mathrm{id}) : X \times T \to Y \times T$ is also a submersive map. Moreover, the following diagram in $\mathbf{CGWH}$ is also cartesian:

(E.2.3.3)

```latex
\begin{tikzcd}
X_T := X \times_{f,Y,g} T \arrow[r, "{(f,\mathrm{id})_T = f_T}"] \arrow[d, "p'"'] & T \arrow[d, "{(g,\mathrm{id})}"] \\
X \times T \arrow[r, "{(f,\mathrm{id})}"'] & Y \times T
\end{tikzcd}
```

and $(g, \mathrm{id})$ is a closed immersion by Lemma E.2.3.4, as it is a continuous section to the second projection $Y \times T \to T$. Upon renaming in (E.2.3.3) the maps $(g, \mathrm{id})$ as $g$, $(f, \mathrm{id})$ as $f$, $p'$ as $p$, we turn (E.2.3.3) into (E.2.3.1) and are reduced to the case $g$ is a closed immersion. Then $p^{-1}(f^{-1}(g(T)))$ is closed in $X_T$, hence it belongs to $\mathbf{CGWH}$ and categorically it coincides with $X_T$, so then $X_T \to T$ is the restriction of the submersive $f : X \to Y$ over a closed subset $T \subset Y$. Hence, $X_T \to T$ is a submersion as desired. $\square$

In a similar vein, we can descend some of the properties of continuous maps in $\mathbf{CGWH}$ in Lemma E.2.3.6, along submersive maps:

**Lemma E.2.3.7.** *Let $X, Y, T$ be compactly generated weakly Hausdorff spaces, $f : X \to Y$ and $g : T \to Y$ two continuous maps. We consider the following cartesian diagram in $\mathbf{CGWH}$:*

(E.2.3.4)

```latex
\begin{tikzcd}
X_T := X \times_{f,Y,g} T \arrow[r, "f'"] \arrow[d, "g'"'] & T \arrow[d, "g"] \\
X \arrow[r, "f"'] & Y
\end{tikzcd}
```

*Assume that $g$ is submersive.*

*(1) If $f'$ is injective then so is $f$.*

*(2) If $f'$ is surjective then so is $f$.*

*(3) If $f'$ is an immersion then so is $f$.*

*(4) If $f'$ is a closed immersion then so is $f$.*

*(5) If $f'$ is an open immersion then so is $f$.*

*(6) If $f'$ is a submersive map then so is $f$.*

*Proof.* We prove (1). By part (1) of Lemma E.2.2.5, the fibre product is computed in $\mathbf{CG}$, and hence its underlying set is a fibre product in $\mathbf{Sets}$ by Lemma E.1.2.2(1). Let $x, x'$ be points in $X$ such that $f(x) = f(x')$. As $g$ is submersive, it is surjective, and hence there exists $t \in T$ such that $g(t) = f(x) = f(x')$. This gives

## PDF page 858

**858** · **CHAPTER E. TOPOLOGICAL STACKS**

$z, z' \in X_T$ such that $f'(z) = f'(z') = t$, and $g'(z) = x$, $g'(z') = x'$. Since $f'$ is injective, we have $z = z'$, and hence $x = x'$, so $f$ is injective. Part (2) follows from surjectivity of $g \circ f'$.

We prove (3). As $f'$ is an immersion, $f$ is injective by part (1). Let $Z$ be an arbitrary compactly generated weakly Hausdorff space, and $h : Z \to X$ a set-function such that $f \circ h$ is continuous. We consider the following diagram:

(E.2.3.5)

```latex
\begin{tikzcd}
Z_T := Z \times_{f \circ h,Y,g} T \arrow[r, dashed, "h'"'] \arrow[d, "g''"'] \arrow[rr, "k", bend left] & X_T \arrow[d, "g'"] \arrow[r, "f'"'] & Y \arrow[d, "g"'] \\
Z \arrow[r, "h"'] & X \arrow[r, "f"'] & Y
\end{tikzcd}
```

where the two solid squares are cartesian. By part (6) of Lemma E.2.3.6, $g''$ is submersive. Let $h'$ be the set-function obtained as the set-theoretic base change of $h$ along $g'$. We have $f' \circ h' = k$, which is continuous. As $f'$ is an immersion by assumption, $h'$ is continuous. It follows that $h \circ g'' = g' \circ h'$ is continuous. Since $g''$ is submersive, $h$ is continuous and so by Lemma E.2.3.3 we see $f$ is an immersion.

We prove (4) and (5). By (3), $f$ is an immersion. The image of $f'$ endowed with the subspace topology is closed, respectively open, in $Y$. The image $f(X)$ of $f$ endowed with the subspace topology is such that $g^{-1}(f(X)) = f'(X_T)$. Since $g$ is submersive, $f(X)$ is closed, respectively open, and hence the immersion $f$ is a closed, respectively open, immersion. We prove (6). Since $f'$ and $g$ are submersive, their composition is submersive by Lemma E.2.3.6(6), and hence $f$ is submersive. $\square$

We discuss properties of submersive maps within the category $\mathbf{CGWH}$. Here is an analog in $\mathbf{CGWH}$ of Lemma E.1.2.14 for $\mathbf{CG}$.

**Lemma E.2.3.8.** *Let $X, Y$ be compactly generated weakly Hausdorff spaces, and $f : X \to Y$ a continuous map. The following conditions are equivalent:*

*(1) There exists a compactly generated weakly Hausdorff space $R$, two maps $s, t : R \rightrightarrows X$ such that $f \circ s = f \circ t$, and a continuous $c : \mathrm{coeq}(s, t) \to Y$ such that the canonical map $p : X \to \mathrm{coeq}(s, t)$ satisfies $c \circ p = f$.*

*(2) $f$ is the co-equalizer in $\mathbf{CGWH}$ of the diagram $p_1, p_2 : X \times_{f,Y,f} X \rightrightarrows X$, where $p_1, p_2$ are the two projections.*

*(3) $f$ is a submersive map.*

*Proof.* We assume that (1) holds and deduce (3). By Lemma E.2.2.5(2), the co-equalizer of $(s, t)$ is computed as:

$$
h(\mathrm{coeq}_{\mathbf{CG}}(u_{\mathrm{wh}}(s), u_{\mathrm{wh}}(t)))
$$

where $\mathrm{coeq}_{\mathbf{CG}}(u_{\mathrm{wh}}(s), u_{\mathrm{wh}}(t))$ denotes the co-equalizer in $\mathbf{CG}$ of $u_{\mathrm{wh}}(s)$ and $u_{\mathrm{wh}}(t)$. For the canonical projection $p : X \to \mathrm{coeq}(s, t)$, the canonical projection $p' : u_{\mathrm{wh}}(X) \to \mathrm{coeq}_{\mathbf{CG}}(u_{\mathrm{wh}}(s), u_{\mathrm{wh}}(t))$, and the submersive map

$$
q : \mathrm{coe}q_{\mathbf{CG}}(u_{\mathrm{wh}}(s), u_{\mathrm{wh}}(t)) \to h(\mathrm{coeq}_{\mathbf{CG}}(u_{\mathrm{wh}}(s), u_{\mathrm{wh}}(t))) \tag{E.2.3.6}
$$

from (E.2.2.5), we have

$$
q \circ p' = u_{\mathrm{wh}}(p). \tag{E.2.3.7}
$$

Since $p'$ is submersive by the equivalence of part (1) and part (3) of Lemma E.1.2.14, so is $u_{\mathrm{wh}}(p)$ because $q$ is submersive. Since $X$ and $\mathrm{coeq}(s, t)$ are compactly generated weakly Hausdorff, $u_{\mathrm{wh}}(p)$ and $p$ are the same continuous map, which is therefore submersive. As $c$ is a homeomorphism, $f = c \circ p$ is also submersive and so (3) holds.

## PDF page 859

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **859**

We now assume that (3) holds, and verify that (2) holds. Since we have $X \times^0_{f,Y,f} X = (f, f)^{-1}(\Delta_Y(Y))$ as subspaces of $X \times_0 X$, and $\Delta_Y(Y)$ is $k$-closed as a subspace of $Y \times_0 Y$ by Lemma E.2.1.6, we deduce that $X \times^0_{f,Y,f} X$ is a $k$-closed subspace of $X \times_0 X$. Thus, $X \times_{f,Y,f} X \subset X \times X$ is closed. The map $u_{\mathrm{wh}}(f)$ is the co-equalizer of its kernel pair in $\mathbf{CG}$ by (3) $\Rightarrow$ (2) in Lemma E.1.2.14 since $u_{\mathrm{wh}}(f) = f$ topologically and we’re assuming $f$ is submersive. The kernel pair of $f$ in $\mathbf{CGWH}$ is computed in $\mathbf{CG}$ by part (1) of Lemma E.2.2.5. Since $X \times_{f,Y,f} X \subset X \times X$ is closed, then by Lemma E.2.1.11, upon calling $p_1, p_2 : X \times_{f,Y,f} X \rightrightarrows X$ the two projections, $\mathrm{coeq}(p_1, p_2)$ is computed in $\mathbf{CG}$ and (2) is proved. Since (2) implies (1) upon choosing $R := X \times_{f,Y,f} X$ and $(s, t) = (p_1, p_2)$, the Lemma is proved. $\square$

We now approach a result concerning the computability in $\mathbf{Spaces}$ of certain push-outs in $\mathbf{CGWH}$. We begin with the following:

**Lemma E.2.3.9.** *Let $f : X \to Y$, $g : Z \to Y$ be morphisms in $\mathbf{CGWH}$. Upon denoting by $f' : X' \to Y'$ and $g' : Z' \to Y'$ the associated continuous maps in $\mathbf{Spaces}$, we consider the following cartesian diagram in $\mathbf{Spaces}$:*

```latex
\begin{tikzcd}
X'_{Z'} := X' \times^0_{f',Y',g'} Z' \arrow[r, "f'_{Z'}"] \arrow[d, "p"'] & Z' \arrow[d, "g'"] \\
X' \arrow[r, "f'"'] & Y'
\end{tikzcd}
```

*If $f'_{Z'}$ is a closed immersion (such as when $f'$ is) then $X'_{Z'}$ is compactly generated weakly Hausdorff, and it computes the fibre product $X \times_{f,Y,g} Z$ of $f$ and $g$ in $\mathbf{CGWH}$.*

*Proof.* Since $f'_{Z'}$ is an immersion, $X'_{Z'}$ is weakly Hausdorff since $Z'$ is. It also lies in $\mathbf{CG}$ since $f'_{Z'}$ is a closed immersion. By Lemma E.2.2.5(1), $k(X'_{Z'}) = u_{\mathrm{wh}}(X) \times_{u_{\mathrm{wh}}(f),u_{\mathrm{wh}}(Y),u_{\mathrm{wh}}(g)} u_{\mathrm{wh}}(Z)$ is weakly Hausdorff and computes $X \times_{f,Y,g} Z$, and by the foregoing we have $k(X'_{Z'}) = X'_{Z'}$, so the lemma is proved. $\square$

We now prove the promised result on push-outs:

**Lemma E.2.3.10.** *Let $X, Z, P$ be compactly generated weakly Hausdorff spaces. Let $Y$ be the push-out in $\mathbf{CGWH}$ of $X, Z$ along two continuous maps $p : P \to Z$ and $q : P \to X$ from $P$ making the diagram*

```latex
\begin{tikzcd}
P \arrow[r, "p"] \arrow[d, "q"'] & Z \arrow[d, "g"] \\
X \arrow[r, "f"'] & Y
\end{tikzcd}
```

*commute in $\mathbf{CGWH}$ and assume the map $p$ is a closed immersion. Then $f$ is a closed immersion and the push-out in $\mathbf{CGWH}$ can be computed in $\mathbf{Spaces}$. Moreover:*

*(1) the fibre product $X \times_{f,Y,g} Z$ of $f$ and $g$ in $\mathbf{CGWH}$ can be computed in $\mathbf{Spaces}$,*

*(2) in $\mathbf{CGWH}$, the natural map*

$$
P \to X \times_{f,Y,g} Z
$$

*is a homeomorphism.*

*Proof.* By Corollary E.2.2.9, co-products in $\mathbf{CGWH}$ are topological, and products in $\mathbf{CGWH}$ are computed in $\mathbf{CG}$. We observe that $Y$ is also the push-out in $\mathbf{CGWH}$ of the following two maps:

$$
p \coprod \mathrm{id}_X : P \coprod X \to Z \coprod X, \quad \phi_q : P \coprod X \to X \tag{E.2.3.8}
$$

where $\phi_q$ is defined to be $q$ on $P$ and the identity on $X$. Since $\phi_q$ is submersive and $p \coprod \mathrm{id}_X$ is a closed immersion, we may rename $P \coprod X$ as $P$, $Z \coprod X$ as $Z$, $\phi_q$ as $q$ and $p \coprod \mathrm{id}_X$ as $p$, and assume that $q$ is, in addition, submersive.

## PDF page 860

**860** · **CHAPTER E. TOPOLOGICAL STACKS**

We define:

$$
Y' := X' \coprod_{q',P',p'} Z', \tag{E.2.3.9}
$$

with associated continuous maps $f' : X' \to Y'$ and $g' : Z' \to Y'$. Given $R' := \Delta_{X'}(X') \coprod P' \coprod P' \coprod \Delta_{Z'}(Z')$, with the continuous map $r : R' \to (X' \coprod Z') \times_0 (X' \coprod Z')$ defined as $\Delta_{X'}$ on the first component, $(p', q') \circ \Delta_{P'}$ on the second, $(q', p') \circ \Delta_{P'}$ on the third and $\Delta_{Z'}$ on the fourth, we call $R$ the set-theoretic image $r(R')$ of $R'$ in $(X' \coprod Z') \times_0 (X' \coprod Z')$. We endow $r(R')$ with the subspace topology. We now describe $R$ explicitly. Calling:

$$
W_1 := \{(a, x) \mid a \in p'(P'),\, x = q'(b),\, p'(b) = a\},\, W_2 := \{(a, b) \in X' \times_0 Z' \mid (b, a) \in W_1\} \tag{E.2.3.10}
$$

where $W_1$ is the set-theoretic image in $Z' \times_0 X'$ of $P'$ under $(p', q') \circ \Delta_{P'}$, and $W_2$ is the set-theoretic image in $X' \times_0 Z'$ of $P'$ under $(q', p') \circ \Delta_{P'}$. We endow $W_1$ and $W_2$ with the subspace topologies, and we have:

$$
R = \Delta_{X'}(X') \coprod W_1 \coprod W_2 \coprod \Delta_{Z'}(Z') \tag{E.2.3.11}
$$

as subspaces of $(X' \coprod Z') \times_0 (X' \coprod Z')$. We now note that $X'$, $Z'$ and $P'$ are weakly Hausdorff by assumption. By part (2) of Lemma E.2.1.6, $\Delta_{X'}(X')$ and $\Delta_{Z'}(Z')$ are $k$-closed in $X' \times_0 X'$, respectively $Z' \times_0 Z'$. Since these products are closed in $(X' \coprod Z') \times_0 (X' \coprod Z')$, we deduce that $\Delta_{X'}(X')$ and $\Delta_{Z'}(Z')$ are $k$-closed in $(X' \coprod Z') \times_0 (X' \coprod Z')$. We now check that $W_1$ from (E.2.3.10) is $k$-closed in $Z' \times_0 X'$. If so, then $W_2$ from (E.2.3.10) is also $k$-closed in $X' \times_0 Z'$, and we shall deduce from (E.2.3.11) that $R$ is $k$-closed in $(X' \coprod Z') \times_0 (X' \coprod Z')$. To check that $W_1$ is $k$-closed in $Z' \times_0 X'$, first observe that the set-theoretic image of $(p', q') : P' \times_0 P' \to Z' \times_0 X'$ is $p'(P') \times_0 X'$, since $q'$ is surjective. By submersiveness of $q'$, the topology on such a set-theoretic image is un-ambiguous, since the quotient topology is equivalent to the subspace topology, which in turn is the product topology of the subspace topology on $p'(P')$ with the intrinsic topology on $X'$, since $p'$ is an immersion. Equivalently, the map $(p', q')$ is strict.

Since $p'$ is a closed immersion, $p'(P')$ is a closed subspace of $Z'$, and $p'(P') \times_0 X'$ is a closed subspace of $Z' \times_0 X'$. We now note that $(p', q')$ is injective, and hence, being strict, it is a topological embedding (i.e. an immersion). It follows that $(p', q')$ is a closed map. The image $W_1$ of the $k$-closed $\Delta_{P'}(P') \subset P' \times_0 P'$ is $k$-closed in $Z' \times_0 X'$ since it is contained in the closed $P' \times_0 X'$ as the graph $\Gamma_{q'}(P') = (q', \mathrm{id}_{X'})^{-1}(\Delta_{X'}(X'))$ with $\Delta_{X'}(X') \subset X' \times_0 X'$ a $k$-closed subset since $X'$ is weakly Hausdorff. We have proved that $R$ is $k$-closed in $(X' \coprod Z') \times_0 (X' \coprod Z')$.

Since, by Corollary E.2.2.9, products in $\mathbf{CGWH}$ are computed in $\mathbf{CG}$ and co-products in $\mathbf{CGWH}$ are computed in $\mathbf{Spaces}$, and since by Lemma E.1.2.2 products in $\mathbf{CG}$ are computed upon evaluating the functor $k(\cdot)$ of Lemma E.1.2.1 on topological products, we have:

$$
k((X' \coprod Z') \times_0 (X' \coprod Z')) = (X' \coprod Z') \times (X' \coprod Z')
$$

and this topological space is weakly Hausdorff since $X'$ and $Z'$ are, we therefore deduce that $k(R)$ is closed in $(X' \coprod Z') \times (X' \coprod Z')$, and that, by Lemma E.2.1.11, $k(Y')$ is therefore weakly Hausdorff. As $Y'$ is compactly generated, as a quotient of the compactly generated space $X' \coprod Z'$, we deduce that we have $k(Y') = Y'$, and hence $Y' = u_{\mathrm{cgwh}}(Y)$. This proves that the push-out of $(p, q)$ in $\mathbf{CGWH}$ is computed in $\mathbf{Spaces}$.

We now check, using the above explicit description of $R$, that $f'$ is a closed immersion. Since $f'$ is a continuous injection, it is the same to show $f'$ is closed. Calling $t : X' \coprod Z' \to Y'$ the quotient map by $R$ and $i : X' \to X' \coprod Z'$ the inclusion, we have $f' = t \circ i$ and for any $C \subset X'$ closed we have $t^{-1}(f'(C)) = C \coprod (q')^{-1}(C)$ which is closed, hence $f'(C)$ is closed as $t$ is a submersive map.

To prove part (1), we observe that the fibre product of $f$ and $g$ in $\mathbf{CGWH}$ can be computed in $\mathbf{Spaces}$ by Lemma E.2.3.9, which is now applicable as $f'$ is a closed immersion. To prove part (2), we observe that to check that $P = X \times_{f,Y,g} Z$ in $\mathbf{CGWH}$, by part (1) and the assertion that the push-out of $f, g$ in $\mathbf{CGWH}$ can

## PDF page 861

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **861**

be computed in $\mathbf{Spaces}$ (proved in the foregoing) it is enough to check that the push-out in $\mathbf{Spaces}$ of the continuous maps $f, g$, and the topological fibre product of $f, g$, agree, which is seen by direct inspection. $\square$

The following example is [LGL, Appendix A, p. 168], and it exhibits a push-out in $\mathbf{CGWH}$ whose underlying topological space is not a push-out in $\mathbf{Spaces}$:

**Example E.2.3.11.** We let $P := [-1, 1] - \{0\}$ endowed with the subspace topology inherited from the Euclidean topology on $\mathbf{R}$, we call $p : P \to [-1, 1] =: Z$ the open immersion, with $[-1, 1]$ also endowed with the subspace topology inherited from the Euclidean topology on $\mathbf{R}$, and $q : P \to \{-1, 1\} =: X$ the submersive map identifying $[-1, 0)$ to $-1$ and $(0, 1]$ to $1$. The push-out $Y' := X \coprod^0_{q,P,p} Z$ in $\mathbf{Spaces}$ is a space with three points, only one of the three being a closed point (in the closure of the other two points). The space $Y := h(Y')$ is therefore made of a single closed point and computes the push-out $X \coprod_{q,P,p} Z$ in $\mathbf{CGWH}$. We note that the push-out of $p$ is not only not an immersion, but not even injective. In other words, Lemma E.2.3.10 does not hold if one drops the assumption on $p$ being a closed immersion.

We refer the reader to Example E.2.2.7 (which is [Du, Appendix 2, Example 2, p. 422]) for an example of a colimit in $\mathbf{Spaces}$ of a small directed system of compactly generated and Hausdorff spaces that is not weakly Hausdorff and therefore does not compute the colimit internal to $\mathbf{CGWH}$.

The following example illustrates the advantage of working within the category $\mathbf{CGWH}$ as opposed to the category of compactly generated Hausdorff spaces considered in [Ste]:

**Example E.2.3.12.** We let $Z$ be a compactly generated non-regular Hausdorff topological space (for an explicit example of a non-regular Hausdorff topological space that is compactly generated, we refer the reader to [StSe, Part II, 78]), and $p : P \to Z$ the closed immersion of a closed subspace witnessing the non-regularity of $Z$. We let $X$ be a point, and $q : P \to X$ the quotient map collapsing $P$ to a single point. While Lemma E.2.3.10 does still ensure that in $\mathbf{Spaces}$ the push-out $X \coprod_{q,P,p} Z$ is compactly generated weakly Hausdorff and computes the push-out $X \coprod_{q,P,p} Z$ in $\mathbf{CGWH}$, the topological push-out is non-Hausdorff, even though $X, P, Z$ are compactly generated and Hausdorff and $p$ is a closed immersion. Indeed, such push-out is $Z/P$, and any point $z \in Z$ that cannot be separated from the closed subspace $P$, has image in $Z/P$ that cannot be separated from the point induced as the image of $P$ in the quotient.

This clarifies the advantage of weakening the Hausdorff condition considered in [Ste] to a weak Hausdorff separation condition. Namely, while arbitrary topological colimits of compactly generated weakly Hausdorff spaces may not compute the internal colimit in $\mathbf{CGWH}$, as illustrated by Example E.2.3.11, push-outs in $\mathbf{CGWH}$ along closed immersions can indeed be computed in $\mathbf{Spaces}$. Within the category of compactly generated Hausdorff spaces of [Ste], not even these can be computed in $\mathbf{Spaces}$.

**Remark E.2.3.13.** We observe that the submersive map $f : Z \to Y := X \coprod^0_{q,P,p} Z$ in $\mathbf{Spaces}$ obtained as the push-out in $\mathbf{Spaces}$ of the submersive map $q$ in Example E.2.3.12, is not open.$^{9}$ This illustrates the additional degree of flexibility of incorporating the weak Hausdorff separation assumption on compactly generated spaces, as opposed to the Hausdorff condition. Indeed, quotients of compactly generated weakly Hausdorff spaces by closed equivalence relations are compactly generated weakly Hausdorff by Lemma E.2.1.11, while the analogous result does not hold upon replacing the weak Hausdorff condition with the Hausdorff condition. It only holds if, in addition,$^{10}$ the quotient map is open.

We conclude this section by discussing a result that provides a concrete characterization of several important classes of morphisms in $\mathbf{CGWH}$. In light of Example E.1.2.16, this is, in turn, an advantage of the category $\mathbf{CGWH}$ over the category $\mathbf{CG}$. First we recall a definition:

---

$^{9}$why not open?

$^{10}$why sufficient? Do we care? Maybe omit this final sentence.

## PDF page 862

**862** · **CHAPTER E. TOPOLOGICAL STACKS**

**Definition E.2.3.14.** In a category $\mathcal{C}$, an epimorphism is called *regular* if and only if it is the co-equalizer of a pair of morphisms, and a monomorphism is called *regular* if and only if it is the equalizer of a pair of morphisms.

If $\mathcal{C}$ contains all small limits and colimits, an epimorphism in $\mathcal{C}$ is called *effective* if and only if it is the co-equalizer of its own kernel pair, and is called *universally effective* if this property holds after arbitrary pull-back. A monomorphism $X \to Y$ is called *effective* if and only if $X \to Y \times_Q Y$ is an isomorphism, for the pushout $Q$ of the two copies $X \rightrightarrows Y$ of the given monomorphism.$^{11}$ We say $\mathcal{C}$ is *regular* if every pull-back of a regular epimorphism is a regular epimorphism (see [Bor2, Def. 2.1.1]).

**Proposition E.2.3.15.** *We have:*

*(1) The monomorphisms in $\mathbf{CGWH}$ are the injective continuous maps.*

*(2) The epimorphisms in $\mathbf{CGWH}$ are the continuous maps with dense image.*

*(3) The regular monomorphisms in $\mathbf{CGWH}$ are the closed immersions.*

*(4) The regular epimorphisms in $\mathbf{CGWH}$ are the submersive maps.*

*(5) The effective monomorphisms in $\mathbf{CGWH}$ are the closed immersions.*

*(6) The effective epimorphisms in $\mathbf{CGWH}$ are the submersive maps.*

*(7) The universally effective epimorphisms in $\mathbf{CGWH}$ are the submersive maps.*

*(8) The isomorphisms in $\mathbf{CGWH}$ are the homeomorphisms.*

*(9) Monomorphisms in $\mathbf{CGWH}$ are stable under products, co-products and compositions.*

*(10) Regular monomorphisms in $\mathbf{CGWH}$ are stable under products, co-products and compositions.*

*(11) Epimorphisms in $\mathbf{CGWH}$ are stable under finite products, co-products and compositions.*

*(12) Regular epimorphisms in $\mathbf{CGWH}$ are stable under finite products, co-products and compositions.*

*(13) Every morphism in $\mathbf{CGWH}$ is universally the composition of a regular epimorphism followed by a monomorphism.*

*(14) $\mathbf{CGWH}$ is a regular category.*

Within $\mathbf{CGWH}$, it is our convention to refer to a pull-back as a *base-change*. Regularity for $\mathbf{CGWH}$ implies several structural properties for continuous maps between compactly generated weakly Hausdorff spaces that will not hold for general topological spaces, following from [Bor2, Ch. 2, Thm. 2.1.3]. In particular, within $\mathbf{CGWH}$ *any continuous map factors as a submersive map followed by a continuous injective map, and the factorization is unique up to homeomorphism, which implies that it is preserved by base-change.* While we will not rely on regularity of $\mathbf{CGWH}$, but only indirectly and with no necessity to appeal to the general theory around the concept, we will use stability of submersive maps under arbitrary base change systematically.

Lemma E.2.3.8 identifies the regular epimorphisms in $\mathbf{CGWH}$ as exactly the submersive maps, since Lemma E.2.3.6(6) proves stability of submersive maps under arbitrary base change, and such stability implies regularity of $\mathbf{CGWH}$, so we are implicitly using regularity of $\mathbf{CGWH}$. This should further motivate the choice of $\mathbf{CGWH}$ as the category of “convenient” topological spaces of reference.

The assertion analogous to Proposition E.2.3.15(7) does not hold for $\mathbf{CG}$ (and hence for $\mathbf{Spaces}$) as illustrated by Example E.1.2.16, which exhibits an example of a submersive map whose base change in $\mathbf{CG}$ is not submersive.

We further mention that, in fact, $\mathbf{CGWH}$ is also a co-regular category: see [Str, §3, Thm. 3.1] for a discussion on the co-regularity of $\mathbf{CGWH}$, which ultimately amounts to combining [Bou-GT, §3, 3.5] with Lemma E.2.3.10 and Lemma E.2.2.5.

Before we prove Proposition E.2.3.15, we introduce the following auxiliary construction, to be used in the argument.

---

$^{11}$Check this definition is correct.

## PDF page 863

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **863**

**Construction E.2.3.16.** Let $X$ be a compactly generated weakly Hausdorff space, $Z \subset X$ a closed subspace, and denote by $i : Z \to X$ the closed immersion. We denote by $\{*\}$ a point endowed with the discrete topology. We let $a : Z \to \{*\}$ be the unique map to a point in $\mathbf{CGWH}$, and extend $i$ to a closed immersion $i : \{*\} \coprod Z \to \{*\} \coprod X$. We call

$$
(X/Z)_* := \{*\} \coprod_{a, \{*\} \coprod Z, i} (\{*\} \coprod X) \tag{E.2.3.12}
$$

the push-out formed in $\mathbf{CGWH}$, and we denote by $x$ the continuous map $\{*\} \to (X/Z)_*$. We denote by $q$ the map

$$
q : X \to (X/Z)_* \tag{E.2.3.13}
$$

obtained as the composition of the open and closed immersion $X \to \{*\} \coprod X$ followed by the map $b : \{*\} \coprod X \to (X/Z)_*$ induced in the quotient by $a$. We further define the continuous map

$$
p : X \to (X/Z)_* \tag{E.2.3.14}
$$

to be the constant map obtained as the composition of the unique continuous map $X \to \{*\}$ followed by $x$.

We now collect some properties of $(X/Z)_*$, $q$, $p$ and $x$ to be used in the proof of Proposition E.2.3.15.

**Lemma E.2.3.17.** *Let $X$ be a compactly generated weakly Hausdorff space, $Z \subset X$ a closed subspace. We let $(X/Z)_*$ be as in (E.2.3.12), $q$ the map from (E.2.3.13) and $p$ the map from (E.2.3.14).*

*(1) The map $q$ is a closed submersion when $Z$ is non-empty.*

*(2) The push-out defining $(X/Z)_*$ in (E.2.3.12) can be computed in $\mathbf{Spaces}$, and we have:*

$$
\{*\} \coprod Z = \{*\} \times_{x,(X/Z)_*,q} (\{*\} \coprod X) \tag{E.2.3.15}
$$

*in $\mathbf{CGWH}$. Moreover, $\{*\} \coprod Z = \{*\} \times_{x,(X/Z)_*,q} (\{*\} \coprod X)$ is compactly generated and computes in $\mathbf{Spaces}$ the fibre product in $\mathbf{CGWH}$.*

*(3) If $Z$ is non-empty, we have*

$$
Z = \{*\} \times_{x,(X/Z)_*,q} X \tag{E.2.3.16}
$$

*in $\mathbf{CGWH}$. Moreover, $\{*\} \times^0_{x,(X/Z)_*,q} X$ is compactly generated and computes in $\mathbf{Spaces}$ the fibre product in $\mathbf{CGWH}$.*

*(4) We have:*

$$
X = \{*\} \times_{x,(X/Z)_*,p} X \tag{E.2.3.17}
$$

*Moreover, we have $p^{-1}(\{x\}) = X$ and, if $Z$ is non-empty, $q^{-1}(\{x\}) = Z$.*

*Proof.* The following diagram is useful to consult during the proof that follows (with $i : \{*\} \coprod Z \to \{*\} \coprod X$ the natural closed immersion):

```latex
\begin{tikzcd}
Z \arrow[r] \arrow[d, "i"'] & \{*\} \coprod Z \arrow[r, "a"] \arrow[d, "i"] & \{*\} \arrow[d] \\
X \arrow[r] \arrow[rr, "q"', bend right] & \{*\} \coprod X \arrow[r, "b"] & (X/Z)_*
\end{tikzcd}
```

By Lemma E.2.3.10(1), the push-out defining $(X/Z)_*$ can be computed in $\mathbf{Spaces}$. This gives the first assertion in (2), which we shall now use to prove the assertion in (1). The map $b : \{*\} \coprod X \to (X/Z)_*$ induced in the quotient by $a$ is submersive since Lemma E.2.3.10 ensures $(X/Z)_*$ is a topological quotient of $(\{*\} \coprod X) \coprod \{*\}$.

## PDF page 864

**864** · **CHAPTER E. TOPOLOGICAL STACKS**

In particular, given an arbitrary topological space $T$ and a set-function $g : (X/Z)_* \to T$, $g$ is continuous if and only if $g \circ b$ is. On the other hand, $g \circ b$ is continuous on $\{*\} \coprod X$ if and only if it is on $X$. As the image of $x$ is in the image of $q$ when $Z$ is non-empty, we deduce that $q$ is surjective when $Z$ is non-empty, so it is submersive. To verify $q$ is also closed, by submersiveness it suffices to show $q^{-1}(q(C))$ is closed in $X$ for all closed $C \subset X$. This holds because for any subset $C \subset X$ we have $q^{-1}(q(C)) = C$ when $C$ is disjoint from $Z$ and $q^{-1}(q(C)) = C \cup Z$ when $C$ meets $Z$.$^{12}$

We next prove the rest of (2). By Lemma E.2.3.10(2), we have the identification in (E.2.3.15) and that such identification remains valid in $\mathbf{Spaces}$. We prove (3). The same argument as for (2) applies to (E.2.3.16) since if $Z$ is non-empty then $(X/Z)_*$ is also the push-out of the closed immersion $i : Z \to X$ and the unique map $Z \to \{*\}$. Part (4) follows from the very definition of $p$ from (E.2.3.14), and the last assertion $p^{-1}(\{x\}) = X$ and $q^{-1}(\{x\}) = Z$ is a reformulation of (3) and (4). $\square$

We now prove Proposition E.2.3.15.

*Proof of Proposition E.2.3.15.* We prove (1). Let $f : X \to Y$ be a monomorphism. Then $f_* : \mathrm{C}(T, X) \to \mathrm{C}(T, Y)$ is injective for all $T$ in $\mathbf{CGWH}$. Upon choosing $T = \{*\}$ a point, we have $\mathrm{C}(T, X) = X^{\mathrm{set}}$ and $\mathrm{C}(T, Y) = Y^{\mathrm{set}}$, so we deduce $f$ is injective. Conversely if $f$ is injective then $f_*$ is also injective, so (1) is proved. We prove (2). Let $f : X \to Y$ be a continuous map of compactly generated weakly Hausdorff spaces, $T$ a compactly generated weakly Hausdorff space, and $g, g' : Y \rightrightarrows T$ arbitrary continuous maps co-equalized by $f$. Then we have:

$$
\mathrm{eq}(g, g') := Y \times_{g,T,g'} Y = (g, g')^{-1}(\Delta_T(T)) \subset Y.
$$

The second identification holds as subspaces of $Y \times Y$, the product indeed being internal to $\mathbf{CGWH}$, as the subspace topology on $(g, g')^{-1}(\Delta_T(T)) \subset Y \times Y$ is compactly generated since $(g, g')^{-1}(\Delta_T(T))$ is $k$-closed in $Y \times_0 Y$ because $\Delta_T(T)$ is $k$-closed in $T \times_0 T$ and $(g, g')$ is continuous. We observe that the image of $f$ is contained in $\mathrm{eq}(g, g')$. Since $\mathrm{eq}(g, g')$ is closed, $g = g'$ if $f$ has dense image. We now assume conversely that $f$ is an epimorphism. This forces $X$ to be non-empty if $Y$ is non-empty (as we may assume) since the two natural maps $Y \rightrightarrows Y \coprod Y$ are distinct for non-empty $Y$. In particular, the closure $Z$ of the image of $f$ is non-empty. Consider the maps $p, q : Y \rightrightarrows (Y/Z)_*$ provided by Construction E.2.3.16. The map $f$ equalizes $p$ and $q$, and since it is an epimorphism we deduce $p = q$ and hence, in the notation of Lemma E.2.3.17, $p^{-1}(\{x\}) = Y$ and $q^{-1}(\{x\}) = Z$ must be equal, forcing $Z = Y$. This means that $f$ has dense image, and (2) is proved.

We prove (3). Suppose $i : Z \to X$ is a closed immersion. Then $i$ is the equalizer of $(p, q) : X \to (X/Z)_*$ from Construction E.2.3.16 (even when $Z$ is empty), and hence it is a regular monomorphism. Conversely, regular monomorphisms are closed immersions, as they are continuous pre-images of diagonal subspaces, and these are closed in every object of $\mathbf{CGWH}$. Part (4) follows from Lemma E.2.3.8. We now prove (5). Since $\mathbf{CGWH}$ contains equalizers and co-kernel pairs, a monomorphism in $\mathbf{CGWH}$ is effective if and only if it is regular, and hence (5) follows from (3). Part (6) follows from Lemma E.2.3.8, and (7) follows from (6) and Lemma E.2.3.6(6).

To prove (8) it is enough to observe that isomorphisms are regular epimorphisms and monomorphisms, and by (4) and (1) these are the bijective submersive maps, hence the homeomorphisms. Part (9) follows from (1), and (10) follows from (3). For (11) and (12), the only delicate aspect$^{13}$ is stability of regular epimorphisms under finite products. By (4), this follows from Lemma E.2.3.6(6). Finally, part (13) is a formal consequence of the fact that $\mathbf{CGWH}$ is closed under finite limits (see Lemma E.2.2.5(1)) and finite colimits (see Lemma E.2.2.5(2)), and that regular epimorphisms are stable under arbitrary base change (see (4) and Lemma E.2.3.6).

---

$^{12}$check this verification of closedness of $q$, attentive to effect of the functor $h$, since closedness proof was omitted before.

$^{13}$Why for (11) – just usual epimorphism – is this the case? Can you use (4) somehow? Must clarify.

## PDF page 865

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **865**

These three conditions say that $\mathbf{CGWH}$ is a *regular category* (see [vO, Def. 4.1] and [Bor2, Ch. 2, Def. 2.1.1]), so by [vO, Prop. 4.2]$^{14}$ this proves (14). $\square$

**E.2.4. Counter-examples on compact generation and separation conditions.** In this subsection we collect a number of examples illustrating the necessity of assumptions being made throughout the previous sections. We also highlight key differences between the definition of compact generation for spaces adopted throughout this work, and other definitions present within the literature. We focus specifically on the following two, apart from the one adopted throughout this appendix (see Definition E.1.1.7):

**Definition E.2.4.1.** Let $X$ be a topological space. We say:

(1) $X$ is a *Kelley compactly generated space* if and only if for any subspace $U \subset X$, $U$ is open if and only if for any compact subspace $K \subset X$, $U \cap K$ is open in $K$.

(2) $X$ is a *Steenrod compactly generated space* if and only if for any subspace $U \subset X$, $U$ is open if and only if for any compact Hausdorff subspace $K \subset X$, $U \cap K$ is open in $K$.

We have the following simpler analog for Kelley compact generation of Lemma E.1.1.3, which we record here to aid in the construction of examples:

**Lemma E.2.4.2.** *Let $X$ be a topological space. Then the following conditions are equivalent:*

*(1) $X$ is Kelley compactly generated.*

*(2) For any topological space $Y$ and set-function $f : X \to Y$, the following conditions are equivalent:*

*(a) $f$ is continuous.*

*(b) For any compact subspace $K \subset X$ immersed through $i : K \to X$, the composition $f \circ i$ is continuous.*

*(3) A subspace $U \subset X$ is open if and only if for any compact topological space $K$ and any continuous map $g : K \to X$, $g^{-1}(U)$ is open in $K$.*

*(4) There exists a set $I$, a compact topological space $K_i$ for each $i \in I$, and for $Y := \coprod_{i \in I} K_i$ the $I$-indexed co-product topological space, a submersive map $q : Y \to X$.*

*Proof.* We prove that (1) and (2) are equivalent. For any topological space $Y$ and set-function $f : X \to Y$, if $f$ is continuous then part (b) of (2) also holds. Conversely, if part (b) of (2) holds for all $(K, i)$ then for any open subspace $V \subset Y$, by writing $U := f^{-1}(V)$, for any compact subspace $K \subset X$ immersed through $i : K \to X$ we see that $(f \circ i)^{-1}(V)$ is open in $K$ by continuity of $f \circ i$ and we have $U \cap K = (f \circ i)^{-1}(V)$. By (1), $U$ is open in $X$, forcing $f$ to be continuous. This proves (2) assuming (1). Conversely, if (2) holds, then we choose $Y$ to be the topological space whose underlying set is $X^{\mathrm{set}}$, and whose topology is the coarsest topology such that every subset $Z$ for which $K \cap Z$ is closed in $K$ is itself closed in $Y$. We let $f$ be the identity set-function. By (2), $f$ is continuous. Since the topology of $Y$ on $X^{\mathrm{set}}$ is finer than that of $X$, $f^{-1}$ is also continuous, and hence $f$ is a homeomorphism. This shows (2) implies (1).

Since (3) implies (1) as a consequence of the definitions, we prove the converse. If (1) holds, we let $K$ be an arbitrary compact topological space and $g : K \to X$ an arbitrary continuous map. Then $g$ factors as $g = i \circ g'$ where $i$ is the immersion of the image $K' := g(K) \subset X$, and $g' : K \to K'$ is continuous and surjective. Clearly $K'$ is a compact subspace of $X$. If the intersection of $U$ with any compact subspace $K' \subset X$ is open, then $g^{-1}(U) = (g')^{-1}(U \cap K')$ is open in $K$ and hence $U$ is open. Thus, (1) and (3) are therefore equivalent.

We now assume (2). We let $I$ be the set of all compact subspaces of $X$. For $i \in I$, we denote $K_i$ the corresponding compact subspace of $X$, and $g_i : K_i \to X$ the immersion. Upon writing $Y := \coprod_{i \in I} K_i$ and $q := \coprod_{i \in I} g_i$, the map $q : Y \to X$ is continuous and surjective. Moreover, for any topological space $Z$ and any set-function $f : X \to Z$, by part (2) the map $f$ is continuous if and only if $f \circ q$ is continuous. By [Bou-GT, Ch. I, §4, Prop. 6], $q$ is submersive, and (4) is proved. Conversely, we assume that (4) holds. We let $U \subset X$ be

---

$^{14}$why citing for verifying a *definition*?

## PDF page 866

**866** · **CHAPTER E. TOPOLOGICAL STACKS**

a subspace such that for any compact subspace $K \subset X$, $U \cap K$ is open in $K$. Then, $U \cap q(K_i)$ is open in the compact subspace $q(K_i)$ for every $i \in I$, which forces $q^{-1}(U)$ to be open in $Y$. As $q$ is submersive, $U$ is open in $X$, hence $X$ is Kelley compactly generated. $\square$

We will now show by example that the two concepts of compact generation introduced in Definition E.2.4.1 are not equivalent to one another, nor are they equivalent to compact generation as defined in Definition E.1.1.7 and throughout this appendix. We first establish a result in the affirmative:

**Lemma E.2.4.3.** *Let $X$ be a topological space. We have:*

*(1) If $X$ is Steenrod compactly generated, then it is compactly generated.*

*(2) If $X$ is compactly generated, then it is Kelley compactly generated.*

*Proof.* Assume that $X$ is Steenrod compactly generated, and let $U \subset X$ be a subspace. We assume that for any compact Hausdorff space $K$ and any continuous map $g : K \to X$, $g^{-1}(U)$ is open in $K$. In particular, this holds as $(K, g)$ range over all compact Hausdorff subspaces of $X$, $g$ being the immersion of such subspace. As $X$ is Steenrod compactly generated, $U$ is open, proving that $X$ is compactly generated in the sense of Definition E.1.1.7, and (1) follows. If $X$ is compactly generated, then by part (4) of Lemma E.1.1.3 there exists a set $I$ and for every $i \in I$ a compact Hausdorff space $K_i$, with a submersive map $q : \coprod_{i \in I} K_i \to X$. By the equivalence of parts (4) and (1) of Lemma E.2.4.2 above, $X$ is Kelley compactly generated. $\square$

We now examine the following example:

**Example E.2.4.4.** We let $Y := \mathbf{Q}$ be the rational numbers equipped with the subspace topology induced by the inclusion $\mathbf{Q} \subset \mathbf{R}$, the reals being endowed with their Euclidean topology. We define $X := Y^+$ to be the one-point compactification of $Y$. Since every neighborhood of the point $X - Y$ has non-empty intersection with every non-empty open subspace of $X$, $X$ is non-Hausdorff. It is, however, weakly Hausdorff, as any compact subspace of $X$ is closed. We refer the reader to [StSe, Part II, 35] for a discussion of further properties of this example.

The following Lemma illustrates how the assumption in Lemma E.2.1.4 concerning the existence of a continuous surjection from a compact Hausdorff space, cannot be dropped. It also illustrates how the weak Hausdorff separation condition is genuinely weaker than the Hausdorff separation condition.

**Lemma E.2.4.5.** *There exists an example of a compact, compactly generated, weakly Hausdorff space that is not Hausdorff.*

*Proof.* We let $X$ be the topological space from Example E.2.4.4. Then $X$ is compact and weakly Hausdorff. It is also compactly generated by Lemma E.1.2.21, since it is sequential (see [StSe, Part II, 35]). It is, however, non-Hausdorff. $\square$

We consider the following:

**Example E.2.4.6.** The Sierpiński space $S$ is the topological space whose underlying set is $\{0, 1\}$ and whose topology $\tau$ is the collection of subsets of $S$:

$$
\{\varnothing, \{1\}, S\}.
$$

**Lemma E.2.4.7.** *There exists a compactly generated space that is not Steenrod compactly generated.*

*Proof.* The space $S$ from Example E.2.4.6 is compactly generated by Lemma E.1.2.21, as every finite space is sequential. On the other hand, it is not Steenrod compactly generated, as the only compact Hausdorff subspaces $K$ of $S$ are the one-element sets $\{0\}$ and $\{1\}$, and any subset $Z \subset S$ satisfies $Z \cap K$ is closed in $K$. As the topology on $S$ is not discrete, $S$ is not Steenrod compactly generated. $\square$

## PDF page 867

**E.2. COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **867**

We point out in the following Lemma that for Hausdorff topological spaces there is no discrepancy among the various notions of compact generation reviewed here, and hence no potential for ambiguity as to which one is being referred to:

**Lemma E.2.4.8.** *Let $X$ be a Hausdorff topological space. Then the following conditions are equivalent:*

*(1) $X$ is Kelley compactly generated.*

*(2) $X$ is compactly generated.*

*(3) $X$ is Steenrod compactly generated.*

*Proof.* We just need to show (1) implies (3). We’ll show (1) $\Rightarrow$ (2) $\Rightarrow$ (3). Assume (1). By Lemma E.2.4.2(4), there exists a set $I$, for every $i \in I$ a compact space $K_i$, and a submersive map $q : \coprod_{i \in I} K_i \to X$. As $X$ is Hausdorff, the compact $K'_i := q(K_i)$ is Hausdorff too. We denote by $g_i : K'_i \to X$ the immersion, and by $q' := \coprod_{i \in I} g_i$ the co-product map $\coprod_{i \in I} K'_i \to X$. The map $q'$ is continuous and surjective by design. As $q$ is submersive, so is $q'$, and hence $X$ is compactly generated by Lemma E.1.1.3. We now assume that (2) holds, and prove (3). By Lemma E.1.1.3(4), there exists a set $I$ and for every $i \in I$ a compact Hausdorff space $K_i$, and a submersive map $q : \coprod_{i \in I} K_i \to X$. We write $K'_i := q(K_i)$. This is compact and Hausdorff. Upon calling $g_i : K'_i \to X$ the immersion, then:

$$
q' := \coprod_{i \in I} g_i : \coprod_{i \in I} K'_i \to X
$$

is submersive, since $q$ is. Let $U \subset X$ be a subspace such that its intersection with every compact Hausdorff subspace $K$ of $X$ is open in $K$. In particular, $U \cap K'_i$ is open in $K'_i$ for every $i \in I$. This implies that $(q')^{-1}(U)$ is open in $\coprod_{i \in I} K'_i$, and as $q'$ is submersive, $U$ is open in $X$. We deduce that $X$ is Steenrod compactly generated. The Lemma is proved. $\square$

The following lemma illustrates how, upon dropping the Hausdorff assumption in Lemma E.2.1.4, topological products of a compact weakly Hausdorff space and a compactly generated (weakly) Hausdorff space may not be compactly generated.

**Lemma E.2.4.9.** *There exists an example of a topological space $X$ such that:*

*(1) $X$ is compact, compactly generated weakly Hausdorff (and not Hausdorff),*

*(2) $X \times_0 X$ is not compactly generated.*

*Proof.* We let $Y$ be the rational numbers endowed with the subspace topology inherited from the Euclidean topology on $\mathbf{R}$, and $X := Y^+$ the one-point compactification as in Example E.2.4.4. Then $X$ is weakly Hausdorff and compact. It is also compactly generated, as it is sequential (see [StSe, Part II, 35]). If $X \times_0 X$ was compactly generated then $X \times X = k(X \times_0 X)$ would coincide with $X \times_0 X$ (i.e., $k$-closed is the same as closed in $X \times_0 X$). Since $X$ is weakly Hausdorff, the diagonal subspace $\Delta_X(X)$ would then be closed in $X \times_0 X$ (see Lemma E.2.1.6), so $X$ would be Hausdorff, a contradiction. $\square$

We consider the following:

**Example E.2.4.10.** We let $Y$ be a topological space such that:

(1) $Y$ is $T_1$.

(2) Every compact subspace of $Y$ is finite and discrete.

(3) $Y$ is non-discrete.

Then the one-point compactification $X := Y^+$ is an example of a compact non-discrete space equipped with an open subspace all of whose compact subspaces are finite. Examples of spaces such as $Y$ can be found in [StSe, Part II, 25, 26].

## PDF page 868

**868** · **CHAPTER E. TOPOLOGICAL STACKS**

Lemma E.2.4.11. *There exists an example of a Kelley compactly generated space that is not compactly generated.*

Proof. Indeed, the space $X$ is Example E.2.4.10 is an example of a Kelley compactly generated space (since $Y$ is $T_1$ and $X-Y$ is a closed point) and we claim it is not compactly generated. If it was compactly generated then by Lemma E.1.2.25(2) every open subspace of $X$ would have to be compactly generated, whereas $Y$ is not (since $k(Y)$ is discrete but $Y$ is not discrete). $\square$

Lemma E.2.4.12. *There exists an example of a topological space $X$ and an open subspace $U\subset X$ such that*

*(1) $X$ is Kelley compactly generated.*

*(2) $U$ is not Kelley compactly generated.*

Proof. Let $X$ be the topological space from Example E.2.4.10. Then $X$ is Kelley compactly generated as noted in the proof of Lemma E.2.4.11. On the other hand, upon choosing $U:=Y$ as in the Example, $Y$ is not compactly generated (also seen in the proof of Lemma E.2.4.11).$^{15}$ $\square$

Compact generation is inherited by open subspaces by Lemma E.1.2.25, whereas by Lemma E.2.4.12 Kelley compact generation is not.

E.3. Small compactly generated weakly Hausdorff spaces

E.3.1. Preparations on small index categories and small compact Hausdorff spaces. We begin, as in [SP, Tags 046U, 000H], by introducing the notion of “size” of a compactly generated weakly Hausdorff topological space.

Definition E.3.1.1. We define a function on cardinals $\kappa$:

$$
\mathrm{Bound}(\kappa):=\max\{\kappa^{\aleph_0},2^{2^{\kappa}},\kappa^{\kappa}\}. \tag{E.3.1.1}
$$

Moreover, given a compactly generated weakly Hausdorff topological space $X$, we define:

$$\mathrm{size}(X):=\max\{\aleph_0,\lambda_1,\lambda_2\}$$

where $\lambda_1$ and $\lambda_2$ are cardinal numbers defined as follows:

(1) we denote by $\Sigma_X$ the set of all compact Hausdorff subspaces $K\subset X$, and we define:

$$\lambda_1:=|\Sigma_X|.$$

(2) We define:

$$\lambda_2:=\sup\{|\mathrm{C}(K,\mathbf C)|,K\in\Sigma_X\}$$

the supremum of the cardinalities of all the $C^*$-algebras of complex-valued continuous functions on all compact Hausdorff subspaces of $X$.

Notation E.3.1.1. We write, for a topological space $X$, $\mathrm{C}(X)$ to denote the algebra of complex-valued continuous functions on $X$.

We recall the construction of the Von Neumann universes, following [Kunen, Ch. 3, §2] and [Jech, Part I, p. 64]. We also refer the reader to [SP, Tag 05N1,000B], where the constructions that follow are used to define categories of schemes, with the aim of defining sites (in the sense of [SP, Tag 00VG]) and stacks over sites on categories of schemes. Our conventions concerning sites are aligned, throughout this work, to those in [SP, Tags 00UZ, 00VG] and, in particular, we shall not be allowing large categories as the categories underlying the sites to be used.

---

$^{15}$Must show Y is not Kelley compactly generated.

## PDF page 869

**E.3. SMALL COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **869**

The discussion in the present section is aimed at constructing a small subcategory of $\mathbf{CGWH}$ stable under enough categorical operations to serve the purpose of underlying a site, over which we shall be considering stacks in groupoids. We will be, in the process, arranging for the closure of such a category under enough many small limits and colimits to ensure our concrete constructions of interest will involve spaces always contained within it.

For any ordinal $\alpha$, we construct the set $V_{\alpha}$ as follows, proceeding recursively. We define:

$$V_0:=\varnothing,\quad V_{\alpha+1}:=2^{V_{\alpha}},$$

with, recall, $2^{V_{\alpha}}$ denoting the power-set of $V_{\alpha}$, and for a limit ordinal $\alpha$ we further set:

$$V_{\alpha}:=\bigcup_{\beta<\alpha}V_{\beta},$$

determining $V_{\alpha}$ by transfinite recursion. We refer the reader to [Kunen, Ch. III, Def. 2.1] and the discussion in loc.cit. following it, for further background on the sets $V_{\alpha}$. We further refer the reader to the discussion before [Jech, Lemma 6.3]. We refer the reader to [SP, Tag 000B] and the subsequent section as well, where the $V_{\alpha}$’s are referred to as partial universes. We refer to the sets $V_{\alpha}$ as the Von Neumann’s universe of level $\alpha$. They satisfy the following properties, seen by transfinite induction (see [Kunen, Ch. III, Lemma 2.3]):

(1) each $V_{\alpha}$ is a transitive set, (2) if $\alpha\le\alpha'$ then $V_{\alpha}\subset V_{\alpha'}$. (3) $\alpha\subset V_{\alpha}$.

The union $\mathbf{WF}$ of all the $V_{\alpha}$ as $\alpha$ varies across all limit ordinals is a proper class, called the class of well-founded sets. By [Kunen, Ch. III, Lemma 2.14], ultimately resting on the Axiom Schema of Regularity and the Axiom of Choice, every set in the class of all sets, and likewise every topological space in the class of all topological spaces, is an element of $\mathbf{WF}$.

Before moving forward, we establish two preparatory results. The following lemma assumes the Axiom of Choice.

Lemma E.3.1.2. *Let $\kappa$ be a cardinal, and $\mathbf{Sets}_{\le\kappa}$ the class of all sets $J$ whose cardinality satisfies $|J|\le\kappa$. Then there exists a sub-class $\mathrm{Sets}_{\le\kappa}\subset\mathbf{Sets}_{\le\kappa}$ such that:*

*(1) $\mathrm{Sets}_{\le\kappa}$ is a set.*

*(2) For any $J\in\mathbf{Sets}_{\le\kappa}$ there exists $J'\in\mathrm{Sets}_{\le\kappa}$ and a bijective set-function $f:J'\to J$.*

Proof. Let $\lambda$ be a cardinal satisfying $\lambda\le\kappa$. By the Axiom of Choice, there exists an ordinal $\alpha$ such that $|\alpha|=\lambda$. We denote $\alpha_{\lambda}:=\inf\{\alpha\mid |\alpha|=\lambda\}$, the initial ordinal associated to $\lambda$. As $\alpha_{\lambda}\subset V_{\alpha_{\lambda}}$ and, for all cardinals $\lambda,\lambda'$ satisfying $\lambda\le\lambda'\le\kappa$, we have$^{16}$ $\alpha_{\lambda}\le\alpha_{\lambda'}\le\alpha_{\kappa}$, we deduce the containments $V_{\alpha_{\lambda}}\subset V_{\alpha_{\lambda'}}\subset V_{\alpha_{\kappa}}$ by [Kunen, Ch. III, Lemma 2.3]. We set $\mathrm{Sets}_{\le\kappa}:=V_{\alpha_{\kappa}+1}$. For any element $J$ of $\mathbf{Sets}_{\le\kappa}$, there exists a least ordinal $\alpha_{|J|}$ with $|J|=|\alpha_{|J|}|$, and we have $\alpha_{|J|}\subset V_{\alpha_{|J|}}\subset V_{\alpha_{\kappa}}$, implying $\alpha_{|J|}\in V_{\alpha_{\kappa}+1}=\mathrm{Sets}_{\le\kappa}$. In other words, there exists an element $J'\in\mathrm{Sets}_{\le\kappa}$, itself a set, and a bijection $f:J'\to J$. $\square$

Definition E.3.1.3. For a cardinal $\nu$, a $\nu$-small category is any small category $I$ whose underlying set of objects satisfies $|I|\le\nu$ and for every pair of objects $i,i'\in I$ we have $|\mathrm{Map}_I(i,i')|\le\nu$.

Building on Lemma E.3.1.2 we now prove an analog for small index categories$^{17}$. Namely, we prove that there exists a set of small categories whose sets of objects and morphisms have cardinality bounded above by a fixed arbitrary cardinal $\nu$, and such that any such small category is isomorphic to a category that is an element of such a set.

---

$^{16}$Why? Give reference or explanation.

$^{17}$The terminology “index category” is often used but never defined/described. Is it needed? Why not simply “category” and “small category”? Should clarify the meaning and rationale for using it.

## PDF page 870

**870** · **CHAPTER E. TOPOLOGICAL STACKS**

Lemma E.3.1.4. *Let $\nu$ be an infinite cardinal. There exists a set $\mathrm{Cat}_{\le\nu}$ whose elements are $\nu$-small index categories, and such that for every $\nu$-small index category there exist an element $J'\in\mathrm{Cat}_{\le\nu}$ and an isomorphism of categories $f:J'\to J$.*

We note that the lemma provides an isomorphism between $\nu$-small categories, and not merely an equivalence of categories.

Proof. We let $\mathrm{Sets}_{\le\nu}$ be the set provided by Lemma E.3.1.2. For sets $J_1,J_2$ and maps $s,t:J_1\rightrightarrows J_2$, $c:J_1\times_{s,J_2,t}J_1$, and $e:J_2\to J_1$, we define the formulas $P_i(s,t,c,e)$ for $i=1,2,3,4$ as

$$
P_1(s,t,c,e):s\circ e=t\circ e=\mathrm{id}:J_2\to J_2, \tag{E.3.1.2}
$$

$$
P_2(s,t,c,e):c(s^{-1}(y)\cap t^{-1}(x),s^{-1}(z)\cap t^{-1}(y))\subset s^{-1}(z)\cap t^{-1}(x),\ \text{for all }x,y,z\in J_2 \tag{E.3.1.3}
$$

(this encodes the two commutative diagrams in (E.4.1.1)),

$$
P_3(s,t,c,e):c(c(\cdot,\cdot),\cdot)=c(\cdot,c(\cdot,\cdot)):J_1\times_{s,J_2,t}J_1\times_{s,J_2,t}J_1\to J_1, \tag{E.3.1.4}
$$

and

$$
P_4(s,t,c,e):c((e\circ t)(\cdot),\cdot)=c(\cdot,(e\circ s)(\cdot))=\mathrm{id}:J_1\to J_1. \tag{E.3.1.5}
$$

Let $\mathbf{C}_{\le\nu}$ be the class of 6-tuples $(J_1,J_2,s,t,c,e)$ where $J_1,J_2$ are $\nu$-small sets, and $(s,t,c,e,i)$ are elements of the set:

$$(s,t,c,e,i)\in\mathrm{Map}(J_1,J_2)\times\mathrm{Map}(J_1\times_{s,J_2,t}J_1,J_1)\times\mathrm{Map}(J_2,J_1).$$

We define the class $\mathrm{Cat}'_{\le\nu}$:

$$\{(J_1,J_2,s,t,c,e),J_1,J_2\in\mathrm{Sets}_{\le\nu},(s,t,c,e)\in(\mathrm{Map}(J_1,J_2),\mathrm{Map}(J_1\times_{s,J_2,t}J_1,J_1),\mathrm{Map}(J_2,J_1)),\wedge^4_{i=1}P_i(s,t,c,e)\}.$$

The class $\mathrm{Cat}'_{\le\nu}$ is a set, as it is contained in the set:

$$\mathcal{C}_{\le\nu}:=\coprod_{J_1,J_2\in\mathrm{Set}_{\le\nu}}\{(J_1,J_2)\}\times\mathrm{Map}(J_1,J_2)\times\mathrm{Map}(J_1\times_{s,J_2,t}J_1,J_1)\times\mathrm{Map}(J_2,J_1)$$

via the injective class function:

$$\phi\subset\mathrm{Cat}'_{\le\nu}\times\coprod_{J_1,J_2\in\mathrm{Set}_{\le\nu}}\{(J_1,J_2)\}\times\mathrm{Map}(J_1,J_2)\times\mathrm{Map}(J_1\times_{s,J_2,t}J_1,J_1)\times\mathrm{Map}(J_2,J_1)$$

defined as

$$\phi:=\{((J_1,J_2,s,t,c,e),(I_1,I_2,s',t',c',e'))\in\mathrm{Cat}'_{\le\nu}\times \mathcal{C}_{\le\nu}\mid (J_1,J_2,s,t,c,e)=(I_1,I_2,s',t',c',e')\},$$

the equality $(J_1,J_2,s,t,c,e)=(I_1,I_2,s',t',c',e')$ being defined within $\mathbf{C}_{\le\nu}$. As $\mathcal{C}_{\le\nu}$ is a set, so is $\mathrm{Cat}'_{\le\nu}$ by the Axiom Schema of Replacement.

Let $J$ be a $\nu$-small category. By Lemma E.3.1.2, there exists $J_2\in\mathrm{Sets}_{\le\nu}$ together with a bijection $f:J_2\to J$. We now let $J':=\coprod_{(i,j)\in J\times J}\mathrm{Map}_J(i,j)$. We define $s',t':=J'\rightrightarrows J$ on each $\mathrm{Map}_J(i,j)$ as $s'(a):=i$, $t'(a):=j$, alongside $e':J\to J'$ defined as $e(i):=\mathrm{id}_i\in J'$, and $c':J'\times_{s',J,t'}J'\to J'$ defined as $c'(a,b):=b\circ a$. As $|J'|\le\max\{|J\times J|,\sup_{(i,j)\in J\times J}|\mathrm{Map}_J(i,j)|\}$, and $J$ is a $\nu$-small category with $\nu$ infinite, we have $|J'|\le\nu$. By Lemma E.3.1.2, there exists $J_1\in\mathrm{Sets}_{\le\nu}$ and a bijection $g:J_1\to J'$. We now define $s:=f^{-1}\circ s'\circ g$, $t:=f^{-1}\circ t'\circ g$, $c:=g^{-1}\circ c'\circ(g,g)$ and $e:=g^{-1}\circ e'\circ f$.

We have $P_1(s,t,c,e)$ from (E.3.1.2) because we have $P_1(s',t',c',e')$, and likewise $P_2(s,t,c,e)$ from (E.3.1.3), $P_3(s,t,c,e)$ from (E.3.1.4) and $P_4(s,t,c,e)$ from (E.3.1.5) because we have $P_i(s',t',c',e')$ for $i=2,3,4$. It follows that $(J_1,J_2,s,t,c,e)$ is an element of $\mathrm{Cat}'_{\le\nu}$. Moreover, we define the category $\mathrm{Cat}(J_1,J_2,s,t,c,e)$

## PDF page 871

**E.3. SMALL COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **871**

to be the category whose objects are the elements of $J_2$ and such that for any $(i,j)\in J_2\times J_2$ we have $\mathrm{Map}(i,j):=s^{-1}(i)\cap t^{-1}(j)$. There is a functor $u:\mathrm{Cat}(J_1,J_2,s,t,c,e)\to J$ defined as $u(i):=f(i)$, and $u(\phi:i\to j):=g(\phi)$. The functor $u$ is a bijection on sets of objects, and it is fully faithful by design of $g$. It is therefore an isomorphism of categories. We finally define the class function:

$$\psi\subset\mathrm{Cat}'_{\le\nu}\times\mathbf{Cat}_{\le\nu}$$

where $\mathbf{Cat}_{\le\nu}$ is the class of $\nu$-small categories, assigned as follows:

$$\psi:=\{((J_1,J_2,s,t,c,e),J)\in\mathrm{Cat}'_{\le\nu}\times\mathbf{Cat}_{\le\nu}\mid\mathrm{Cat}(J_1,J_2,s,t,c,e)=J\}$$

where the equality $\mathrm{Cat}(J_1,J_2,s,t,c,e)=J$ is defined within $\mathbf{Cat}_{\le\nu}$. As $\mathrm{Cat}'_{\le\nu}$ is a set, by the Axiom Schema of Replacement so is the image of $\psi$. We define such image to be $\mathrm{Cat}_{\le\nu}$. The set $\mathrm{Cat}_{\le\nu}$ satisfies the requirements in the statement of the Lemma. $\square$

We further recall the following well-known structural result on compact Hausdorff spaces:

Lemma E.3.1.5. *Let $K$ be a compact Hausdorff space, and $\kappa$ a cardinal satisfying $\mathrm{size}(K)\le\kappa$ (see Definition E.3.1.1). There exists a closed immersion*

$$\phi:K\to\prod_{\kappa}[0,1],$$

*the product being endowed with the product topology.*

Proof. We call $i:[0,1]\to\mathbf C$ the closed immersion of the unit interval in $\mathbf R$. Then $i_*:\mathrm{C}(K,[0,1])\to \mathrm{C}(K)$, defined as $i_*(f):=i\circ f$ for any $f\in \mathrm{C}(K,[0,1])$, is injective, and hence $|\mathrm{C}(K,[0,1])|\le\kappa$. We will now construct a closed immersion:

$$\phi:K\to[0,1]^{\kappa},$$

where we define $[0,1]^{\kappa}$ to be $\prod_{\alpha_{\kappa}}[0,1]$ endowed with the product topology (whose $\alpha_{\kappa}$ is the least ordinal with cardinality $\kappa$). We define

$$\phi_K:K\to\prod_{a\in \mathrm{C}(K,[0,1])}[0,1]$$

by $\phi_K(x):=(a(x))_{a\in \mathrm{C}(K,[0,1])}$. The set-function $\phi_K$ is continuous. As $|\mathrm{C}(K,[0,1])|\le\kappa$, we may call $\lambda$ the cardinality of $\mathrm{C}(K,[0,1])$ with $\lambda\le\kappa$, and select (by the Axiom of Choice) a bijection $j:\mathrm{C}(K,[0,1])\to\alpha_{\lambda}$. We may therefore define $J:=\{x\in\alpha_{\kappa}\mid x>y,\text{ for all }y\in\alpha_{\lambda}\}$, and we have $\alpha_{\kappa}=\alpha_{\lambda}\coprod J$. We define

$$i_K:\prod_{a\in \mathrm{C}(K,[0,1])}[0,1]\to[0,1]^{\kappa}$$

by $i_K((x_a)_{a\in \mathrm{C}(K,[0,1])}):=(x_c)_{c\in\alpha_{\kappa}}$ where $x_c=x_a$ in $[0,1]$ for $c$ of the form $c=j(a)$ (where such $a$ is unique by injectivity of $j$), and $x_c=0$ otherwise. The map $i_K$ is continuous, and we may therefore define $\phi:K\to[0,1]^{\kappa}$ as $\phi:=i_K\circ\phi_K$. The set-function $\phi$ is therefore continuous. It is also injective by Urysohn’s Lemma, as $K$ is compact Hausdorff (hence normal). Since $K$ is compact and $[0,1]^{\kappa}$ is Hausdorff, $\phi$ is a closed immersion. $\square$

We now construct, for any fixed cardinal $\kappa$, a set of representatives of all compact Hausdorff spaces of size at most $\kappa$ up to homeomorphism.

Lemma E.3.1.6. *Let $\kappa$ be a cardinal, and $\mathcal K_{\le\kappa}$ the class of all compact Hausdorff spaces $K$ such that $\mathrm{size}(K)\le\kappa$. Then there exists a sub-class $\mathrm{CH}_{\le\kappa}\subset\mathcal K_{\le\kappa}$ such that:*

*(1) $\mathrm{CH}_{\le\kappa}$ is a set.*

*(2) For any $K\in\mathcal K_{\le\kappa}$ there exists $K'\in\mathrm{CH}_{\le\kappa}$ and a homeomorphism $f:K'\to K$.*

Proof. We note that, by design of $\mathrm{size}(\cdot)$ (see Definition E.3.1.1), for any fixed compact Hausdorff space $K$ with $\mathrm{size}(K)\le\kappa$, the set of all compact Hausdorff subspaces of $K$ has cardinality bounded above by $\kappa$,

## PDF page 872

**872** · **CHAPTER E. TOPOLOGICAL STACKS**

and the algebra of continuous complex-valued functions on each compact Hausdorff subspace of $K$ also has cardinality bounded above by $\kappa$. In particular,

$$|\mathrm{C}(K)|\le\kappa.$$

We define $\mathcal C_{\kappa}$ to be the set of all closed subsets of $[0,1]^{\kappa}$, so all elements of $\mathcal C_{\kappa}$ are compact Hausdorff. We may therefore define $\mathrm{CH}_{\le\kappa}:=\mathcal C_{\kappa}\cap\mathcal K_{\le\kappa}$, the intersection being formed within the class of all compact Hausdorff spaces. For any compact Hausdorff space $K$ such that $\mathrm{size}(K)\le\kappa$, by Lemma E.3.1.5 there exists a closed immersion $\phi:K\to[0,1]^{\kappa}$, and hence an element $K'$ in $\mathrm{CH}_{\le\kappa}$ and a homeomorphism $f:K'\to K$, defined as the inverse of the homeomorphism induced by $\phi$ from $K$ onto the image $K':=\phi(K)$. $\square$

We can now use Lemma E.3.1.2 and Lemma E.3.1.6 alongside Proposition E.2.1.13 to construct, for each fixed cardinal $\kappa$, a set of compactly generated and weakly Hausdorff spaces such that every object of $\mathbf{CGWH}$ of size at most $\kappa$ is homeomorphic to an object of such a set. This construction will be used as a crutch to build a small subcategory of $\mathbf{CGWH}$ stable under enough categorical operations to enable us to make some intrinsic constructions of interest, and that will serve as underlying category for our sought-for “topological site”. The following Lemma is an analog of [SP, Tag 000I].

Lemma E.3.1.7. *For every cardinal $\kappa$, there exists a set $S$ of compactly generated weakly Hausdorff topological spaces, such that for every compactly generated weakly Hausdorff topological space $X$ with $\mathrm{size}(X)\le\kappa$, there exists an element $Y\in S$ and an isomorphism $Y\to X$ in $\mathbf{CGWH}$.*

Proof. We consider the set $S'$ defined as follows. For any $J\in\mathrm{Sets}_{\le\kappa}$, where $\mathrm{Sets}_{\le\kappa}$ is the set from Lemma E.3.1.2, we let $f$ be a set-function $f:J\to\mathrm{CH}_{\le\kappa}$, where $\mathrm{CH}_{\le\kappa}$ is the set from Lemma E.3.1.6 above. We define $S'_{(J,f)}$ to be the set of all closed equivalence relations in the topological space $(\coprod_J f(j))\times(\coprod_J f(j))$ (product in $\mathbf{CGWH}$, agreeing with the one in $\mathbf{Spaces}$), and we further define:

$$S':=\coprod_{J\in\mathrm{Sets}_{\le\kappa}}\coprod_{f\in\mathrm{Map}(J,\mathrm{CH}_{\le\kappa})}S'_{(J,f)}$$

itself a set. For any $s\in S'$, there exists $J\in\mathrm{Sets}_{\le\kappa}$ and $f\in\mathrm{Map}(J,\mathrm{CH}_{\le\kappa})$, and a closed equivalence relation $R\subset(\coprod_J f(j))\times(\coprod_J f(j))$, with $s=R$. We define $q(s):=(\coprod_J f(j))/R$, a compactly generated and weakly Hausdorff space by Lemma E.2.1.11.

We now define the class function

$$F:=\{(s,X)\mid s\in S',X\in\mathrm{Ob}(\mathbf{CGWH}),q(s)=X\}$$

where the formula $q(s)=X$ holds in the class $\mathrm{Ob}(\mathbf{CGWH})$. We call $S$ the image of $F$. By the Axiom Schema of Replacement, $S$ is a set. By Proposition E.2.1.13, any compactly generated and weakly Hausdorff topological space $X$ with $\mathrm{size}(X)\le\kappa$ is a quotient of a coproduct of all compact Hausdorff subspaces of $X$ indexed by a set $J$ of cardinality at most $\kappa$ (the set of all compact Hausdorff subspaces of $X$). By Lemma E.3.1.6, such subspaces are each homeomorphic to a compact Hausdorff space which is an element of $\mathrm{CH}_{\le\kappa}$, and the index set is bijective to a set in $\mathrm{Sets}_{\le\kappa}$. The closed equivalence relation on the coproduct of all compact Hausdorff subspaces of $X$ is therefore homeomorphic to an element of $S'$, and via the class function $F$ there exists a compactly generated weakly Hausdorff space $Y$ which is an element of $S$ and a homeomorphism $Y\to X$. $\square$

E.3.2. $\alpha$-small compactly generated and weakly Hausdorff spaces. We assign the following:

Definition E.3.2.1. Let $\alpha$ be an ordinal, and $\nu$ be a cardinal.

(1) The category $\mathbf{CGWH}_{\alpha}$ has as its objects the compactly generated weakly Hausdorff topological spaces whose underlying sets are elements of $V_{\alpha}$, and its morphisms are continuous maps of topological spaces. We call $\alpha$-small the compactly generated and weakly Hausdorff spaces that are the objects of $\mathbf{CGWH}_{\alpha}$.

## PDF page 873

**E.3. SMALL COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **873**

(2) For $\mathcal{C}$ a category, $I$ a $\nu$-small category, and $P:I\to \mathcal{C}$ a diagram, we call $P$ a $\nu$-small diagram and denote by $\lim_I P$ respectively $\mathrm{colim}_I P$ its $\nu$-small limit respectively $\nu$-small colimit if representable in $\mathcal{C}$.

(3) We say that a category $\mathcal{C}$ contains all $\nu$-small limits respectively contains all $\nu$-small colimits (or that $\nu$-small limits, respectively $\nu$-small colimits, are representable in $\mathcal{C}$) if and only if for any $\nu$-small diagram $P:I\to \mathcal{C}$ the object $\lim_I P$ respectively $\mathrm{colim}_I P$ exists in $\mathcal{C}$.

Remark E.3.2.2. On Definition E.3.2.1, we make the following observation. Every topological space is homeomorphic to one whose underlying set is in the class $\mathbf{WF}$. This is [Kunen, Lemma 2.14], and justifies the approach taken throughout to bound the size of the topological spaces in our sought-for small subcategory of the category $\mathbf{CGWH}$ of all compactly generated weakly Hausdorff topological spaces. We refer the reader to [Jech, Lemma 6.3] that establishes that every set is in some $V_{\alpha}$, as a consequence of the Axiom of Regularity in ZF$^{-}$. In particular, this makes no use of the Axiom of Choice.

The following result is an analog of [SP, Tag 000J]. We keep the notation similar so as to enable the reader familiar with loc.cit. to closely follow the analogous steps within the arguments.

Lemma E.3.2.3. *Let $S_0$ be a set of compactly generated weakly Hausdorff topological spaces and $\nu$ an arbitrary infinite cardinal. Then there exists a limit ordinal $\alpha$, depending on $S_0$ and $\nu$, such that:*

*(1) $S_0$ is contained in $V_{\alpha}$.*

*(2) For any $\alpha$-small space $X$ and any compactly generated weakly Hausdorff topological space $Y$ with*

$$
\mathrm{size}(Y)\le\mathrm{Bound}(\mathrm{size}(X))
$$

*(see (E.3.1.1)) there exists an $\alpha$-small space $X'$ and a homeomorphism $X'\to Y$.*

*(3) $\nu$-small limits and colimits are representable in $\mathbf{CGWH}_{\alpha}$ and the forgetful functor to $\mathbf{CGWH}$ preserves them.*

The following argument is an adaptation to the context of this work of the argument of [SP, Tag 000J], with minor adjustments and complements.

Proof. We define a function $f$ on ordinals as follows. We set $f(0)=0$. Suppose $f(\alpha)$ is already defined. We define $f(\alpha+1)$ to be the smallest ordinal $\beta$ such that:

(1) $\max\{\alpha+1,f(\alpha)\}\le\beta$.

(2) For any object $T$ of $\mathbf{CGWH}_{f(\alpha)}$ and any compactly generated weakly Hausdorff $X$ with $\mathrm{size}(X)\le\mathrm{Bound}(\mathrm{size}(T))$, there exists an object $T'$ of $\mathbf{CGWH}_{\beta}$ and a homeomorphism $T'\to X$.

(3) For any $\nu$-small index category $I$ and any functor $F:I\to\mathbf{CGWH}_{f(\alpha)}$, $\lim_I F$ and $\mathrm{colim}_I F$ are isomorphic to objects of $\mathbf{CGWH}_{\beta}$.

We proceed in a very similar manner as in [SP, Tag 000J] to prove that $\beta$ indeed exists.

We set $\kappa:=\sup_T\mathrm{Bound}(\mathrm{size}(T))$ where $T$ varies across all objects of $\mathbf{CGWH}_{f(\alpha)}$, which is a small category by design. The cardinal $\kappa$ therefore exists. We apply Lemma E.3.1.7 to $\kappa$ to obtain the set $S$ of that Lemma. We now repeat the argument at this stage of [SP, Tag 000J]. Up to isomorphism of small index categories, we may require that $I$ in (3) is an element of the set of $\nu$-small categories $\mathrm{Cat}_{\le\nu}$ provided by Lemma E.3.1.4, so the pair $(I,F)$ in part (3) therefore varies over a set of pairs $(I,F)$ where $I$ is an element of $\mathrm{Cat}_{\le\nu}$, and $F$ is a functor $I\to\mathbf{CGWH}_{f(\alpha)}$. We may therefore find a set $S'$ such that for any pair $(I,F)$ as in (3) above, the limit and colimit are isomorphic to elements of $S'$. Upon choosing any $\beta$ such that $\beta\ge\max\{\alpha+1,f(\alpha)\}$ and $S\cup S'\subset V_{\beta}$, all the required axioms hold for $\beta$. Upon minimizing over such ordinals $\beta$, we see that $f(\alpha+1)$ is well-defined by transfinite recursion. One then extends $f$ to limit ordinals by setting:

$$f(\alpha):=\sup_{\beta<\alpha}f(\beta).$$

## PDF page 874

**874** · **CHAPTER E. TOPOLOGICAL STACKS**

We now choose an ordinal $\gamma$ such that $S_0\subset V_{\gamma}$. As $f(\delta)\ge\delta$ for all ordinals $\delta$. and $f(\delta')\ge f(\delta)$ whenever $\delta'\ge\delta$ by design of $f$, we see that

$$S_0\subset V_{f(\gamma)}\subseteq V_{f(\beta)}\text{ for all }\beta\ge\gamma.$$

We choose a limit ordinal $\gamma'>\gamma$ with cofinality greater than $\nu$ and set $\alpha:=f(\gamma')$. The verification that $\alpha$ is the sought-for ordinal is now identical to that in [SP, Tag 000J]. We repeat it here merely because we wish to record an argument for compactly generated weakly Hausdorff topological spaces without referring to an argument for schemes, even though formally identical.

Property (1) is satisfied because we chose $\gamma'>\gamma$. We have, as $\gamma'$ is a limit ordinal:

$$f(\gamma')=\sup_{\beta<\gamma'}f(\beta).$$

The set $\{f(\beta)\mid\beta<\gamma'\}\subset f(\gamma')$ is a cofinal subset, and we get:

$$V_{\alpha}=V_{f(\gamma')}=\bigcup_{\beta<\gamma'}V_{f(\beta)}.$$

For any object $T$ in $\mathbf{CGWH}_{\alpha}$, we call $\beta(T)$ the ordinal such that $T$ is an object of $\mathbf{CGWH}_{f(\beta)}$, minimal with respect to this property. It follows $\beta(T)<\gamma'$. Since the objects of $\mathbf{CGWH}_{\beta(T)+1}$ are contained in $\mathbf{CGWH}_{f(\beta+1)}$ with $\beta+1<\gamma'$, so they are objects of $\mathbf{CGWH}_{\alpha}$, the second property is also seen to be satisfied.

The last part of the argument is identical to the last paragraph in [SP, Tag 000J], with only notational changes; we repeat it here for the sake of completeness. Suppose that for a set $J$ with $|J|\le\nu$, we have a $J$-indexed collection $\{S_j,j\in J\}$ of objects of $\mathbf{CGWH}_{\alpha}$. The function $\nu\to\gamma'$ given by $j\mapsto\beta(S_j)$ is such that its image is not a cofinal subset, since the cofinality of $\gamma'$ is greater than $\nu$. There therefore exists $\beta<\gamma'$ such that $\{S_j,j\in J\}\subset\mathbf{CGWH}_{f(\beta)}$, and so every functor $F:I\to\mathbf{CGWH}_{\alpha}$ as in part (3) of the Lemma factors through a subcategory $\mathbf{CGWH}_{f(\beta)}$ for some appropriate $\beta<\gamma'$ depending on $I$ and $F$. The limit, respectively colimit, of the diagram $F:I\to\mathbf{CGWH}_{\alpha}$ is, by design of $f$, therefore isomorphic to an object of $\mathbf{CGWH}_{f(\beta+1)}$, which is in turn a subcategory of $\mathbf{CGWH}_{\alpha}$. $\square$

E.3.3. Size-bound criteria. We have the following Lemma, in analogy with [SP, Tag 000P].

Lemma E.3.3.1. *Let $X$ be a compact Hausdorff topological space. Then:*

$$\mathrm{size}(X)\le\max\{\aleph_0,2^{|\mathrm{C}(X)|}\}.$$

See Definition E.3.1.1 for the definition of $\mathrm{size}(\cdot)$ on $\mathbf{CGWH}$.

Proof. The number of compact Hausdorff subspaces of $X$ is at most $\max\{\aleph_0,2^{|\mathrm{C}(X)|}\}$ because if $K\subset X$ is compact Hausdorff then by Urysohn’s Lemma $K$ is the zero locus of an ideal $I\subset \mathrm{C}(X)$ (namely, $I$ is the ideal of $f$ vanishing on $X$), and the number of such ideals is at most $2^{|\mathrm{C}(X)|}$. $\square$

Lemma E.3.3.2. *Let $X$ be a compactly generated weakly Hausdorff topological space, and $\{K_i,i\in I\}$ a collection of compact Hausdorff subspaces of $X$ such that:*

$$\bigcup_{i\in I}K_i=X.$$

*Then we have:*

$$\mathrm{size}(X)\le\max\{\aleph_0,(\sup_{i\in I}\mathrm{size}(K_i))^{|I|}\}.$$

Proof. Let $K$ be a compact Hausdorff subspace of $X$, and call $H_i:=K\cap K_i$ for all $i\in I$. As $K$ is compact Hausdorff and $X$ is weakly Hausdorff, $K$ is closed in $X$. In particular, $H_i$ is closed in $K_i$, hence

## PDF page 875

**E.3. SMALL COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **875**

compact Hausdorff and closed in $X$. Since $\bigcup_{i\in I}K_i=X$, we have $\bigcup_{i\in I}H_i=K$. As the map

$$q:\coprod_{i\in I}H_i\to K$$

is surjective, the set-function

$$\mathrm{C}(K)\to\prod_{i\in I}\mathrm{C}(H_i)$$

is injective. We deduce the bound

$$|\mathrm{C}(K)|\le|\prod_{i\in I}\mathrm{C}(H_i)|.$$

As $K_i$ is normal and $H_i\subset K_i$ is closed, Tietze’s Extension Theorem gives that $\mathrm{C}(K_i)\to \mathrm{C}(H_i)$ is surjective for every $i\in I$. We deduce the bound:

$$|\prod_{i\in I}\mathrm{C}(H_i)|\le|\prod_{i\in I}\mathrm{C}(K_i)|.$$

As $\sup_{i\in I}|\mathrm{C}(K_i)|\le\sup_{i\in I}\mathrm{size}(K_i):=\lambda$, there exists an initial ordinal $\omega_{\lambda}$ for $\lambda$ and we further obtain the cardinal bound $|\prod_{i\in I}\mathrm{C}(K_i)|\le|\prod_{i\in I}\omega_{\lambda}|=\lambda^{|I|}$. We deduce the cardinal bound:

$$|\mathrm{C}(K)|\le\lambda^{|I|}.$$

The set of compact Hausdorff subspaces of $X$ has cardinality at most the cardinality of the set

$$\prod_{i\in I}\Sigma_i$$

where $\Sigma_i$ is the set of compact Hausdorff subspaces of $K_i$. Indeed, upon writing $\Sigma_X$ for the set of compact Hausdorff subspaces of $X$, the set-function $\phi:\Sigma_X\to\prod_{i\in I}\Sigma_i$ assigned by $\phi(K):=(K\cap K_i)_{i\in I}$ is injective, and hence $|\Sigma_X|\le|\prod_{i\in I}\Sigma_i|$. Since each $K_i$ is itself compact Hausdorff, so $|\Sigma_i|\le\mathrm{size}(K_i)$ for every $i\in I$,

$$|\Sigma_X|\le(\sup_{i\in I}\mathrm{size}(K_i))^{|I|}.$$

We may therefore assemble the bounds obtained to deduce that we have

$$\mathrm{size}(X)=\max\{\aleph_0,|\Sigma_X|,\sup\{|\mathrm{C}(K)|,K\in\Sigma_X\}\}\le\max\{\aleph_0,\lambda^{|I|}\}.$$

$\square$

Lemma E.3.3.3. *Let $f:X\to Y$ and $g:Z\to Y$ be morphisms of compactly generated weakly Hausdorff topological spaces. Then:*

$$\mathrm{size}(X\times_{f,Y,g}Z)\le\max\{\mathrm{Bound}(\mathrm{size}(X)),\mathrm{Bound}(\mathrm{size}(Z))\}.$$

Proof. Let $\{K_i,i\in I_Y\}$ be a collection of compact Hausdorff topological subspaces of $Y$ without repetition such that $\coprod_{i\in I_Y}K_i\to Y$ is submersive. This can be found in light of Proposition E.2.1.13. We have $|I_Y|\le\mathrm{size}(Y)$. The closed preimages $X_i:=f^{-1}(K_i)$ and $Z_i:=g^{-1}(K_i)$ in $X$ respectively $Z$ are compactly generated by Lemma E.1.2.25 and weakly Hausdorff. For each $i\in I_Y$, by Proposition E.2.1.13, there exist index sets $I_{X_i}$ and $I_{Z_i}$ with $|I_{X_i}|\le|\Sigma_{X_i}|$ and $|I_{Z_i}|\le|\Sigma_{Z_i}|$, with $\Sigma_{X_i}$ and $\Sigma_{Z_i}$ the sets of compact Hausdorff subspaces of $X_i$, $Z_i$, respectively, and compact Hausdorff subspaces $H_{ij}\subset X_i$ and $F_{im}\subset Z_i$ for every $j\in I_{X_i}$, $m\in I_{Z_i}$, such that we have submersions

$$\coprod_{j\in I_{X_i}}H_{ij}\to X_i,$$

$$\coprod_{m\in I_{Z_i}}F_{im}\to Z_i.$$

## PDF page 876

**876** · **CHAPTER E. TOPOLOGICAL STACKS**

It follows that, upon denoting $J:=\coprod_{i\in I_Y}I_{X_i}\times I_{Z_i}$, we have, upon denoting $(j,m)$ the elements of $J$, with $j\in I_{X_i}$, $m\in I_{Z_i}$ for a unique $i\in I_Y$:

$$\bigcup_{(j,m)\in J}(H_{ij}\times_{f,K_i,g}F_{im})=X\times_{f,Y,g}Z.$$

As $H_{ij}$ and $F_{im}$ are compact Hausdorff for every $i\in I_Y$, $j\in I_{X_i}$ and $m\in I_{Z_i}$, we have that $H_{ij}\times^0_{f,K_i,g}F_{im}$ is closed in $H_{ij}\times_0 F_{im}$, which is compact Hausdorff. It follows that $H_{ij}\times^0_{f,K_i,g}F_{im}$ is compact Hausdorff and hence compactly generated and weakly Hausdorff by Lemma E.2.3.1. We therefore have that the topological fibre product $H_{ij}\times^0_{f,K_i,g}F_{im}$ computes the fibre product $H_{ij}\times_{f,K_i,g}F_{im}$ in $\mathbf{CGWH}$ by Lemma E.2.2.5(1) and Lemma E.1.2.2(1). By Lemma E.3.3.2, we have

$$\mathrm{size}(X\times_{f,Y,g}Z)\le\max\{\aleph_0,\sup_{(j,m)\in J}(\mathrm{size}(H_{ij}\times^0_{f,K_i,g}F_{im}))^{|J|}\}$$

and by Lemma E.3.3.1 we further have

$$\mathrm{size}(H_{ij}\times^0_{f,K_i,g}F_{im})\le\max\{\aleph_0,2^{|\mathrm{C}(H_{ij}\times^0_{f,K_i,g}F_{im})|}\},$$

so

$$\mathrm{size}(X\times_{f,Y,g}Z)\le\max\{\aleph_0,(\sup_{(j,m)\in J}\max\{\aleph_0,2^{|\mathrm{C}(H_{ij}\times^0_{f,K_i,g}F_{im})|}\})^{|J|}\}$$

and hence

$$\mathrm{size}(X\times_{f,Y,g}Z)\le\max\{\aleph_0,\aleph_0^{|J|},(\sup_{(j,m)\in J}2^{|\mathrm{C}(H_{ij}\times^0_{f,K_i,g}F_{im})|})^{|J|}\}.$$

We now check that

$$|\mathrm{C}(H_{ij}\times^0_{f,K_i,g}F_{im})|=|\mathrm{C}(H_{ij})\otimes_{\mathrm{C}(K_i)}\mathrm{C}(F_{im})|\le\max\{\aleph_0,|\mathrm{C}(H_{ij})|,|\mathrm{C}(F_{im})|\},$$

where the tensor product is an algebraic tensor product. The elements of the Banach algebra $\mathrm{C}(H_{ij}\times^0_{f,K_i,g}F_{im})$ extend to $\mathrm{C}(H_{ij}\times F_{im})$ by the Tietze Extension Theorem, and in the latter algebra everything is the limit of a sequence from $\mathrm{C}(H_{ij})\otimes_{\mathrm{C}(K_i)}\mathrm{C}(F_{im})$ (density by Stone-Weierstrass), so

$$|\mathrm{C}(H_{ij})\otimes_{\mathrm{C}(K_i)}\mathrm{C}(F_{im})|\le|\mathrm{C}(H_{ij})|\times|\mathrm{C}(F_{im})|\times\aleph_0.$$

By [Kunen, Ch. I, Cor. 10.13] the right side is, in turn, $\max\{\aleph_0,|\mathrm{C}(H_{ij})|,|\mathrm{C}(F_{im})|\}$. As

$$(\sup_{(j,m)\in J}\max\{\aleph_0,|\mathrm{C}(H_{ij})|,|\mathrm{C}(F_{im})|\})^{|J|}=\max\{\aleph_0^{|J|},(\sup_{(j,m)\in J}|\mathrm{C}(H_{ij})|)^{|J|},(\sup_{(j,m)\in J}|\mathrm{C}(F_{im})|)^{|J|}\}$$

and

$$(\sup_{(j,m)\in J}|\mathrm{C}(H_{ij})|)^{|J|}\le(\mathrm{size}(X))^{|J|},(\sup_{(j,m)\in J}|\mathrm{C}(F_{im})|)^{|J|}\le(\mathrm{size}(Z))^{|J|},$$

upon assembling all the bounds so far obtained we have

$$\mathrm{size}(X\times_{f,Y,g}Z)\le\max\{\aleph_0,\aleph_0^{|J|},(2^{\mathrm{size}(X)})^{|J|},(2^{\mathrm{size}(Z)})^{|J|}\}. \tag{E.3.3.1}$$

We further have:

$$|J|=\sup_{i\in I_Y}|I_{X_i}|\times|I_{Z_i}|\le\sup_{i\in I_Y}|\Sigma_{X_i}|\times|\Sigma_{Z_i}|.$$

By [Kunen, Ch. I, Cor. 10.13], the right side is $\max\{\sup_{i\in I_Y}|\Sigma_{X_i}|,\sup_{i\in I_Y}|\Sigma_{Z_i}|\}$, which is bounded above by $\max\{\mathrm{size}(X),\mathrm{size}(Z)\}$, as $X_i$ is closed in $X$ and $Z_i$ is closed in $Z$, and hence the maps $\Sigma_{X_i}\to\Sigma_X$ and $\Sigma_{Z_i}\to\Sigma_Z$ sending a compact Hausdorff subspace $K$ of $X_i$, respectively $Z_i$, to itself as a compact Hausdorff subspace of $X$, respectively $Z$, are injective. We deduce from (E.3.3.1) the cardinal bound:

$$\mathrm{size}(X\times_{f,Y,g}Z)\le\max\{\aleph_0,2^{\max\{\mathrm{size}(X),\mathrm{size}(Z)\}},(\mathrm{size}(X))^{\max\{\mathrm{size}(X),\mathrm{size}(Z)\}},(\mathrm{size}(Z))^{\max\{\mathrm{size}(X),\mathrm{size}(Z)\}}\}$$

## PDF page 877

**E.3. SMALL COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **877**

which in turn yields:

$$
\mathrm{size}(X \times_{f,Y,g} Z) \le \max\{\aleph_0, 2^{\max\{\mathrm{size}(X),\mathrm{size}(Z)\}}, \max\{(\mathrm{size}(X))^{\mathrm{size}(X)}, (\mathrm{size}(Z))^{\mathrm{size}(Z)}\}\}.
$$

Finally, the right side is bounded above by $\max\{\mathrm{Bound}(\mathrm{size}(X)), \mathrm{Bound}(\mathrm{size}(Z)\}$ and the Lemma is proved. $\square$

**Lemma E.3.3.4.** *For $S_0$ and $V$ as in Lemma E.3.2.3, let $\alpha$ be as constructed there. Let $Y$ be a compactly generated weakly Hausdorff topological space and $\{K_i, i \in I\}$ a collection of compact Hausdorff subspaces of $Y$ such that $\coprod_{i \in I} K_i \to Y$ us submersive. Assume that there exists an object $X$ in $\mathbf{CGWH}_\alpha$ such that*

(1) *$\mathrm{size}(K_i) \le \mathrm{size}(X)$ for all $i \in I$,*

(2) *$|I| \le \mathrm{size}(X)$.*

*Then $Y$ is homeomorphic to an object of $\mathbf{CGWH}_\alpha$.*

*Proof.* This holds as the size of $Y$ is, by Lemma E.3.3.2, at most:

$$
\max\{\aleph_0, (\sup_{i \in I} \mathrm{size}(K_i))^{|I|}\} \le \mathrm{Bound}(\mathrm{size}(X)).
$$

By Lemma E.3.2.3(2) there exists an object $X'$ of $\mathbf{CGWH}_\alpha$ and a homeomorphism $X' \to Y$. $\square$

**E.3.4. Closure properties of $\mathbf{CGWH}_\alpha$.** We collect here the properties that the category $\mathbf{CGWH}_\alpha$ enjoys.

**Proposition E.3.4.1.** *For $S_0$ a set of compactly generated weakly Hausdorff topological spaces, $\nu$ an infinite cardinal, and $\alpha$ a limit ordinal as provided by Lemma E.3.2.3, the category $\mathbf{CGWH}_\alpha$ satisfies the following properties:*

(1) *$\nu$-small limits and colimits are representable in $\mathbf{CGWH}_\alpha$ and the forgetful functor to $\mathbf{CGWH}$ commutes with them.*

(2) *Fibre products exist in $\mathbf{CGWH}_\alpha$ and the forgetful functor to $\mathbf{CGWH}$ commutes with them.*

(3) *Countable coproducts exist in $\mathbf{CGWH}_\alpha$ and the forgetful functor to $\mathbf{CGWH}$ commutes with them.*

(4) *For any object $X$ in $\mathbf{CGWH}_\alpha$ and any immersion $Z \to X$ with $Z$ compactly generated weakly Hausdorff, there exists an object $Z'$ in $\mathbf{CGWH}_\alpha$ and a homeomorphism $Z' \to Z$.*

(5) *For any object $X$ in $\mathbf{CGWH}_\alpha$ and any open, respectively closed, respectively locally closed, immersion $Z \to X$ (so $Z$ is compactly generated weakly Hausdorff by Lemma E.1.2.25), there exists an object $Z'$ in $\mathbf{CGWH}_\alpha$ and a homeomorphism $Z' \to Z$.*

*Proof.* By Lemma E.3.2.3(3), part (1) holds. Parts (2) and (3) are a consequence of part (1) since $\nu$ is infinite. We prove parts (4) and (5). In both cases, the cardinality of the set $I$ of compact Hausdorff subspaces of $Z$ is bounded above by $\mathrm{size}(X)$. Likewise, for any compact Hausdorff subspace $K$ of $Z$, we have $\mathrm{size}(K) \le \mathrm{size}(X)$, as $\Sigma_K \hookrightarrow \Sigma_X$ because the image of $K$ under the immersion $Z \to X$ is a compact Hausdorff subspace of $X$ as well. We now observe that the set $I$ defined above is such that $\bigcup_{K \in I} K$ is $Z$ by Proposition E.2.1.13. By Lemma E.3.3.4, we deduce that $Z$ is homeomorphic to an object of $\mathbf{CGWH}_\alpha$. This proves (4) and (5). $\square$

**Remark E.3.4.2.** We do not address whether the function space $\mathscr{C}ont(X, Y)$, for $\alpha$-small compactly generated topological spaces $X$ and $Y$, is homeomorphic to an object of $\mathbf{CGWH}_\alpha$, as this would be of no use for the purposes of this appendix. Such objects would not endow $\mathbf{CGWH}_\alpha$ with the structure of a cartesian closed symmetric monoidal category. Indeed, the obstruction to $\mathbf{CGWH}_\alpha$ being a cartesian closed symmetric monoidal category such that the forgetful functor to $\mathbf{CGWH}$ is a strict closed functor; i.e., it preserves internal Hom-bifunctors, is that the category $\mathbf{CGWH}_\alpha$ is not replete. This is because it is a small category by design, whereas $\mathbf{CGWH}$ is large. If $\mathbf{CGWH}_\alpha$ was cartesian closed, and if the forgetful functor (which, in light of Proposition E.3.4.1(1) is product-preserving and hence automatically a “strong

## PDF page 878

**878** · **CHAPTER E. TOPOLOGICAL STACKS**

closed functor” between symmetric monoidal categories) were a *strict* closed functor then $\mathbf{CGWH}_\alpha$ would have to contain all function spaces of all pairs of its objects. This cannot be, as Example E.3.4.3 below shows. Proposition E.3.4.1 shows, however, that despite not being cartesian closed, the category $\mathbf{CGWH}_\alpha$ does still enjoy important consequences of cartesian-closedness of $\mathbf{CGWH}$ that we have collected in the previous sections. Most importantly, formation of products in $\mathbf{CGWH}_\alpha$ commutes with *representable* colimits. Proposition E.3.4.1 also ensures that $\nu$-small colimits (and $\nu$-small limits) are representable.

**Example E.3.4.3.** We let $X_0 := \varnothing$, equipped with the empty topology. We note that $X$ is compactly generated and weakly Hausdorff (by definition, or, for instance, by Remark E.2.1.2). We further let $Y := \{0, 1\}$ endowed with the discrete topology, so $Y$ is also compactly generated and weakly Hausdorff. For any ordinal $\beta$, we call:

$$
X_{\beta+1} := \mathscr{C}ont(X_\beta, Y)
$$

therefore assigning $X_\beta$ by transfinite recursion. All the $X_\beta$ are compactly generated and weakly Hausdorff by Proposition E.2.2.10. However, the size of the underlying set of $X_{\beta+1}$ is $\beth_\beta$ (see [Kunen, Ch. I, §10, Def. 10.44]) which, for large enough $\beta$, exceeds the size of the von Neumann universe $V_\alpha$ (see [Kunen, Ch. III, §3, Lemma 2.13]) that contains all of the objects of $\mathbf{CGWH}_\alpha$. We let $\gamma := \inf\{\beta \mid X_\beta \notin V_\alpha\}$, so $X_\gamma$ is an example of an object of $\mathbf{CGWH}_\alpha$ such that $\mathscr{C}ont(X_\gamma, Y)$ is not an object of $\mathbf{CGWH}_\alpha$ but only is homeomorphic to such an object.

We denote by:

$$
u_\alpha : \mathbf{CGWH}_\alpha \to \mathbf{CGWH} \tag{E.3.4.1}
$$

the forgetful functor. The functor $u_\alpha$ is fully faithful by design, and it commutes with $\nu$-small limits and $\nu$-small colimits by Proposition E.3.4.1. In particular, it commutes with finite limits and finite colimits.

We conclude this subsection with a description of important classes of morphisms within $\mathbf{CGWH}_\alpha$, in the spirit of Proposition E.2.3.15.

**Proposition E.3.4.4.** *We have:*

(1) *The monomorphisms in $\mathbf{CGWH}_\alpha$ are the injective continuous maps.*

(2) *The epimorphisms in $\mathbf{CGWH}_\alpha$ are the continuous maps with dense image.*

(3) *The regular monomorphisms in $\mathbf{CGWH}_\alpha$ are the closed immersions.*

(4) *The regular epimorphisms in $\mathbf{CGWH}_\alpha$ are the submersive maps.*

(5) *The effective monomorphisms in $\mathbf{CGWH}_\alpha$ are the closed immersions.*

(6) *The effective epimorphisms in $\mathbf{CGWH}_\alpha$ are the submersive maps.*

(7) *The universally effective epimorphisms in $\mathbf{CGWH}_\alpha$ are the submersive maps.*

(8) *The isomorphisms in $\mathbf{CGWH}_\alpha$ are the homeomorphisms.*

(9) *Monomorphisms in $\mathbf{CGWH}_\alpha$ are stable under products, coproducts and compositions.*

(10) *Regular monomorphisms in $\mathbf{CGWH}_\alpha$ are stable under products, coproducts and compositions.*

(11) *Epimorphisms in $\mathbf{CGWH}_\alpha$ are stable under finite products, coproducts and compositions.*

(12) *Regular epimorphisms in $\mathbf{CGWH}_\alpha$ are stable under finite products, coproducts and compositions.*

(13) *Every morphism in $\mathbf{CGWH}_\alpha$ is universally the composition of a regular epimorphism followed by a monomorphism.*

(14) *$\mathbf{CGWH}_\alpha$ is a regular category.*

We recall the notion of regular category (see [vO, Def. 4.1]): a category is regular when it contains finite limits, the kernel pair of any morphism has a co-equalizer, and regular epimorphisms are stable under arbitrary base change.

*Proof.* As the forgetful functor $u_\alpha$ is faithful, it reflects monomorphisms, proving (1), and epimorphisms, proving (2). As $u_\alpha$ is fully faithful, it is conservative, i.e. it reflects isomorphisms. We now prove (3) and

## PDF page 879

**E.3. SMALL COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **879**

(5). By Lemma E.3.4.1(1), $\mathbf{CGWH}_\alpha$ contains equalizers and co-kernel pairs, and the forgetful functor $u_\alpha$ to $\mathbf{CGWH}$ commutes with them. It follows that $u_\alpha$ reflects effective monomorphisms, and that a monomorphism in $\mathbf{CGWH}_\alpha$ is regular if and only if it is effective. Suppose $f : X \to Y$ is a closed immersion of objects of $\mathbf{CGWH}_\alpha$. Then $u_\alpha(f)$ is a closed immersion in $\mathbf{CGWH}$, hence an effective monomorphism in $\mathbf{CGWH}$ by Proposition E.2.3.15. It follows $f$ that is an effective monomorphism in $\mathbf{CGWH}_\alpha$. Conversely, if $f$ is an effective monomorphism in $\mathbf{CGWH}_\alpha$, then $u_\alpha(f)$ is an effective monomorphism in $\mathbf{CGWH}$, hence a closed immersion by Proposition E.2.3.15(5) and therefore $f$ is a closed immersion.

We now prove (4) and (6). By part (1) of Lemma E.3.4.1, the category $\mathbf{CGWH}_\alpha$ contains co-equalizers and kernel pairs. It follows that epimorphisms are regular if and only if they are effective. Moreover, as $u_\alpha$ is fully faithful and commutes with finite limits and colimits by part (1) of Lemma E.3.4.1, $u_\alpha$ reflects effective epimorphisms. Suppose $f : X \to Y$ is a submersive map of objects in $\mathbf{CGWH}_\alpha$. Then $u_\alpha(f)$ is a submersive map in $\mathbf{CGWH}$, hence an effective epimorphism in $\mathbf{CGWH}$ by part (4) of Proposition E.2.3.15. As $u_\alpha$ reflects effective epimorphisms, it follows that $f$ is an effective epimorphism in $\mathbf{CGWH}_\alpha$, equivalently a regular epimorphism. Conversely, assume $f$ is an effective epimorphism. As $u_\alpha$ commutes with co-equalizers by part (1) of Lemma E.3.4.1, $u_\alpha(f)$ is a regular epimorphism, hence a submersive map, implying that $f$ is a submersive map. This proves (4) and (6).

We now prove part (7). Since $\mathbf{CGWH}_\alpha$ contains fibre products, and $u_\alpha$ commutes with them, submersive maps between objects of $\mathbf{CGWH}_\alpha$ remain submersive under base change along an arbitrary morphism in $\mathbf{CGWH}_\alpha$, since the same is true in $\mathbf{CGWH}$ by part (4) of Lemma E.2.3.6. By part (6), submersive maps are universally effective epimorphisms. Conversely, since universally effective epimorphisms are, in particular, effective epimorphisms, they are submersive maps by (6). Part (8) follows, for instance, from parts (2) and (3). For parts (9) and (11), we observe that since $u_\alpha$ reflects monomorphisms and epimorphisms, then part (9) and part (11) follow from part (9) and Proposition E.2.3.15(11). As $u_\alpha$ reflects effective monomorphisms and effective epimorphisms, then by (3) and (4), parts (10) and (12) follow from Proposition E.2.3.15(10, 12). Part (13) is a formal consequence of the fact that $\mathbf{CGWH}_\alpha$ is closed under finite limits and finite colimits by Lemma E.3.4.1(1), and regular epimorphisms are stable under arbitrary base change by (4) and (7). These three conditions say that $\mathbf{CGWH}_\alpha$ is a *regular category* (see [vO, Def. 4.1]) and by [vO, Prop. 4.2], which proves (14). $\square$

The above Proposition E.3.4.4 is saying that even though $\mathbf{CGWH}_\alpha$ is not cartesian closed as a cartesian symmetric monoidal subcategory of $\mathbf{CGWH}$ (i.e. a cartesian symmetric monoidal category such that the forgetful functor $u_\alpha$ is a strict closed functor), it inherits the good properties of $\mathbf{CGWH}$ collected in this appendix, many of which are a consequence of cartesian closure of $\mathbf{CGWH}$.

**E.3.5. The site of small compactly generated weakly Hausdorff spaces.** We let:

(1) $S_0$ be an arbitrary set of compactly generated weakly Hausdorff spaces.

(2) $\nu$ an arbitrary infinite cardinal.

We shall refer to the datum $(S_0, \nu)$ as *basic setup*. By Lemma E.3.2.3 there exists a limit ordinal $\alpha$ and a *small* category $\mathbf{CGWH}_\alpha$ with the following properties:

(1) $S_0$ is contained in the objects of $\mathbf{CGWH}_\alpha$.

(2) $I$-indexed limits and colimits exist in $\mathbf{CGWH}_\alpha$ and are preserved by the forgetful functor to $\mathbf{CGWH}$, as long as the cardinality of $I$ is at most $\nu$.

When paired with Proposition E.3.4.1 on closure properties of $\mathbf{CGWH}_\alpha$, we obtained Proposition E.3.4.4 that gives a topological description of key classes of morphisms in $\mathbf{CGWH}_\alpha$. We are allowed to choose a basic setup $(S_0, \nu)$ that fits our requirements.

We are now going to use Proposition E.3.4.4 to construct a site. The topology of our choosing will be the canonical topology itself. Proposition E.3.4.4 enables a concrete description for it (see Lemma E.3.5.7).

## PDF page 880

**880** · **CHAPTER E. TOPOLOGICAL STACKS**

The methods in use within this subsection follow [SP, Tag 00VH], and [KS, Ch. 16-17], and particularly [KS, Ch. 16, §16.1] and [KS, Ch. 17, §17.1-17.2].

We begin with the following construction:

**Construction E.3.5.1.** We let $S'_0$ be the smallest set of compactly generated weakly Hausdorff topological spaces, satisfying the following properties:

(1) $S'_0$ contains the following topological groups:

(a) $\mathbf{Q}$, $\mathbf{Q}^\times$ with the discrete topology.

(b) $\mathbf{Z}$ and all its finite abelian quotients, all with the discrete topology.

(c) $\mathbf{Z}_p^\times$, $\mathbf{Z}_p$ with the $p$-adic topology.

(d) $\mathbf{R}$, $\mathbf{R}^\times$, $\mathbf{C}$, $\mathbf{C}^\times$, all with the Euclidean topology.

(e) $\mathbf{A}_\mathbf{Q}$ with the adelic topology.

(f) $\mathbf{A}_{\mathbf{Q}}^\times$ with the idelic topology.

(g) The closed subgroups of all of the above.

(2) $S'_0$ contains $\mathbf{CP}^1$.

(3) $S'_0$ is closed under countable products and coproducts in $\mathbf{CGWH}$.

(4) For any $X \in S'_0$, all closed equivalence relations $R \subset X \times X$ are contained in $S_0$, and the quotients $X/R$ are contained in $S'_0$.

We let $\nu := \mathrm{Bound}(\sup_{X \in S'_0}\{\mathrm{size}(X)\})$ (see (E.3.1.1) from Definition E.3.1.1 for the definition of the “size” of a compactly generated weakly Hausdorff space, alongside the $\mathrm{Bound}(\cdot)$ function on cardinals) and call $S''_0$ the set $\mathrm{CH}_{\le \nu}$ provided by Lemma E.3.1.6. For $S_0 := S'_0 \cup S''_0$. the pair $(S_0, \nu)$ is our choice of basic setup. We let $\alpha$ be the limit ordinal provided by Lemma E.3.2.3 associated to this choice of $S_0$ and $\nu$.

We refer the reader to §E.3.1 for the construction of $\mathrm{CH}_{\le \nu}$, and likewise for the construction of $\mathrm{Sets}_{\le \nu}$ and $\mathrm{Cat}_{\le \nu}$. These are sets, the first a set of representatives for the homeomorphism classes of all compact Hausdorff spaces of size bounded above by $\nu$, the second a set of representatives for all sets of cardinality bounded above by $\nu$, the third a set of representatives for the isomorphism classes of small categories, whose sets of objects and morphisms has cardinality bounded above by $\nu$. Constructing the three sets was carried out in Lemma E.3.1.2, Lemma E.3.1.4, and Lemma E.3.1.6.

We now construct three classes of coverings on $\mathbf{CGWH}_\alpha$, for $\alpha$ the limit ordinal constructed in Construction E.3.5.1, depending on the basic setup $(S_0, \nu)$ chosen in Construction E.3.5.1.

**Definition E.3.5.2.** We define:

(1) The class $\mathrm{Cov}_0(\mathbf{CGWH}_\alpha)$ whose elements are families of closed immersions $\{f_i : T_i \to T\}_{i \in I}$ for $I \in \mathrm{Sets}_{\le \nu}$ and $T \in S_0$, for $(S_0, \nu)$ the basic setup constructed in Construction E.3.5.1, and $T_i$ a compact Hausdorff subspace of $T$ and $f_i$ the resulting closed (since $T$ is weakly Hausdorff) immersion for all $i \in I$.

(2) The class $\mathrm{Cov}_1(\mathbf{CGWH}_\alpha)$ whose elements are families of continuous maps $\{f_i : T_i \to T\}_{i \in I}$ of $\alpha$-small compactly generated weakly Hausdorff spaces such that the induced continuous map

$$
\coprod_{i \in I} f_i : \coprod_{i \in I} T_i \to T
$$

is a submersive map.

(3) The class $\mathrm{Cov}_2(\mathbf{CGWH}_\alpha)$ whose elements are families of open immersions $\{f_i : T_i \to T\}_{i \in I}$ of $\alpha$-small compactly generated weakly Hausdorff spaces such that the induced continuous map

$$
\coprod_{i \in I} f_i : \coprod_{i \in I} T_i \to T
$$

is surjective.

## PDF page 881

**E.3. SMALL COMPACTLY GENERATED WEAKLY HAUSDORFF SPACES** · **881**

We call the elements of the class $\mathrm{Cov}_0(\mathbf{CGWH}_\alpha)$ *fundamental coverings*, the elements of the class $\mathrm{Cov}_1(\mathbf{CGWH}_\alpha)$ *submersive coverings*, and the elements of the class $\mathrm{Cov}_2(\mathbf{CGWH}_\alpha)$ *open coverings*.

We need the following:

**Lemma E.3.5.3.** *The class $\mathrm{Cov}_0(\mathbf{CGWH}_\alpha)$ is a set.*

*Proof.* The class $\mathrm{Cov}_0(\mathbf{CGWH}_\alpha)$ is a sub-class of:

$$
\coprod_{(T,I) \in S_0 \times \mathrm{Sets}_{\le \nu}} \mathrm{Map}(I, \mathrm{CH}(T))
$$

where $\mathrm{CH}(T)$ is the set of all compact Hausdorff subspaces of $T$, and $\mathrm{Map}(I, \mathrm{CH}(T))$ is the set of set-functions $I \to \mathrm{CH}(T)$. Indeed, given an element $\mathcal{U} := \{f_i : T_i \to T\}_{i \in I}$ of $\mathrm{Cov}_0(\mathbf{CGWH}_\alpha)$, we may define $q(\mathcal{U}) := f \in \mathrm{Map}(I, \mathrm{CH}(T))$, where $f : I \to \mathrm{CH}(T)$ is defined as $f(i) := T_i$. We see that $q$ is an injective class function:

$$
q : \mathrm{Cov}_0(\mathbf{CGWH}_\alpha) \to \coprod_{(T,I) \in S_0 \times \mathrm{Sets}_{\le \nu}} \mathrm{Map}(I, \mathrm{CH}(T))
$$

and by the Axiom of Separation $\mathrm{Cov}_0(\mathbf{CGWH}_\alpha)$ is a set since $\mathrm{Map}(I, \mathrm{CH}(T))$ is, and the co-product is indexed by a product of two sets, so it is therefore itself a set. $\square$

We proceed as in [SP, Tag 000W] to obtain a site in the sense of [SP, Tag 00VH], and [KS, Ch. 16-17].

**Construction E.3.5.4.** By [SP, Tag 000W], we pick out a *set* of coverings in $\mathrm{Cov}_1(\mathbf{CGWH}_\alpha)$ and $\mathrm{Cov}_2(\mathbf{CGWH}_\alpha)$, as follows. There exists a cardinal $\kappa$ and a limit ordinal $\beta$, such that:

$$
\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}, \text{ for } i = 1, 2 \tag{E.3.5.1}
$$

is a set of submersive coverings, for $i = 1$, respectively open coverings, for $i = 2$, contained within the classes $\mathrm{Cov}_1(\mathbf{CGWH}_\alpha)$, respectively $\mathrm{Cov}_2(\mathbf{CGWH}_\alpha)$, such that:

(1) $\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$ contains $\mathrm{Cov}_0(\mathbf{CGWH}_\alpha)$ for $i = 1, 2$.

(2) $\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$ is contained in the Von Neumann universe $V_\beta$ for $i = 1, 2$.

(3) For every $\{f_i : T_i \to T\}_{i \in I} \in \mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$, for $i = 1, 2$, we have $|I| \le \kappa$.

(4) For every $\{f_i : T_i \to T\}_{i \in I} \in \mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$, for $i = 1, 2$, the defining axioms for coverings (see [SP, Tag 00VH]) hold.

(5) every element in $\mathrm{Cov}_1(\mathbf{CGWH}_\alpha)$, respectively $\mathrm{Cov}_2(\mathbf{CGWH}_\alpha)$, is combinatorially equivalent to (informally: has a refinement coming from) some element of $\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$, for $i = 1, 2$ respectively.

That large enough $\kappa$ and $\beta$ as in Construction E.3.5.4 exist is the content of [SP, Tag 000W].

**Definition E.3.5.5.** We define:

(1) $J_1$ the topology on $\mathbf{CGWH}_\alpha$ generated by $\mathrm{Cov}_1(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$. We refer to $J_1$ as the *submersive-covering topology* on $\mathbf{CGWH}_\alpha$.

(2) $J_2$ the topology on $\mathbf{CGWH}_\alpha$ generated by $\mathrm{Cov}_2(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$. We refer to $J_2$ as the *open-covering topology* on $\mathbf{CGWH}_\alpha$.

**Remark E.3.5.6.** On Definition E.3.5.5, we make the following observations.

(1) The pairs $(\mathbf{CGWH}_\alpha, \mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta})$ are sites in the sense of [SP, Tag 00VH], and in the sense of [KS, Ch. 17, Def. 17.2.1]. We further refer the reader to [KS, Ch. 16, Def. 16.1.2], [KS, Ch. 16, Def. 16.1.5], and [SP, Tag 00YW] on how to relate the two approaches to the construction of categories of sheaves of sets on sites whose underlying categories are small, through the concept of topology generated by a set of coverings (see [KS, Ch. 16, Def. 16.1.5] and the discussion from [KS, Ch. 16, p. 392] following the Definition, and [SP, Tags 00YZ, 00Z1]). In particular, the pairs $(\mathbf{CGWH}_\alpha, J_1)$ and $(\mathbf{CGWH}_\alpha, J_2)$ are sites in the sense of [KS, Ch. 17, Def. 17.2.1].

## PDF page 882

**882** · **CHAPTER E. TOPOLOGICAL STACKS**

(2) We recall that the topology (in the sense of [SP, Tag 00Z4], which is also [KS, Ch. 16, Def. 16.1.2]) on the small category (pre-site, in the terminology of [KS, Ch. 17, Def. 17.1.1]) $\mathbf{CGWH}_\alpha$ *generated* by $\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$ for $i = 1, 2$ respectively is the assignment $T \rightsquigarrow J_i(T)$, for every object $T \in \mathrm{Ob}(\mathbf{CGWH}_\alpha)$, where $J_i(T)$ is the set of sieves $S \subset h_T$ of the form $S_{\mathcal{U}} = S(\{f_j : T_j \to T\}_{j \in I})$, for some element $\mathcal{U} = \{f_j : T_j \to T\}_{j \in I} \in \mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\alpha}$, where $S_{\mathcal{U}}$ is the unique smallest sieve $S$ such that each $f_j$ belongs to $S(T_j)$. Such $S_{\mathcal{U}}$ indeed exists by part (4) of [SP, Tag 00YZ] (see also the discussion on [KS, Ch. 16, §1, p. 392] after [KS, Ch. 16, Def. 16.1.5]).

(3) We note that the topology $J_1$ is finer than the topology $J_2$ (see [SP, Tag 00Z6]), which is to say that for every object $T$ of $\mathbf{CGWH}_\alpha$, $J_2(T) \subset J_1(T)$. Indeed, for any open covering $\{f_i : T_i \to T\}_{i \in I}$, the map:

$$
\coprod_{i \in I} f_i : \coprod_{i \in I} T_i \to T
$$

is open and surjective, and hence submersive by [SP, Tag 02YB]. The element $\{f_i : T_i \to T\}_{i \in I}$ of $\mathrm{Cov}_2(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$ is therefore an element of $\mathrm{Cov}_1(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$ and the sieve it generates is a covering sieve for $J_1$, i.e. it is contained in $J_1(T)$. This shows the containment $J_2(T) \subset J_1(T)$. In particular, to show that $J_2$ is sub-canonical, it is enough to show that $J_1$ is.

(4) We note that the ordinal $\beta$ and the cardinal $\kappa$ in the definition of $\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$ provided by [SP, Tag 000X] for $i = 1, 2$ respectively are a priori distinct, and should be denoted $\beta_1, \kappa_1$ and $\beta_2, \kappa_2$. Upon inspection of the proof of [SP, Tag 000X], one can replace each $\beta_i$, respectively $\kappa_i$, with some $\beta \ge \max\{\beta_1, \beta_2\}$, respectively $\kappa \ge \max\{\kappa_1, \kappa_2\}$, and arrange for the same $\beta$ and the same $\kappa$ to ensure the existence of $\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$, for $i = 1, 2$, satisfying the desired properties.

(5) We note that the dependency of the topologies $J_1, J_2$ on $\mathbf{CGWH}_\alpha$ on $\beta$ and $\kappa$, while a priori stringent, is mitigated by [SP, Tag 00VY], from which we deduce that we may replace $\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)_{\kappa,\beta}$, for $i = 1, 2$, respectively, with any other set of coverings of the same class $\mathrm{Cov}_i(\mathbf{CGWH}_\alpha)$ respectively (see parts (2) and (3) of Definition E.3.5.2) such that every element $\mathcal{U} \in \mathrm{Cov}_i(\mathbf{CGWH}_\alpha)$ is combinatorially equivalent to an element of the set, without changing the topos of sheaves of sets with respect to the resulting topology. In other words, the dependency of the topoi $\mathrm{Shv}(\mathbf{CGWH}_\alpha, J_i)$ for $i = 1, 2$ on $\beta$ and $\kappa$ is not too stringent.

We conclude this section with one final consideration on the topologies $J_1$ and $J_2$. It is that $J_1$ is sub-canonical (and hence so is $J_2$ by part (3) of Remark E.3.5.6). In fact, we shall show that $J_1$ is the canonical topology itself on $\mathbf{CGWH}_\alpha$ (which is, recall, the coarsest topology with respect to which all representable pre-sheaves are sheaves; see [SP, Tag 00ZA], and also [SP, Tags 00Z8,00Z9] applied to the collection of all pre-sheaves of sets).

**Lemma E.3.5.7.** *The topology $J_1$ on $\mathbf{CGWH}_\alpha$ is the canonical topology.*

*Proof.* This is a direct consequence of Proposition E.3.4.4(7), which implies that the covering sieves of $J_1$ are exactly those generated by jointly surjective families of universal effective epimorphisms. By [SGA3, Exp. IV, Prop. 2.3], $J_1$ is the canonical topology on $\mathbf{CGWH}_\alpha$. $\square$

**Remark E.3.5.8.** We point out to the reader [Les, Prop. 4.7], where a characterization of the canonical topology on $\mathbf{CGWH}$ is provided. This can be used to deduce Lemma E.3.5.7. We caution the reader that we have endeavoured to only define topologies on “pre-sites” in the sense of [KS, Ch. 17, Def. 17.1.1], hence without allowing large categories. One can, however, define the concept of a Grothendieck topology on any category, as in [SGA4, Exp. II, §1], and hence define the canonical topology as in [SGA4, Exp. II, §2, Def. 2.5]. We further point out that, in this sense, one can define the canonical topology on the large category $\mathbf{Spaces}$. It turns out that it is defined by those covering sieves generated by families of maps that are jointly surjective and jointly universally submersive, where a continuous map is universally submersive if and only if it remains

## PDF page 883

**E.4. TOPOLOGICAL GROUPOIDS** · **883**

submersive under arbitrary topological base change. It is a feature of $\mathbf{CGWH}$ that submersive maps are stable under arbitrary base change internally in $\mathbf{CGWH}$ (see Lemma E.2.3.6(6)), and one that does not hold not only in $\mathbf{Spaces}$ but also in $\mathbf{CG}$, the category of compactly generated spaces (see Example E.1.2.16). This is one of the reasons for adopting $\mathbf{CGWH}$ as ambient category for the relevant site.

We conclude by introducing some terminology, to be used throughout the remainder of this appendix.

**Definition E.3.5.9.** For the choice of limit ordinal $\alpha$ made in Construction E.3.5.1, and for the choices of cardinal $\kappa$ and limit ordinal $\beta$ made in Construction E.3.5.4, we denote by:

(1) $\mathbf{CGWH}_{\alpha,\tau}$ the site $(\mathbf{CGWH}_\alpha, J_1)$.

(2) $\mathbf{CGWH}_{\alpha,\sigma}$ the site $(\mathbf{CGWH}_\alpha, J_2)$.

We refer to $\mathbf{CGWH}_{\alpha,\tau}$ as the *topological $\tau$-site*, and to $\mathbf{CGWH}_{\alpha,\sigma}$ as the *topological $\sigma$-site*.

We will be mostly using the topological $\tau$-site throughout the remainder of this appendix, with only occasional reference to the $\sigma$-site. In other words, the “open-covering” topology will play a very limited role.

**E.4. Topological groupoids**

The stacks of interest for the purposes of this appendix will always be fibered in groupoids. In fact they will always be quotient stacks associated to explicit topological groupoids. The aim of this section is to collect here what is needed on the subject of topological groupoids for our later use with 2-categorical constructions in §E.5-§E.6.

**E.4.1. Groupoids in sets and internal groupoids.** There exist several sources within the literature covering some of the material of this section. We will be occasionally following [Hig], [CdSW, Part VI] and [N, §3.2]. In terms of notation, we follow the notational choices of [SP, Tag 022L] closely, in analogy with [SP, Tag 0437] for “groupoids in schemes” and “groupoids in spaces”, so as to facilitate the reader who wishes to skip this section and the next on a first reading and rely on their own familiarity with the algebraic counterparts of the topics discussed within them.

We first recall the following:

**Definition E.4.1.1.** A *groupoid in sets* is the datum $(X, R, s, t, c, e, i)$ of:

(i) a set denoted $X$ which we shall refer as the *set of objects*,

(ii) a set denoted $R$ which we shall refer as the *set of morphisms*,

(iii) set-functions $s, t : R \rightrightarrows X$ respectively called *source* and *target* morphisms,

(iv) a set-function

$$
c : R \times_{s,X,t} R \to R
$$

called the *composition law*,

(v) a set-function $e : X \to R$ called the *unit section*,

(vi) a set-function $i : R \to R$ called the *inversion*,

satisfying the following axioms:

(1) Associativity:

(a) the diagrams

(E.4.1.1)

```latex
\begin{tikzcd}[row sep=large, column sep=large]
R \times_{s,X,t} R \arrow[r,"c"] \arrow[d,"\mathrm{pr}_1" left] & R \arrow[d,"t" right] \\
R \arrow[r,"t" below] & X
\end{tikzcd}
\qquad
\begin{tikzcd}[row sep=large, column sep=large]
R \times_{s,X,t} R \arrow[r,"c"] \arrow[d,"\mathrm{pr}_2" left] & R \arrow[d,"s" right] \\
R \arrow[r,"s" below] & X
\end{tikzcd}
```

commute,

## PDF page 884

**884** · **CHAPTER E. TOPOLOGICAL STACKS**

(b) we have the equality of set-functions

$$
c(\mathrm{id}_R, c) = c \circ (c, \mathrm{id}_R) : R \times_{s,X,t} R \times_{s,X,t} R \rightrightarrows R \tag{E.4.1.2}
$$

(2) Identity:

(a) we have the equality of set-functions

$$
s \circ e = t \circ e = \mathrm{id} : X \rightrightarrows X \tag{E.4.1.3}
$$

(b) we have the equalities of pairs of set-functions

$$
c \circ (\mathrm{id}, (e \circ s)) = c \circ ((e \circ t), \mathrm{id}) = \mathrm{id} : R \rightrightarrows R \tag{E.4.1.4}
$$

(3) Inverse:

(a) As set-functions $R \to X$, we have the equality:

$$
s \circ i = t, t \circ i = s : R \to X \tag{E.4.1.5}
$$

(b) As set-functions $R \to R$, we have the equality:

$$
c \circ (i\mathrm{d}, i) = e \circ t, c \circ (i, \mathrm{id}) = e \circ s : R \to R \tag{E.4.1.6}
$$

We call the set-functions $s, t, c, e, i$ the *structure morphisms* of the groupoid.

*Morphisms* of groupoids are pairs of set-functions

$$
f = (f_1 : X \to X', f_2 : R \to R') \tag{E.4.1.7}
$$

compatible with the structure morphisms of $(X, R, s, t, c, e, i)$ and $(X', R', s', t', c', e', i')$; i.e., the following diagrams commute:

(1) (Compatibility with source and target)

(E.4.1.8)

```latex
\begin{tikzcd}[row sep=large, column sep=large]
R \arrow[r] \arrow[d,"s" left] & R' \arrow[d,"s'" right] \\
X \arrow[r] & X'
\end{tikzcd}
\qquad
\begin{tikzcd}[row sep=large, column sep=large]
R \arrow[r] \arrow[d,"t" left] & R' \arrow[d,"t'" right] \\
X \arrow[r] & X'
\end{tikzcd}
```

(2) (Compatibility with the composition laws)

(E.4.1.9)

```latex
\begin{tikzcd}[row sep=large, column sep=large]
R \times_{s,X,t} R \arrow[r,"{(f_2,f_2)}"] \arrow[d,"c" left] & R' \times_{s',X',t'} R' \arrow[d,"c'" right] \\
R \arrow[r,"f_2" below] & R'
\end{tikzcd}
```

(3) (Compatibility with units)

(E.4.1.10)

```latex
\begin{tikzcd}[row sep=large, column sep=large]
X \arrow[r,"f_1"] \arrow[d,"e" left] & X' \arrow[d,"e'" right] \\
R \arrow[r,"f_2" below] & R'
\end{tikzcd}
```

(4) (Compatibility with inversions)

(E.4.1.11)

```latex
\begin{tikzcd}[row sep=large, column sep=large]
R \arrow[r,"f_2"] \arrow[d,"i" left] & R' \arrow[d,"i'" right] \\
R \arrow[r,"f_2" below] & R'
\end{tikzcd}
```

## PDF page 885

**E.4. TOPOLOGICAL GROUPOIDS** · **885**

We define the category $\mathbf{Groupoids}$ whose objects are the class of all groupoids in sets and morphisms are morphisms of groupoids.

**Notation E.4.1.1.** We abbreviate the notation $(X, R, s, t, c, e, i)$ to $R \rightrightarrows X$, or $(X, R, s, t, c)$, when no confusion is expected to arise. Moreover, for a morphism between groupoids assigned by a pair of set-functions $(f_1, f_2)$ as in (E.4.1.7), we often write $f$ for both $f_1$ and $f_2$, so as to simplify the notation. Source and target of each $f$ are expected to leave no ambiguity as to whether an $f$ is a set-function on objects or on morphisms.

**Remark E.4.1.2.** On Definition E.4.1.1, we make the following observations:

(1) We note that the datum of a groupoid in sets is equivalent to the datum of an (effective) small category (see Definition E.5.1.15) all of whose morphisms are isomorphisms. Indeed, given a groupoid in sets $(X, R, s, t, c, e, i)$, we may construct the category $\mathcal{C}_R$ whose set of objects is defined to be $\mathrm{Ob}(\mathcal{C}_R) := X$, and whose morphisms are defined as follows. For any pair of objects $x, y \in \mathrm{Ob}(\mathcal{C}_R)$, $\mathrm{Hom}_{\mathcal{C}_R}(x, y) := s^{-1}(x) \cap t^{-1}(y)$. The axioms from Definition E.4.1.1 ensure that the above assignment indeed is a (small) category. We will occasionally use this perspective, especially throughout the development and use of the desired theory of stacks in groupoids on a suitable site on topological spaces. For $g \in \mathcal{R}$ with $s(g) = x$ and $t(g) = y$, we may write $g : x \to y$ to view $g$ as a morphism $x \to y$ in $\mathcal{C}_R$.

(2) In (E.4.1.8) for the definition of morphisms of groupoids, concerning compatibility with the composition laws we note that by (E.4.1.9) on compatibility with source and target morphisms the set-function $(f_2, f_2) : R \times R \to R' \times R'$ restricted to $R \times_{s,X,t} R \subset R \times R$ factors through a set-function $R \times_{s,X,t} R \to R'_{s',X',t'} R'$; it is *this* set-function that is being referred to in Axiom (2) on compatibility with composition laws. We denote this set-function by $(f_2, f_2)$ again, as it is uniquely determined by $(f_2, f_2) : R \times R \to R' \times R'$, expecting no confusion to arise.

We now prove a first lemma that reduces the task of verifying the defining compatibilities of a morphism of groupoids:

$$
(f_1, f_2) : (X, R, s, t, c, e, i) \to (X', R', s', t', c', e', i')
$$

to the task of verifying compatibility of $f_1$ and $f_2$ with $(s, t, c)$ and $(s', t', c')$ only.

**Lemma E.4.1.3.** *Let $(X, R, s, t, c, e, i)$ and $(X', R', s', t', c', e', i')$ be two groupoids in sets. Let $f_1 : X \to X'$ and $f_2 : R \to R'$ be set-functions. The following conditions are equivalent:*

(1) *$(f_1, f_2)$ is a morphism of groupoids.*

(2) *$f_1$ and $f_2$ satisfy the following compatibilities:*

(a) *$s' \circ f_2 = f_1 \circ s$.*

(b) *$t' \circ f_2 = f_1 \circ t$.*

(c) *$f_2 \circ c(\cdot, \cdot) = c'(f_2(\cdot), f_2(\cdot))$.*

*Proof.* In terms of the associated small categories $\mathcal{C}_R$ and $\mathcal{C}_{R'}$, condition (2) says $(f_1, f_2)$ defines a covariant functor $F : \mathcal{C}_R \to \mathcal{C}_{R'}$. Since any covariant functor respects identity maps and inverses of isomorphisms, we are done. $\square$

The following result is also a direct consequence of the axioms, and will be used later.

**Lemma E.4.1.4.** *Let $(X, R, s, t, c, e, i)$ be a groupoid in sets, and $x, y, z, w \in R$ such that:*

(1) *$(x, y)$, $(z, w)$ are elements of $R \times_{s,X,t} R$.*

(2) *$c(x, y) = c(z, w)$.*

*Then:*

$$
c(c(i(y), i(x)), c(z, w)) = (e \circ s)(y) = (e \circ s)(w).
$$

## PDF page 886

**886** · **CHAPTER E. TOPOLOGICAL STACKS**

*Proof.* In terms of the associated small category $\mathcal{C}_R$, we’re given a commutative diagram of isomorphisms


```latex
\begin{tikzcd}[row sep=large, column sep=large]
a \arrow[r,"y"] \arrow[d,"w" left] & b \arrow[d,"x" right] \\
b' \arrow[r,"z" below] & c
\end{tikzcd}
```

and the assertion is $y^{-1}x^{-1}(zw) = \mathrm{id}_a$, which is clear. $\square$

**E.4.2. Groupoids internal to CGWH.** We now assign the notion of groupoid internal to any category. While it will be useful to have the general concept within this appendix, we shall not need it beyond this appendix apart from the notion of groupoids internal to the category $\mathbf{CGWH}$, the large category of topological spaces constructed in Definition E.2.2.1.

**Definition E.4.2.1.** Let $\mathscr{A}$ be a category, and assume fibre products are representable in $\mathscr{A}$. An *$\mathscr{A}$-groupoid* is the datum $(X, \mathcal{R}, s, t, c, e, i)$ with $X, \mathcal{R}$ objects of $\mathscr{A}$, and $s, t : \mathcal{R} \rightrightarrows X$, $c : \mathcal{R} \times_{s,X,t} \mathcal{R} \to \mathcal{R}$, $i : \mathcal{R} \to \mathcal{R}$, $e : X \to \mathcal{R}$ morphisms in $\mathscr{A}$ such that the diagrams as in Definition E.4.1.1 commute. We denote the category of $\mathscr{A}$-groupoids by $\mathscr{A}\text{-}\mathbf{Grpd}$.

A *map of groupoids* $(X, \mathcal{R}) \to (X', \mathcal{R}')$ is a pair of morphisms $f_1 : X \to X'$ and $f_2 : \mathcal{R} \to \mathcal{R}'$ such that the analogues of (E.4.1.8)–(E.4.1.11) commute.

**Remark E.4.2.2.** We define $\mathrm{PShv}(\mathscr{A})$ the functor category $\mathbf{Functors}(\mathscr{A}^{\mathrm{opp}}, \mathbf{Sets})$ and refer to it as the category of *pre-sheaves of sets on $\mathscr{A}$*, following [SGA4, Exp. I, §1, Def. 1.3] and [SP, Tag 00V1]. We denote by:

$$
h : \mathscr{A} \to \mathrm{PShv}(\mathscr{A})
$$

the functor-of-points functor (see [SP, Tag 001O]), defined by the assignment, for every object $X$ of $\mathscr{A}$:

$$
T \rightsquigarrow h_X(T) := \mathrm{Hom}_{\mathscr{A}}(T, X),
$$

and we write $h(f)$ for the effect of $h$ on morphisms $f$ in $\mathscr{A}$, as opposed to $h_f$. In particular, we shall denote by $h(f)(T)$ the value at the object $T$ of $\mathscr{A}$ of the morphism of pre-sheaves of sets $h(f) : h_X \to h_Y$, for a morphism $f : X \to Y$ in $\mathscr{A}$. We may then assign the notion of *groupoid-object in $\mathscr{A}$* by means of analogy with Definition E.4.1.1: a groupoid-object in $\mathscr{A}$ is the datum of objects $X, \mathcal{R}$ of $\mathscr{A}$, and morphisms:

$$
s, t : \mathcal{R} \rightrightarrows X, \quad c : \mathcal{R} \times_{s,X,t} \mathcal{R} \to \mathcal{R}, \quad e : X \to \mathcal{R}, \quad i : \mathcal{R} \to \mathcal{R}
$$

such that for every object $T$ in $\mathscr{A}$, the datum:

$$
(h_X(T), h_{\mathcal{R}}(T), h(s)(T), h(t)(T), h(c)(T), h(e)(T), h(i)(T))
$$

is a groupoid in sets in the sense of Definition E.4.1.1. Morphisms of internal $\mathscr{A}$-groupoids are likewise pairs of morphisms $(f_1, f_2) : (X, \mathcal{R}) \to (X', \mathcal{R}')$ in $\mathscr{A}$ such that $(h(f_1)(T), h(f_2)(T))$ is a morphism of groupoids in sets in the sense of Definition E.4.1.1 for every object $T$ of $\mathscr{A}$.

**Definition E.4.2.3.** We define the category of *topological groupoids* to be the category $\mathbf{CGWH}\text{-}\mathbf{Grpd}$ of Definition E.4.2.1. We shall be referring to the objects of $\mathbf{CGWH}\text{-}\mathbf{Grpd}$ as *topological groupoids*.

The above definition means that we are assuming that both sets of objects and morphisms of the groupoid are compactly generated weakly Hausdorff topological spaces, and that all the structure morphisms are continuous maps. Note that $\mathbf{CGWH}$ does contain all fibre products, by Lemma E.2.2.5(1).

**Remark E.4.2.4.** We observe that for an arbitrary subspace $T \subset X$, the subspaces $s^{-1}(T)$ and $t^{-1}(T)$ of $\mathcal{R}$ may not be compactly generated. When $T = \{x\}$ is a point, however, they both are, since $s, t$ are continuous maps between compactly generated weakly Hausdorff spaces, and weakly Hausdorff spaces are $T_1$-spaces (every

## PDF page 887

**E.4. TOPOLOGICAL GROUPOIDS** · **887**

point is the continuous image of $\{\ast\}$ and thus is closed), hence $T$ is closed, and so are $s^{-1}(T)$ and $t^{-1}(T)$. By Lemma E.1.2.25, these subspaces are compactly generated, and they are weakly Hausdorff (as are all subspaces). This is, more generally, the case when $T$ is open, or locally closed, again by Lemma E.1.2.25.

We have the following:

**Lemma E.4.2.5.** *Let $(X, \mathcal{R}, s, t, c, e, i)$ be a topological groupoid. Then:*

(1) *the unit map $e$ is a closed immersion.*

(2) *The source and target maps $s, t : \mathcal{R} \rightrightarrows X$ are submersive.*

*Proof.* The assertions follow from Lemma E.2.3.4, as $e$ is a continuous section to both $s, t$ and all topological spaces are objects of $\mathbf{CGWH}$. $\square$

**Lemma E.4.2.6.** *Let $(X, \mathcal{R}, s, t, c, e, i)$ be a topological groupoid. Then the fibre product $\mathcal{R} \times^0_{s,X,t} \mathcal{R}$ is closed as a subspace of $\mathcal{R} \times \mathcal{R}$ and so belongs to $\mathbf{CGWH}$ coinciding with $\mathcal{R} \times_{s,X,t} \mathcal{R}$.*

*Proof.* This is a special case of Lemma E.2.2.5(1), but we review the proof in this case for the reader’s convenience. Indeed, we have, as subspaces of $\mathcal{R} \times_0 \mathcal{R}$:

$$
\mathcal{R} \times^0_{s,X,t} \mathcal{R} = (s, t)^{-1}(\Delta_X(X)).
$$

Since $X$ is compactly generated weakly Hausdorff, by Lemma E.2.1.6 the diagonal subspace $\Delta_X(X) \subset X \times_0 X$ is $k$-closed. As $(s, t) : \mathcal{R} \times_0 \mathcal{R} \to X \times_0 X$ is continuous, the subspace $\mathcal{R} \times^0_{s,X,t} \mathcal{R} \subset \mathcal{R} \times_0 \mathcal{R}$ is also $k$-closed. It follows that $\mathcal{R} \times^0_{s,X,t} \mathcal{R}$ is a closed subspace of $\mathcal{R} \times \mathcal{R}$, and as such it is compactly generated by Lemma E.1.2.25(2), and weakly Hausdorff (as are all subspaces of $\mathcal{R} \times \mathcal{R}$). In particular, $\mathcal{R} \times^0_{s,X,t} \mathcal{R} = \mathcal{R} \times_{s,X,t} \mathcal{R}$, as desired. $\square$

**Lemma E.4.2.7.** *Let $(X, \mathcal{R}, s, t, c, e, i)$ be a topological groupoid. For any $x \in X$, the subspace of $\mathcal{R}$:*

$$
\mathcal{R}_x := s^{-1}(x) \cap t^{-1}(x) \tag{E.4.2.1}
$$

*is a compactly generated weakly Hausdorff topological group, closed as a subspace of $\mathcal{R}$.*

*Proof.* As compactly generated weakly Hausdorff spaces are $T_1$-spaces, $\mathcal{R}_x$ is $T_1$ as a subspace of $\mathcal{R}$, and as such it is compactly generated by Lemma E.1.2.25 and weakly Hausdorff (as are all subspaces of $\mathcal{R}$). Since the group law, and the inversion homomorphisms are induced by $c$ and $i$ on $\mathcal{R}$, they are continuous, making $\mathcal{R}_x$ into a topological group. $\square$

There’s an evident formal analogy between the datum of a groupoid in sets and that of an equivalence relation on a set. We make this analogy precise:

**Remark E.4.2.8.** We make the following observations:

(1) Let $(X, R, s, t, c, e, i)$ be a groupoid in sets. Then the image of the set-function:

$$
(t, s) : R \to X \times X
$$

is an equivalence relation on $X$. Note the order of source and target morphisms being exchanged in the definition of $(t, s)$. Conversely, given an equivalence relation $R \subset X \times X$, there exists, up to isomorphism of groupoids in sets, a unique groupoid:

$$
(X, R', s, t, c, e, i)
$$

such that:

(1) $j : R' \to X \times X$ is injective.

(2) $R = j(R') \subset X \times X$.

## PDF page 888

**888** · **CHAPTER E. TOPOLOGICAL STACKS**

Indeed, we may set $R' := R$, and $s, t$ the compositions of the inclusion $R \subset X \times X$ with the two projections $p_2, p_1 : X \times X \to X$, respectively, where $p_1$ is the left projection, and $p_2$ is the right projection.

(2) If $(X, \mathcal{R}, s, t, c, e, i)$ is a topological groupoid, then the image of $(t, s)$ endowed with the subspace topology is a topological equivalence relation on $X \times X$, and the above construction provides a method to construct a topological groupoid from a topological equivalence relation. We caution the reader that such relation may not be closed, as is typically the case when the groupoid is an action groupoid associated to the continuous, non-proper action of a (compactly generated weakly Hausdorff) topological group.

Beware that the topology on the image of $(t, s)$ is, by convention, the quotient topology and this may not be the subspace topology inherited from $X \times X$; i.e., $(t, s)$ may not be a strict map (see part (3) of Terminology E.0.0.2). Topological groupoids therefore generalize the assignment of topological equivalence relations, allowing more flexibility beyond the case of immersed equivalence relations in $X \times X$. The resulting quotients therefore necessitate a more robust geometric theory than that of topological quotients, which leads us to the necessity of an appropriate theory of stacks, to supply the otherwise missing geometric objects serving as the quotients.

E.4.2.1. *Constant groupoids.* The following construction and the subsequent Lemma explain how one can view a space $X$ as a “constant” topological groupoid.

**Construction E.4.2.9.** Let $X$ be an object in $\mathbf{CGWH}$. We denote by $\mathbf{Const}_X$ the datum:

$$
(X, \Delta(X), s = \mathrm{id}, t = \mathrm{id}, e = \mathrm{id}, c = \mathrm{id}, i = \mathrm{id}) \tag{E.4.2.2}
$$

where $\Delta(X)$ is the diagonal subspace within $X \times X$. Then $\mathbf{Const}_X$ is a topological groupoid.

**Definition E.4.2.10.** For $X$ a compactly generated weakly Hausdorff space, we refer to $\mathbf{Const}_X$ as the *constant groupoid* on $X$.

**Lemma E.4.2.11.** *The assignment $\mathrm{Const}$ defined as $X \rightsquigarrow \mathbf{Const}_X$ on objects of $\mathbf{CGWH}$ and as $(f, f) : \mathbf{Const}_X \to \mathbf{Const}_Y$ on morphisms $f : X \to Y$ in $\mathbf{CGWH}$, is a fully faithful functor:*

$$
\mathrm{Const} : \mathbf{CGWH} \to \mathbf{CGWH}\text{-}\mathbf{Grpd}. \tag{E.4.2.3}
$$

*Proof.* The set $\mathrm{Hom}_{\mathbf{CGWH}}(X, Y)$ is sent under $\mathrm{Const}$ onto the subset of

$$
\mathrm{Hom}_{\mathbf{CGWH}\text{-}\mathbf{Grpd}}(\mathbf{Const}_X, \mathbf{Const}_Y)
$$

given by the pairs of maps $f = (f_1 : X \to Y, f_2 : \Delta(X) \to \Delta(Y))$ where $f_1 = f_2$. The spaces of morphisms of $\mathbf{Const}_X, \mathbf{Const}_Y$ contain the identities only, and so this subset is the entire Hom-set in $\mathbf{CGWH}\text{-}\mathbf{Grpd}$, since the only morphisms $(f, f') : \mathbf{Const}_X \to \mathbf{Const}_Y$ of topological groupoids must, for every $x \in X$, preserve the identities; i.e., $f'(e(x)) = e'(f(x))$. This forces $f = f'$, which is what we needed to show. $\square$

E.4.2.2. *Action groupoids.* We show how to assign a topological groupoid to the datum of an action of a compactly generated weakly Hausdorff topological group $G$ on a compactly generated weakly Hausdorff space $X$. For such $G$ and $X$, we assume that $G$ acts on $X$ continuously via a morphism in $\mathbf{CGWH}$:

$$
a : G \times X \to X. \tag{E.4.2.4}
$$

**Construction E.4.2.12.** We denote by $G \times X \rightrightarrows X$ the topological groupoid assigned by the datum $(X, \mathcal{R}, s, t, c, e, i)$, where

$$
\mathcal{R} := G \times X \tag{E.4.2.5}
$$

and

$$
s, t : \mathcal{R} \rightrightarrows X, \quad (g, x) \rightsquigarrow s(g, x) := x, \quad (g, x) \mapsto t(g, x) := a(g, x), \tag{E.4.2.6}
$$

## PDF page 889

**E.5. 2-CATEGORICAL PREPARATIONS** · **889**

with $a : G \times X \to X$ the action map from (E.4.2.4). We further define:

$$
c : \mathcal{R} \times_{s,X,t} \mathcal{R} \to \mathcal{R}, \quad ((g,x),(g',x')) \mapsto c((x,g),(x',g')) := (gg',x') \tag{E.4.2.7}
$$

and:

$$
e : X \to \mathcal{R}, \quad x \mapsto e(x) := (1,x) \tag{E.4.2.8}
$$

$$
i : \mathcal{R} \to \mathcal{R} \quad (g,x) \mapsto i(g,x) := (g^{-1},a(g,x)). \tag{E.4.2.9}
$$

The datum $G \times X \rightrightarrows X$ indeed assigns a topological groupoid in the sense of Definition E.4.2.3.

**E.5. 2-categorical preparations**

In this subsection we collect background material on 2-categories, up to and including the concept of 2-fibre products. We will then include some examples of interest, and explain how the category of $\mathscr{A}$-groupoids is a 2-category in a natural manner.

2-categories were first introduced, in their “strict” form by J. Bénabou in [Be, Example (5)] and J.-M. Maranda in [Mar, Def. 1], building in some measure on Ehresmann’s work on double categories and structured categories ([Ehr1] and [Ehr2]). Our main references will be [Bor1, Ch. 7], [GR, Ch. 2], M. Hakim’s Ph.D. thesis [Ha, Ch. 1], alongside [SP, Tag 003G] and [SP, Tag 003O]. Our aim is to give a self-contained treatment of a special case of the theory of 2-categories, encompassing only basic terminology and constructions, and including a concrete discussion of 2-fibre products in (strict) (2,1)-categories. These will suffice for all intended applications, insofar the category of stacks in groupoids on the topological site $\mathbf{CGWH}_{\alpha,\tau}$ that was constructed in §E.3.5 will be one example of such a (strict) (2,1)-category, and all constructions of interest to this appendix will be performed intrinsically within it.

The concept of a 2-category serves the purpose of keeping track of morphisms between morphisms, a notion that often arises when studying moduli spaces of structures equipped with non-trivial symmetries.

We begin by describing the structures that are present within the category of all small categories, for later axiomatizing them into the concept of a 2-category. This example will serve as guidance and will justify the terminology that we shall be introducing accordingly afterwards. It will also enable us to construct more examples and, most importantly, once we formally endow the category of all small categories with the structure of a 2-category it will contain, in the appropriate 2-categorical sense, all examples of 2-categories of main focus within this appendix. The various operations and constructions that will be discussed explicitly for it will thereby encompass all cases of interest. In this section, functors are understood to be *covariant*.

**E.5.1. The category of all small categories.** Main sources for the material discussed in this section are [SP, Tag 003D] and [Bor1, Ch. 7, §7.1].

E.5.1.1. *The categories* $\mathbf{Cat}$ *and* $\mathbf{Cat}^{*}$. We begin with a Definition:

**Definition E.5.1.1.** We call $\mathbf{Cat}$ the category whose objects are small categories, and whose morphisms are functors between small categories.

The category $\mathbf{Cat}$ is endowed with more structure than that of an ordinary category. Namely, for any pair of small categories $A, B$, and any two functors $F, F' : A \rightrightarrows B$, we also have all natural transformations of functors, denoted $F \Rightarrow F'$, and it is the purpose of this section to recall how to record such additional structure within $\mathbf{Cat}$ in a robust manner.

Before axiomatizing it into the notion of a 2-category, of which $\mathbf{Cat}$ will turn out to be a first example, we describe some operations on objects, morphisms and natural transformations of functors within $\mathbf{Cat}$.

## PDF page 890

**CHAPTER E. TOPOLOGICAL STACKS** · **890**

E.5.1.2. *Structures on the category of all small categories.* For a triple of small categories $A, B, C$, and functors $F : A \to B$ and $G : B \to C$, we may compose functors to obtain the functor:

$$
G \circ F : A \to C. \tag{E.5.1.1}
$$

For a triple of functors between a fixed pair of small categories $F, F', F'' : A \rightrightarrows B$, we may consider natural transformations $t : F \Rightarrow F'$ and $t' : F' \Rightarrow F''$, and compose them to obtain a natural transformation which we denote:

$$
t' \odot t : F \Rightarrow F''. \tag{E.5.1.2}
$$

We call $\odot$ from (E.5.1.2) the *vertical composition* of natural transformations of functors.

**Notation E.5.1.1.** We let $A, B$ be small categories and $F : A \to B$ a functor.

(1) We denote by $\mathbf{1}_{F}$ the identity natural transformation $\mathbf{1}_{F} : F \Rightarrow F$.

(2) We denote, for $A = B$, by $\mathrm{id}_{A}$ the identity functor $F : A \to A$, sending every object and morphism of $A$ to itself.

In particular, for any small category $A$, $\mathbf{1}_{\mathrm{id}_{A}}$ denotes the identity natural transformation of the identity functor on $A$.

**Lemma E.5.1.2.** *Let $A, B$ be small categories, $F, F' : A \rightrightarrows B$ functors and $t : F \Rightarrow F'$ a natural transformation of functors. Then we have:*

$$
\mathbf{1}_{F} \odot t = t \odot \mathbf{1}_{F} = t \tag{E.5.1.3}
$$

*making $\mathbf{1}_{F}$ a unit for the vertical composition $\odot$ of natural transformations. Moreover, $\odot$ is associative.*

*Proof.* For an arbitrary object $a$ of $A$, we have:

$$
(\mathbf{1}_{F} \odot t)_{a} = \mathrm{id}_{F(a)} \circ t_{a} = t_{a} = t_{a} \circ \mathrm{id}_{F(a)} = (t \odot \mathbf{1}_{F})_{a}
$$

where the innermost compositions are as morphisms in $B$. Associativity of $\odot$ is a direct consequence of associativity of composition of morphisms in any category. □

As a direct consequence of the definition in (E.5.1.2) and Lemma E.5.1.2, for small categories $A, B$ we may define:

$$
\mathbf{Hom}_{\mathbf{Cat}}(A,B) \tag{E.5.1.4}
$$

to be the category of functors $A \to B$, whose morphisms are natural transformations of functors, and whose composition law is $\odot$.

**Situation E.5.1.3.** We fix a triple of small categories $A, B, C$ and two pairs of functors $F, F' : A \rightrightarrows B$ and $G, G' : B \rightrightarrows C$, we consider natural transformations $t : F \Rightarrow F'$ and $s : G \Rightarrow G'$.

We can compose $t$ and $s$ from Situation E.5.1.3 as well, to obtain a natural transformation:

$$
s \star t : G \circ F \Rightarrow G' \circ F'. \tag{E.5.1.5}
$$

We shall call it *horizontal composition* of natural transformations of functors. Constructing $s \star t$ (mainly that two possible definitions agree) and proving its properties is one of the main purposes of this subsection.

**Remark E.5.1.4.** We recall for the reader, in the hope of motivating this endeavor, that all examples of 2-categories of interest throughout this work will be encompassed by $\mathbf{Cat}$ in the appropriate sense. Vertical and horizontal compositions of natural transformations of functors will, in particular, be taking place, or at least be computable, within $\mathbf{Cat}$. The constructions contained within this subsection will therefore cover all cases of interest.

## PDF page 891

**E.5. 2-CATEGORICAL PREPARATIONS** · **891**

We start with the case $G = G'$ and $s = \mathbf{1}_{G}$.

**Construction E.5.1.5.** Let $A, B, C$ be a triple of small categories, and $F, F' : A \rightrightarrows B$ a pair of functors. Let $G : B \to C$ be a functor, and $t : F \Rightarrow F'$ a natural transformation as in Situation E.5.1.3. We call $\mathbf{1}_{G} \star t$ the natural transformation:

$$
\mathbf{1}_{G} \star t : G \circ F \Rightarrow G \circ F' \tag{E.5.1.6}
$$

defined as follows. For any object $a \in A$, we assign:

$$
(\mathbf{1}_{G} \star t)_{a} := G(t_{a}) : (G \circ F)(a) \to (G \circ F')(a) \tag{E.5.1.7}
$$

where $t_{a}$ is the morphism $F(a) \to F'(a)$ in $B$ induced by the natural transformation $t : F \Rightarrow F'$ evaluated at the object $a \in \mathrm{Ob}(A)$. One checks that $\mathbf{1}_{G} \star t$ indeed is a natural transformation since for any morphism $f : a \to a'$ in $A$, the following diagram in $B$ commutes

(E.5.1.8)


```latex
\begin{tikzcd}[row sep=large, column sep=large]
F(a) \arrow[r, "t_{a}"] \arrow[d, "F(f)"'] & F'(a) \arrow[d, "F(f)"] \\
F(a') \arrow[r, "t_{a'}"'] & F'(a')
\end{tikzcd}
```

and upon evaluating $G$ on the (E.5.1.8), we obtain a morphism

$$
(G \circ F)(f) : (G \circ F)(a) \to (G \circ F)(a') \tag{E.5.1.9}
$$

exhibiting naturality of $G(t_{a})$ as a consequence of naturality of $t_{a}$ with respect to morphisms in $A$. Compatibility with compositions of morphisms in $A$ is a consequence of both naturality of $t$ and functoriality of $F$ and $G$.

The following is straightforward.

**Lemma E.5.1.6.** *Let $A, B, C$ be a triple of small categories, and $F, F', F'$ a triple of functors from $A$ to $B$. Let $G : B \to C$ be a functor, and $t : F \Rightarrow F'$, $t' : F' \Rightarrow F''$ natural transformations. We have:*

$$
\mathbf{1}_{G} \star \mathbf{1}_{F} = \mathbf{1}_{G \circ F}, \quad (\mathbf{1}_{G} \star t') \odot (\mathbf{1}_{G} \star t) = \mathbf{1}_{G} \star (t' \odot t) \tag{E.5.1.10}
$$

*and:*

$$
\mathbf{1}_{\mathrm{id}_{A}} \star t = t \tag{E.5.1.11}
$$

*In particular, the assignment:*

$$
G_{*} := G \circ (\cdot) : \mathbf{Hom}_{\mathbf{Cat}}(A,B) \to \mathbf{Hom}_{\mathbf{Cat}}(A,C)
$$

*is a functor.*

Within Situation E.5.1.3, we now construct horizontal compositions of natural transformations in the case $F = F'$, $t = \mathbf{1}_{F}$ and $s$ is an arbitrary natural transformation $s : G \Rightarrow G'$.

**Construction E.5.1.7.** Let $A, B, C$ be a triple of small categories, and $F : A \to B$ a functor. Let $G, G' : B \rightrightarrows C$ be a pair of functors, and $s : G \Rightarrow G'$ a natural transformation. We call $s \star \mathbf{1}_{F}$ the natural transformation:

$$
s \star \mathbf{1}_{F} : G \circ F \Rightarrow G' \circ F \tag{E.5.1.12}
$$

defined as follows. For any object $a \in A$, we assign:

$$
(s \star \mathbf{1}_{F})_{a} := s_{F(a)} : (G \circ F)(a) \to (G \circ F')(a) \tag{E.5.1.13}
$$

## PDF page 892

**CHAPTER E. TOPOLOGICAL STACKS** · **892**

where $s_{F(a)}$ is the morphism $(G \circ F)(a) \to (G' \circ F)(a)$ in $C$ induced by the natural transformation $s : G \Rightarrow G'$. To check that $s \star \mathbf{1}_{F}$ indeed is a natural transformation, we observe that $s_{F(a)}$ is natural with respect to morphisms on $a$ by functoriality of $F$ and naturality of $s$.

**Lemma E.5.1.8.** *Let $A, B, C$ be a triple of small categories, and $F : A \to B$ a functor. Let $G, G', G''$ a triple of functors from $B$ to $C$, and $s : G \Rightarrow G'$, $s' : G' \Rightarrow G''$ natural transformations. We have:*

$$
(s' \star \mathbf{1}_{F}) \odot (s \star \mathbf{1}_{F}) = (s' \odot s) \star \mathbf{1}_{F} \tag{E.5.1.14}
$$

*and:*

$$
s \star \mathbf{1}_{\mathrm{id}_{B}} = s \tag{E.5.1.15}
$$

*In particular, the assignment:*

$$
F^{*} := (\cdot) \circ F : \mathbf{Hom}_{\mathbf{Cat}}(B,C) \to \mathbf{Hom}_{\mathbf{Cat}}(A,C)
$$

*is a functor.*

*Proof.* To check all the identities, it is enough to evaluate them on an arbitrary object $a$ of $A$, respectively an arbitrary object $b$ of $B$, as the reader may carry out. □

We further note that these constructions are compatible with one another in the following sense:

**Lemma E.5.1.9.** *We have:*

$$
\mathbf{1}_{G_{1}} \star (\mathbf{1}_{G_{2}} \star t) = \mathbf{1}_{G_{1} \circ G_{2}} \star t \tag{E.5.1.16}
$$

*for any natural transformation of functors $t : F \Rightarrow F' : A \to B$, and functors $G_{2} : B \to C$ and $G_{1} : C \to D$. We further have:*

$$
(s \star \mathbf{1}_{F_{1}}) \star \mathbf{1}_{F_{2}} = s \star \mathbf{1}_{F_{1} \circ F_{2}} \tag{E.5.1.17}
$$

*for any natural transformation of functors $s : G \Rightarrow G' : C \to D$ and functors $F_{2} : A \to B$ and $F_{1} : B \to C$. Moreover, for any natural transformation of functors $s : G \Rightarrow G' : B \to C$, and any functors $F : A \to B$ and $H : C \to D$, we have:*

$$
\mathbf{1}_{H} \star (s \star \mathbf{1}_{F}) = (\mathbf{1}_{H} \star s) \star \mathbf{1}_{F}. \tag{E.5.1.18}
$$

*Proof.* The result is obtained analogously to Lemma E.5.1.6 and Lemma E.5.1.8, by evaluating all natural transformations on objects and deducing the desired identities from the definitions alone, using functoriality of the component functors and naturality of the component natural transformations. □

We have the following:

**Lemma E.5.1.10.** *We let $F, F' : A \rightrightarrows B$ and $G, G' : B \rightrightarrows C$ be functors between small categories, and let $t : F \Rightarrow F'$ and $s : G \Rightarrow G'$ be natural transformations of functors. Then the following identity of natural transformations of functors $A \to C$ holds:*

$$
(\mathbf{1}_{G'} \star t) \odot (s \star \mathbf{1}_{F}) = (s \star \mathbf{1}_{F'}) \odot (\mathbf{1}_{G} \star t). \tag{E.5.1.19}
$$

This result is obtained analogously to Lemma E.5.1.6 and Lemma E.5.1.8, by evaluating all natural transformations on objects and deducing the desired identities from the definitions alone, using functoriality of the component functors and naturality of the component natural transformations. We further refer the reader to [SP, Tag 003D].

**Definition E.5.1.11.** For $t : F \Rightarrow F'$ and $s : G \Rightarrow G'$ two natural transformations of the functors $F, F' : A \rightrightarrows B$ and $G, G' : B \rightrightarrows C$, define

$$
s \star t := (\mathbf{1}_{G'} \star t) \odot (s \star \mathbf{1}_{F}) : G \circ F \Rightarrow G' \circ F'. \tag{E.5.1.20}
$$

## PDF page 893

**E.5. 2-CATEGORICAL PREPARATIONS** · **893**

In light of Lemma E.5.1.10, the construction of $s \star t$ is well-posed. This is the alternate notion of composition for natural transformations of functors promised in (E.5.1.5), which we shall refer to as *horizontal composition*.

We now establish properties of the two composition laws $\star$ and $\odot$ on natural transformations.

**Lemma E.5.1.12.** *The composition $\star$ is associative, and for every small category $A$, the identity natural transformation $\mathbf{1}_{\mathrm{id}_{A}}$ of the identity functor is a unit for both $\odot$ and $\star$.*

*Proof.* We let $A, B, C, D$ be four small categories, and $F, F' : A \rightrightarrows B$, $G, G' : B \rightrightarrows C$, $H, H' : C \rightrightarrows D$ three pairs of functors. We let $t : F \Rightarrow F'$, $s : G \Rightarrow G'$ and $r : H \Rightarrow H'$ be three natural transformations of functors. For an arbitrary object $a$ of $A$, we have:

$$
((r \star s) \star t)_{a} = ((\mathbf{1}_{H' \circ G'} \star t) \odot ((r \star s) \star \mathbf{1}_{F}))_{a}
$$

$$
= ((\mathbf{1}_{H' \circ G'} \star t) \odot (((\mathbf{1}_{H'} \star s) \odot (r \star \mathbf{1}_{G})) \star \mathbf{1}_{F}))_{a}
$$

$$
= (\mathbf{1}_{H' \circ G'} \star t)_{a} \circ ((\mathbf{1}_{H'} \star s) \odot (r \star \mathbf{1}_{G}))_{F(a)}
$$

$$
= H'(G'(t_{a})) \circ H'(s_{F(a)}) \circ r_{G(F(a))}.
$$

We also have:

$$
(r \star (s \star t))_{a} = ((\mathbf{1}_{H'} \star (s \star t)) \odot (r \star \mathbf{1}_{G \circ F}))_{a}
$$

$$
= H'((s \star t)_{a}) \circ r_{G(F(a))}
$$

$$
= H'((\mathbf{1}_{G'} \star t)_{a} \circ (s \star \mathbf{1}_{F})_{a}) \circ r_{G(F(a))}
$$

$$
= H'(G'(t_{a})) \circ H'(s_{F(a)}) \circ r_{G(F(a))}.
$$

We deduce that $(r \star s) \star t = r \star (s \star t)$. For every small category $A$, the identity natural transformation of the identity functor $\mathbf{1}_{\mathrm{id}_{A}}$ is a unit for both $\odot$ by Lemma E.5.1.2 applied to $F = \mathbf{1}_{\mathrm{id}_{A}}$, and for $\star$ by (E.5.1.11) from Lemma E.5.1.6 and (E.5.1.15) from Lemma E.5.1.8. □

**Lemma E.5.1.13.** *Let $A, B, C$ be three small categories, and consider triples of functors $F, F', F''$ from $A$ to $B$ and $G, G', G''$ from $B$ to $C$ equipped with natural transformations $t : F \Rightarrow F'$, $t' : F' \Rightarrow F''$, $s : G \Rightarrow G'$, and $s' : G' \Rightarrow G''$. Then we have:*

$$
(s' \odot s) \star (t' \odot t) = (s' \star t') \odot (s \star t). \tag{E.5.1.21}
$$

*Proof.* For any object $a$ of $A$, we have:

$$
((\mathbf{1}_{G''} \star (t' \odot t)) \odot ((s' \odot s) \star \mathbf{1}_{F}))_{a} = (\mathbf{1}_{G''} \star (t' \odot t))_{a} \circ ((s' \odot s) \star \mathbf{1}_{F})_{a}
$$

$$
= G''(t'_{a} \circ t_{a}) \circ (s'_{F(a)} \circ s_{F(a)})
$$

$$
= G''(t'_{a}) \circ G''(t_{a}) \circ s'_{F(a)} \circ s_{F(a)}
$$

$$
= ((\mathbf{1}_{G''} \star t') \odot (\mathbf{1}_{G''} \star t) \odot (s' \star \mathbf{1}_{F}) \odot (s \star \mathbf{1}_{F}))_{a}
$$

$$
= ((\mathbf{1}_{G''} \star t') \odot ((s' \star \mathbf{1}_{F'}) \odot (\mathbf{1}_{G'} \star t)) \odot (s \star \mathbf{1}_{F}))_{a}
$$

and by Lemma E.5.1.2 on associativity of $\odot$, we deduce:

$$
(\mathbf{1}_{G''} \star t') \odot ((s' \star \mathbf{1}_{F'}) \odot (\mathbf{1}_{G'} \star t)) \odot (s \star \mathbf{1}_{F}) = ((\mathbf{1}_{G''} \star t')) \odot (s' \star \mathbf{1}_{F'}) \odot ((\mathbf{1}_{G'} \star t) \odot (s \star \mathbf{1}_{F}))
$$

$$
= (s' \star t') \odot (s \star t).
$$

□

**Lemma E.5.1.14.** *Let $A, B, C$ be small categories. Then the assignment:*

$$
c_{A,B,C}(\cdot,\cdot) := (\circ,\star) : \mathbf{Hom}_{\mathbf{Cat}}(A,B) \times \mathbf{Hom}_{\mathbf{Cat}}(B,C) \to \mathbf{Hom}_{\mathbf{Cat}}(A,C) \tag{E.5.1.22}
$$

## PDF page 894

**CHAPTER E. TOPOLOGICAL STACKS** · **894**

*defined as the composition of functors from (E.5.1.1) on objects, and the horizontal composition of natural transformations from (E.5.1.20) on morphisms, is a functor. Moreover, we have the following identities:*

(1) *For small categories $A, B$, functors $F, F' : A \rightrightarrows B$, and a natural transformation $t : F \Rightarrow F'$, we have:*

(a) $c_{A,A,B}(\mathrm{id}_{A},F) = c_{A,B,B}(F,\mathrm{id}_{B}) = F$.

(b) $c_{A,A,B}(\mathbf{1}_{\mathrm{id}_{A}},t) = c_{A,B,B}(t,\mathbf{1}_{\mathrm{id}_{B}}) = t$.

(2) *For small categories $A, B, C, D$, functors $F, F' : A \rightrightarrows B$, $G, G' : B \rightrightarrows C$, $H, H' : C \rightrightarrows D$, and natural transformations $t : F \Rightarrow F'$, $s : G \Rightarrow G'$, $r : H \Rightarrow H'$, we have:*

(a) $c_{A,B,D}(c_{A,B,C}(F,G),H) = c_{A,B,D}(F,c_{B,C,D}(G,H))$.

(b) $c_{A,B,C}(c_{A,B,C}(t,s),r) = c_{A,B,D}(t,c_{B,C,D}(s,r))$.

We recall that the product $\mathbf{Hom}_{\mathbf{Cat}}(A,B) \times \mathbf{Hom}_{\mathbf{Cat}}(B,C)$ is the product of two small categories (see [SP, Tag 001K]). We further refer the reader to [SP, Tag 003F].

*Proof.* This is a direct consequence of Lemma E.5.1.12, which can be applied by Lemma E.5.1.13. Explicitly, we let $(F,G)$, $(F',G')$ and $(F'',G'')$ be three objects in the product category:

$$
\mathbf{Hom}_{\mathbf{Cat}}(A,B) \times \mathbf{Hom}_{\mathbf{Cat}}(B,C)
$$

and $t : F \Rightarrow F'$, $s : G \Rightarrow G'$, $t' : F' \Rightarrow F''$, $s' : G' \Rightarrow G''$ natural transformations of functors defining morphisms $(t,s)$ and $(t',s')$ in the product category. Then

$$
(\circ,\star)(F,G) = G \circ F, \quad (\circ,\star)(F',G') = G' \circ F', \quad (\circ,\star)(F'',G'') = G'' \circ F''
$$

on objects, and

$$
(\circ,\star)(t,s) = s \star t, \quad (\circ,\star)(t',s') = s' \star t'
$$

on morphisms.

We are to check, upon denoting by $\square$ the composition of morphisms in the product category:

$$
(\circ,\star)((t',s') \square (t,s)) = ((\circ,\star)(t',s')) \star ((\circ,\star)(t,s)).
$$

Since we have $(t',s') \square (t,s) = (t' \odot t, s' \odot s)$, we deduce the identity of morphisms in $\mathbf{Hom}_{\mathbf{Cat}}(A,C)$:

$$
((\circ,\star)(t',s')) \star ((\circ,\star)(t,s)) = (s' \star t') \odot (s \star t)
$$

and we have $(s' \odot s) \star (t' \odot t) = (s' \star t') \odot (s \star t)$ from Lemma E.5.1.13, which is what we needed to show. The desired identities are a reformulation of (E.5.1.11) from Lemma E.5.1.6 and of (E.5.1.15) from Lemma E.5.1.8, for part (b) of (1), and of Lemma E.5.1.12 for part (b) of (2). Parts (a) of (1) and of (2) is a consequence of the fact that on objects, $c_{\bullet,\bullet,\bullet}$ is defined via composition of functors between small categories. □

E.5.1.3. *Effective small categories.* We now revisit the category $\mathbf{Cat}$ under a different perspective, which will be of use throughout and will give us the opportunity to make examples. We begin with a definition:

**Definition E.5.1.15.** Call $\mathbf{Cat}^{*}$ the category whose objects are 6-tuples $(X,A,s,t,c,e)$ as for groupoids in sets in Definition E.4.1.1 but without the inversion axioms (this is why we write “$A$” instead of “$R$”), and likewise for morphisms.$^{18}$ A *functor* between objects in $\mathbf{Cat}^{*}$ is a map between such 6-tuples as in (E.4.1.7) but without the inversion aspect.

Objects in $\mathbf{Cat}^{*}$ are called *effective small categories*. There is an evident analogy between $\mathbf{Cat}^{*}$ and the category $\mathbf{Cat}$ from §E.5.1.1. We define the analog of natural transformations of functors:

**Definition E.5.1.16.** Let $(X,A,s,t,c,e)$ and $(X',A',s',t',c',e')$ be in $\mathbf{Cat}^{*}$ and

$$
F := (f,g), F' := (f',g') : (X,A,s,t,c,e) \to (X',A',s',t',c',e')
$$

$^{18}$Previously had not included compatibility with $e$’s, which was surely an oversight.

## PDF page 895

**E.5. 2-CATEGORICAL PREPARATIONS** · **895**

two functors.

We define a *natural transformation* $t : F \Rightarrow F'$ to be a set-function:

$$
T : X \to A' \tag{E.5.1.23}
$$

such that for all $x \in X$ we have $T(x) : f(x) \to f(x')$ and for every $a : x \to y$ the diagram

(E.5.1.24)


```latex
\begin{tikzcd}[row sep=large, column sep=large]
f(x) \arrow[r, "g(a)"] \arrow[d, "T(x)"'] & f(y) \arrow[d, "T(y)"] \\
f'(x) \arrow[r, "g'(a)"'] & f'(y)
\end{tikzcd}
```

commutes.

As for the category $\mathbf{Cat}$, we highlight here additional structures that the category $\mathbf{Cat}^{*}$ is equipped with.

**Construction E.5.1.17.** Let $(X,A,s,t,c,e)$, $(X',A',s',t',c',e')$ and $(X'',A'',s'',t'',c'',e'')$ be three effective small categories.

(1) We write

$$
\mathrm{Hom}_{\mathbf{Cat}^{*}}((X,A,s,t,c,e),(X',A',s',t',c',e')) \tag{E.5.1.25}
$$

for the set of functors $(X,A,s,t,c,e) \to (X',A',s',t',c',e')$.

(2) For functors $F = (f_{1},f_{2})$, $F' = (f'_{1},f'_{2}) : (X,A,s,t,c,e) \rightrightarrows (X',A',s',t',c',e')$, we write $\mathrm{2\text{-}Morph}_{F,F'}$ for the sets of natural transformations $F \Rightarrow F'$. We write:

$$
\mathrm{2\text{-}Morph}((X,A,s,t,c,e),(X',A',s',t',c',e')) := \coprod_{(F,F')} \mathrm{2\text{-}Morph}_{F,F'} \tag{E.5.1.26}
$$

where the co-product is over all ordered pairs

$$
(F,F') \in \mathrm{Hom}_{\mathbf{Cat}^{*}}((X,A,s,t,c,e),(X',A',s',t',c',e')) \times \mathrm{Hom}_{\mathbf{Cat}^{*}}((X,A,s,t,c,e),(X',A',s',t',c',e'))
$$

and we define

(a) For a triple of functors $F, F', F''$ from $(X,A,s,t,c,e)$ to $(X',A',s',t',c',e')$ and natural transformations:

$$
T : F \Rightarrow F', \quad T' : F' \Rightarrow F''
$$

we define

$$
\odot : \mathrm{2\text{-}Morph}_{F,F'} \times \mathrm{2\text{-}Morph}_{F',F''} \to \mathrm{2\text{-}Morph}_{F,F''} \tag{E.5.1.27}
$$

by

$$
(T' \odot T)(x) := c'(T(x),T'(x)) \tag{E.5.1.28}
$$

for all $x \in X$ and refer to $\odot$ as the *vertical composition* of natural transformations.

(b) For functors

$$
F = (f_{1},f_{2}), F' = (f'_{1},f'_{2}) : (X,A,s,t,c,e) \rightrightarrows (X',A',s',t',c',e')
$$

and

$$
G = (g_{1},g_{2}), G' = (g'_{1},g'_{2}) : (X',A',s',t',c',e') \rightrightarrows (X'',A'',s'',t'',c'',e'')
$$

we define, for natural transformations $T : F \Rightarrow F'$ and $S : G \Rightarrow G'$:

$$
\star : \mathrm{2\text{-}Morph}_{F,F'} \times \mathrm{2\text{-}Morph}_{G,G'} \to \mathrm{2\text{-}Morph}_{G \circ F,G' \circ F'} \tag{E.5.1.29}
$$

## PDF page 896

**CHAPTER E. TOPOLOGICAL STACKS** · **896**

by

$$
(S \star T)(x) := c''(S(f_{1}(x)),g'_{2}(T(x))) \tag{E.5.1.30}
$$

for all $x \in X$ and refer to it as the *horizontal composition* of natural transformations.

(3) For a functor $F = (f_{1},f_{2}) : (X,A,s,t,c,e) \to (X',A',s',t',c',e')$, we denote by $\mathbf{1}_{F}$ the set-function

$$
\mathbf{1}_{F}(x) := (f_{2} \circ e)(x) = (e' \circ f_{1})(x).
$$

We now briefly state and prove analogs for the category $\mathbf{Cat}^{*}$ of the results established on $\odot$ and $\star$ in the foregoing, concerning the category $\mathbf{Cat}$.

**Lemma E.5.1.18.** *Let $(X,A,s,t,c,e)$, $(X',A',s',t',c',e')$, $(X'',A'',s'',t'',c'',e'')$, $(X''',A''',s''',t''',c''',e''')$ be effective small categories. Let $F = (f_{1},f_{2})$, $F' = (f'_{1},f'_{2})$, and $F'' = (f''_{1},f''_{2})$ be triples of functors*

$$
(X,A,s,t,c,e) \to (X',A',s',t',c',e')
$$

*and $G = (g_{1},g_{2})$, $G' = (g'_{1},g'_{2})$, and $G'' = (g''_{1},g''_{2})$ be triples of functors*

$$
(X',A',s',t',c',e') \to (X'',A'',s'',t'',c'',e''),
$$

*and $H = (h_{1},h_{2}) : (X'',A'',s'',t'',c'',e'') \to (X''',A''',s''',t''',c''',e''')$ another such functor.*

*Let $T : F \Rightarrow F'$, $T' : F' \Rightarrow F''$, $S : G \Rightarrow G'$, $S' : G' \Rightarrow G''$ be natural transformations. We have the identities:*

$$
\mathbf{1}_{F'} \odot T = T \odot \mathbf{1}_{F} \tag{E.5.1.31}
$$

$$
\mathbf{1}_{G} \star \mathbf{1}_{F} = \mathbf{1}_{G \circ F}, \quad (\mathbf{1}_{G} \star T') \odot (\mathbf{1}_{G} \star T) = \mathbf{1}_{G} \star (T' \odot T), \quad \mathbf{1}_{\mathrm{id}_{(X,A)}} \star T = T \tag{E.5.1.32}
$$

$$
(S' \star \mathbf{1}_{F}) \odot (S \star \mathbf{1}_{F}) = (S' \odot S) \star \mathbf{1}_{F}, \quad S \star \mathbf{1}_{\mathrm{id}_{(Y,B)}} = S \tag{E.5.1.33}
$$

$$
\mathbf{1}_{H} \star (S \star \mathbf{1}_{F}) = (\mathbf{1}_{H} \star S) \star \mathbf{1}_{F} \tag{E.5.1.34}
$$

$$
(\mathbf{1}_{G'} \star T) \odot (S \star \mathbf{1}_{F}) = (S \star \mathbf{1}_{F'}) \odot (\mathbf{1}_{G} \star T) \tag{E.5.1.35}
$$

$$
(S' \odot S) \star (T' \odot T) = (S' \star T') \odot (S \star T). \tag{E.5.1.36}
$$

*Proof.* For (E.5.1.31), we have:

$$
(\mathbf{1}_{F'} \odot T)(x) = c'(T(x),(f'_{2} \circ e)(x))
$$

$$
= c'((f_{2} \circ e)(x),T(x))
$$

$$
= (T \odot \mathbf{1}_{F})(x)
$$

by (E.5.1.24). For (E.5.1.32), we have:

$$
(\mathbf{1}_{G} \star \mathbf{1}_{F})(x) = c''(\mathbf{1}_{G}(f_{1}(x)),g_{2}(\mathbf{1}_{F}(x)))
$$

$$
= c''((g_{2} \circ e' \circ f_{1})(x),(g_{2} \circ f_{2} \circ e)(x))
$$

$$
= c''((g_{2} \circ f_{2})(e(x)),(g_{2} \circ f_{2})(e(x)))
$$

$$
= \mathbf{1}_{G \circ F}(x).
$$

## PDF page 897

**E.5. 2-CATEGORICAL PREPARATIONS** · **897**

and the second identity of (E.5.1.32) is proved in the same way as the first in (E.5.1.33) that we now check:

$$
((S' \star \mathbf{1}_{F}) \odot (S \star \mathbf{1}_{F}))(x) = c''((S \star \mathbf{1}_{F})(x),(S' \star \mathbf{1}_{F})(x))
$$

$$
= c''(c''(S(f_{1}(x)),g'_{2}(f_{2}(e(x)))),c''(S'(f_{1}(x)),g''_{2}(f_{2}(e(x)))))
$$

$$
= c''(c''(c''(S(f_{1}(x)),g'_{2}(f_{2}(e(x)))),S'(f_{1}(x))),g''_{2}(f_{2}(e(x))))
$$

$$
= c''(c''(S(f_{1}(x)),c''(g'_{2}(f_{2}(e(x))),S'(f_{1}(x)))),g''_{2}(f_{2}(e(x))))
$$

$$
= c''(c''(S(f_{1}(x)),c''(e''(g'_{1}(f_{1}(x))),S'(f_{1}(x)))),g''_{2}(f_{2}(e(x))))
$$

$$
= c''(c''(S(f_{1}(x)),c''((e'' \circ t'')(S'(f_{1}(x))),S'(f_{1}(x))),g''_{2}(f_{2}(e(x)))))
$$

$$
= c''(c''(S(f_{1}(x)),S'(f_{1}(x))),g''_{2}(f_{2}(e(x))))
$$

$$
= c''((S' \odot S)(f_{1}(x)),g''_{2}(f_{2}(e(x))))
$$

$$
= ((S' \odot S) \star \mathbf{1}_{F})(x)
$$

The third identity in (E.5.1.32) is proved in the same way as the second in (E.5.1.33) that we now check:

$$
(\mathbf{1}_{\mathrm{id}_{A}} \star T)(x) = c'(e(f_{1}(x)),\mathrm{id}(T(x))) = T(x)
$$

where the last identity follows from $(t \circ T)(x) = f_{1}(x)$ and (??). For (E.5.1.34), we have:

$$
(\mathbf{1}_{H} \star (S \star \mathbf{1}_{F}))(x) = c'''(\mathbf{1}_{H}(g_{1}(f_{1}(x))),h_{2}((S \star \mathbf{1}_{F})(x)))
$$

$$
= c'''(h_{2}(e''(g_{1}(f_{1}(x)))),h_{2}(c''(S(f_{1}(x)),g'_{2}(f_{2}(e(x))))))
$$

$$
= c'''(h_{2}(e''(g_{1}(f_{1}(x)))),c'''(h_{2}(S(f_{1}(x))),h_{2}(g'_{2}(f_{2}(e(x))))))
$$

$$
= c'''(c'''(h_{2}(e''(g_{1}(f_{1}(x)))),h_{2}(S(f_{1}(x)))),h_{2}(g'_{2}(f_{2}(e(x)))))
$$

$$
= c'''((\mathbf{1}_{H} \star S)(f_{1}(x)),h_{2}(g'_{2}(f_{2}(e(x)))))
$$

$$
= ((\mathbf{1}_{H} \star S) \star \mathbf{1}_{F})(x).
$$

For (E.5.1.35), we have:

$$
((\mathbf{1}_{G'} \star T) \odot (S \star \mathbf{1}_{F}))(x) = c''((S \star \mathbf{1}_{F})(x),(\mathbf{1}_{G'} \star T)(x))
$$

$$
= c''(c''(S(f_{1}(x)),g'_{2}(f_{2}(e(x)))),c''(g'_{2}(e'(f_{1}(x))),g'_{2}(T(x))))
$$

$$
= c''(c''(S(f_{1}(x)),e''(g'_{1}(f_{1}(x)))),g'_{2}(c'(e'(f_{1}(x)),T(x))))
$$

$$
= c''(S(f_{1}(x)),g'_{2}(T(x)))
$$

$$
= c''(g_{2}(T(x)),S(f'_{1}(x))
$$

$$
= c''(c''(g_{2}(e'(f_{1}(x))),g_{2}(T(x))),c''(S(f'_{1}(x)),g'_{2}(f'_{2}(e(x)))))
$$

$$
= c''((\mathbf{1}_{G} \star T)(x),(S \star \mathbf{1}_{F'})(x))
$$

where we used naturality of $S$ (from (E.5.1.24)) to obtain the identity $c''(S(f_{1}(x)),g'_{2}(T(x))) = c''(g_{2}(T(x)),S(f'_{1}(x))$. For (E.5.1.36), the proof is formally identical to the proof of Lemma E.5.1.13. □

We have the following analog of Lemma E.5.1.14:

**Lemma E.5.1.19.** *Let:*

$$
(X,A,s,t,c,e,i),(Y,B,p,q,d,f),(Z,C,\sigma,\tau,\gamma,\varepsilon),(W,D,\phi,\psi,\theta,\eta)
$$

*be effective small categories, and:*

$$
F = (f_{i}), F' = (f'_{i}) : (X,A) \rightrightarrows (Y,B), G = (g_{i}), G' = (g'_{i}) : (Y,B) \rightrightarrows (Z,C)
$$

$$
H = (h_{i}), H' = (h'_{i}) : (Z,C) \rightrightarrows (W,D)
$$

## PDF page 898

**898** · **CHAPTER E. TOPOLOGICAL STACKS**

*be functors for $i=1,2$, let:*

$$
T: F \Rightarrow F', S: G \Rightarrow G', R: H \Rightarrow H'
$$

*be natural transformations. Then the assignment:*

$$
c_{A,B,C}(\cdot,\cdot) := (\circ,\star): \mathbf{Hom}_{\mathbf{Cat}^*}((X,A),(Y,B)) \times \mathbf{Hom}_{\mathbf{Cat}^*}((Y,B),(Z,C)) \to \mathbf{Hom}_{\mathbf{Cat}^*}((X,A),(Z,C))
$$

*defined as the composition of functors on objects, and the horizontal composition of natural transformations from (E.5.1.30) on morphisms, is a functor. Moreover, we have the following identities:*

(1) *We have:*

(a) $c_{A,A,B}(\mathrm{id}_{(X,A)},F) = c_{A,B,B}(F,\mathrm{id}_{(Y,B)}) = F.$

(b) $c_{A,A,B}(\mathbf{1}_{\mathrm{id}_{(X,A)}},T) = c_{A,B,B}(T,\mathbf{1}_{\mathrm{id}_{(Y,B)}}) = T.$

(2) *We have:*

(a) $c_{A,B,D}(c_{A,B,C}(F,G),H) = c_{A,B,D}(F,c_{B,C,D}(G,H)).$

(b) $c_{A,B,C}(c_{A,B,C}(T,S),R) = c_{A,B,D}(T,c_{B,C,D}(S,R)).$

PROOF. Given Lemma E.5.1.18, which provides analogs to Lemma E.5.1.2, Lemma E.5.1.6, Lemma E.5.1.8, Lemma E.5.1.9, Lemma E.5.1.10, Lemma E.5.1.12 and Lemma E.5.1.13, the proof of the Lemma proceeds in a formally identical manner as for Lemma E.5.1.14.

$\square$

REMARK E.5.1.20. On the categories $\mathbf{Cat}$ and $\mathbf{Cat}^*$, we make the following remarks.

(1) Both $\mathbf{Cat}$ and $\mathbf{Cat}^*$ have a final object. It is given, for $\mathbf{Cat}$, by the small category with only one object, which we denote $\bullet$, whose only morphism is the identity, which we denote $e_{\bullet}$, and for $\mathbf{Cat}^*$ by the datum $(X,A,s,t,c,e)$ with $X=\{1\}$, $A=X$, $s=t=\mathrm{id}$, $c:A\times_{s,X,t}A=A$ the unique morphism, $e:X\to A$ the identity. In both cases, we denote the final object by $\mathbf{1}$.

(2) Throughout the next section we shall use the two examples of $\mathbf{Cat}$ and $\mathbf{Cat}^*$ as the archetypal example of a 2-category. We shall be proving that, according to the appropriate notion of equivalence of 2-categories, they are equivalent (in fact, isomorphic) as 2-categories, and they may therefore be thought of as the same, for all practical purposes. This will provide us with a rigorous dictionary to turn results on groupoids and topological groupoids into assertions about small categories, functors and natural transformations, while at the same time enabling us to construct more examples.

Most importantly, all 2-categories of interest throughout this appendix will be contained as sub 2-categories of $\mathbf{Cat}$, whether directly in its category of small categories incarnation, or as sub 2-categories of $\mathbf{Cat}^*$. In particular, the reader may think of the operations occurring denoted $\circ,\odot,\star$ occurring throughout this appendix as being exactly those constructed explicitly in this subsection.

**E.5.2. 2-categories.** We discuss here the basic definitions. We refer the reader to [Bor1, Ch.7], [GR, Ch.2], [Ha, Ch.I,§1], and [SP, Tag 003H], for the corresponding subjects within the sources. We will closely follow the former two, while for the most part adopting the notation in use in the latter two. The main difference between this subsection and the referred sources is that we allow the objects of our 2-categories to be elements of proper classes. We reserve the terminology *small 2-category* to refer to those 2-categories whose objects form a *set*. Our envisioned examples are: groupoids internal to the large category $\mathbf{CGWH}$, the 2-category $\mathbf{Groupoids}$ of all groupoids in sets introduced in Definition E.4.1.1 (see part (3) of [SP, Tag 003J]) and the 2-category of stacks in groupoids on a site. Large categories will have a limited role throughout, but we shall need the language to speak of 2-functors and 2-fibre products within some.

*E.5.2.1. Basic notions on 2-categories.*

DEFINITION E.5.2.1. A 2-*category* $\mathcal{C}$ is the datum of:

(1) A class of objects $\mathrm{Ob}(\mathcal{C})$.

(2) For each pair of objects $(A,B)\in\mathrm{Ob}(\mathcal{C})\times\mathrm{Ob}(\mathcal{C})$, a small category $\mathbf{Hom}_{\mathcal{C}}(A,B)$.

## PDF page 899

**E.5. 2-CATEGORICAL PREPARATIONS** · **899**

(a) We call 1-*morphisms* the objects of $\mathbf{Hom}_{\mathcal{C}}(A,B)$, denoted $f:A\to B$.

(b) We call 2-*morphisms* the morphisms of $\mathbf{Hom}_{\mathcal{C}}(A,B)$, denoted $\alpha:f\Rightarrow g$, for two objects $f,g:A\rightrightarrows B$.

(c) For two 2-morphisms $\alpha:f\Rightarrow g$ and $\beta:g\Rightarrow h$, we write $\beta\odot\alpha$ for their composition. We call *vertical composition* the operation $\odot$.

(3) For each triple of objects $A,B,C\in\mathrm{Ob}(\mathcal{C})$, a *composition bifunctor*:

$$
c_{A,B,C}:\mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{Hom}_{\mathcal{C}}(B,C)\to\mathbf{Hom}_{\mathcal{C}}(A,C).
$$

Given 1-morphisms $f:A\to B$ and $g:B\to C$, and 2-morphisms $\alpha:f\Rightarrow g$ and $\beta:g\Rightarrow h$, we write:

(a) $g\circ f$ for $c_{A,B,C}(f,g):A\to C$.

(b) $\beta\star\alpha$ for $c_{A,B,C}(\alpha,\beta):f\Rightarrow h$.

(4) For every object $A\in\mathrm{Ob}(\mathcal{C})$, a *unit functor*:$^{19}$

$$
u_A:\mathbf{1}\to\mathbf{Hom}_{\mathcal{C}}(A,A)
$$

where $\mathbf{1}$ denotes the final object of $\mathbf{Cat}$ (see Remark E.5.1.20).

The bifunctors $c_{A,B,C}$ and the functor $u_A$ are assumed to satisfy the following axioms:

(1) (Unit Axiom) The following diagram is commutative:

(E.5.2.1)

```latex
\begin{tikzcd}
\mathbf{1}\times\mathbf{Hom}_{\mathcal{C}}(A,B) \arrow[d, "{(u_A,\mathbf{id})}"'] & \mathbf{Hom}_{\mathcal{C}}(A,B) \arrow[r] \arrow[d, equal] \arrow[l] & \mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{1} \arrow[d, "{(\mathbf{id},u_A)}"] \\
\mathbf{Hom}_{\mathcal{C}}(A,A)\times\mathbf{Hom}_{\mathcal{C}}(A,B) \arrow[r, "c_{A,A,B}"'] & \mathbf{Hom}_{\mathcal{C}}(A,B) & \mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{Hom}_{\mathcal{C}}(B,B) \arrow[l, "c_{A,B,B}"]
\end{tikzcd}
```

where the top horizontal arrows are equivalences of categories, and where $\mathbf{id}$ denotes, within (E.5.2.1), the identity functor.

(2) (Associativity of Compositions Axiom) The following diagram is commutative:

(E.5.2.2)

```latex
\begin{tikzcd}
\mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{Hom}_{\mathcal{C}}(B,C)\times\mathbf{Hom}_{\mathcal{C}}(C,D) \arrow[r, "{(\mathbf{id},c_{B,C,D})}"] \arrow[d, "{(c_{A,B,C},\mathbf{id})}"'] & \mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{Hom}_{\mathcal{C}}(B,D) \arrow[d, "c_{A,B,D}"] \\
\mathbf{Hom}_{\mathcal{C}}(A,C)\times\mathbf{Hom}_{\mathcal{C}}(C,D) \arrow[r, "c_{A,C,D}"'] & \mathbf{Hom}_{\mathcal{C}}(A,D)
\end{tikzcd}
```

where $\mathbf{id}$ denotes, within (E.5.2.2), the identity functor. We say a 2-category is *small* if the class $\mathrm{Ob}(\mathcal{C})$ is a set.

REMARK E.5.2.2. We make the following observations:

(1) The functors $\mathbf{Hom}_{\mathcal{C}}(A,B)\to\mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{1}$ on the top row of (E.5.2.1) are defined by sending an object $f\in\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(A,B))$ to $(f,\bullet)\in\mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{1}$, and likewise sending a morphism $\alpha:f\Rightarrow g$ to $(\alpha,e_{\bullet})$.

(2) The functor $u_A$ is equivalent to the datum of a distinguished object $\bullet_A\in\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(A,A))$, together with its identity, which we denote $e_A:\bullet_A\to\bullet_A$. See also [GR, Ch. 2, §2.1, p. 71].

(3) In light of (1) above, we may rephrase the Unit Axiom in the above Definition E.5.2.1 as follows. For each triple of objects $A,B,C\in\mathrm{Ob}(\mathcal{C})$, we have, for any 1-morphisms $f,f'\in\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(A,B))$ and every 2-morphism $\alpha:f\Rightarrow f'$:

$$
c_{A,A,B}(\bullet_A,f) = c_{A,B,B}(f,\bullet_B) = f
$$

$^{19}$Do we need to axiomatize that $u_A(\cdot):A\to A$ is an isomorphism, or is this automatic?

## PDF page 900

**900** · **CHAPTER E. TOPOLOGICAL STACKS**

and:

$$
c_{A,A,B}(e_A,\alpha) = c_{A,B,B}(\alpha,e_B) = \alpha.
$$

We note that we are not assuming $\bullet_A$ and $\bullet_B$ to be the identity functors of $A$ and $B$ respectively, although this will be the case in all situations of interest throughout this work (since this is indeed the case for $\mathbf{Cat}$ and $\mathbf{Cat}^*$).

(4) In light of (1) above, we may rephrase the Associativity of Compositions Axiom in the above Definition E.5.2.1 as follows. For every quadruple of objects $A,B,C,D\in\mathrm{Ob}(\mathcal{C})$, and every $f,f'\in\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(A,B))$, $g,g'\in\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(B,C))$ and $h,h'\in\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(C,D))$, we have:

$$
c_{A,B,D}(c_{A,B,C}(f,g),h) = c_{A,B,D}(f,c_{B,C,D}(g,h))
$$

and for every 2-morphisms $\alpha:f\Rightarrow f'$, $\beta:g\Rightarrow$ and $\gamma:h\Rightarrow h'$, we have:

$$
c_{A,B,D}(c_{A,B,C}(\alpha,\beta),\gamma) = c_{A,B,D}(\alpha,c_{B,C,D}(\beta,\gamma)).
$$

(5) Definition E.5.2.1 above is [Bor1, Ch. 7,Def. 7.1.1]. It is also the Definition introduced in [GR, Ch. 2, §2.1], with one difference. We are allowing $\mathrm{Ob}(\mathcal{C})$ to be a proper class, as opposed to a set. None of the arguments in *loc.cit.* for the results that we require are affected by this additional amount of generality. We shall in any event recall the required arguments here, exhibiting explicitly that this is indeed the case. We shall follow [GR, Ch.2§2.1] to treat pseudo-functors, and we shall then specialize to the case of strict (2, 1)-categories only, with the aim of constructing two types of 2-fibre products in strict (2, 1)-categories.

(6) In light of parts (1), (2), and (3) of this Remark, small 2-categories in the sense of Definition E.5.2.1 agree with 2-categories as defined in [Ha, Ch. I, §1].

(7) For a pair of objects $A,B\in\mathrm{Ob}(\mathcal{C})$, we think of the objects of $\mathbf{Hom}_{\mathcal{C}}(A,B)$ as arrows $f:A\to B$, and are occasionally also referred to as 1-*cells* in the literature, such as in [Bor1, Ch.7] and [GR, Ch.2]. For two 1-morphisms $f,g\in\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(A,B))$, morphisms $f\Rightarrow g$ are also referred to as 2-*cells* in the literature, as done in [Bor1, Ch. 7] and [GR, Ch. 2]. Our preferred choice of terminology follows [Ha, Ch. I, §1, (1.3)], where it is referred back to Bénabou's paper [Be], and it is also the terminology from [SP, Tags 003G, 003O, 02XG] and [SP, Tags 02XP, 02XQ].

*E.5.2.2. Basic notions on 1-morphisms.* Throughout this subsection, we fix a 2-category $\mathcal{C}$. We now define when two objects of a 2-category are “equivalent”, respectively “isomorphic”, and what it means for 1-morphisms and 2-morphisms to be “invertible”. The definition below is [Bor1, Def.7.1.2], and it is directly analogous to the concept defined right after [Ha, Ch.I,(1.3.3)], [SP, Tag 003L], and [GR, Ch.2, Def.2.1.3].

DEFINITION E.5.2.3. Let $\mathcal{C}$ be a 2-category, and $A,B\in\mathrm{Ob}(\mathcal{C})$ be objects, and $f:A\to B$ a 1-morphism.

(1) We say that $f$ is an *equivalence*, or *essentially invertible*, if and only if there exist two 1-morphisms $g,h:B\rightrightarrows A$, and two 2-isomorphisms:

$$
\alpha:\bullet_A\Rightarrow g\circ f,\quad \beta:f\circ h\Rightarrow\bullet_B.
$$

(2) We say that $f$ is an *isomorphism* if and only if there exist two 1-morphisms $g,h:B\rightrightarrows A$ such that the elements $\bullet_A$ and $g\circ f$ of the set $\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(A,A))$ are the same element, and the elements $\bullet_B$ and $f\circ h$ of the set $\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(B,B))$ are the same element. In this case, we define $\alpha$ and $\beta$ to be the identities.

(3) We say that a 1-morphism $g:B\to A$ is right-adjoint to $f:A\to B$ if and only if there exists 2-morphisms $\epsilon:f\circ g\Rightarrow\bullet_B$ and $\eta:\bullet_A\Rightarrow g\circ f$ such that the following *triangular identities* hold:

$$
(\mathbf{1}_g\star\epsilon)\odot(\eta\star\mathbf{1}_g) = \mathbf{1}_g,\quad (\epsilon\star\mathbf{1}_f)\odot(\mathbf{1}_f\star\eta) = \mathbf{1}_f.
$$

## PDF page 901

**E.5. 2-CATEGORICAL PREPARATIONS** · **901**

We also say that $f$ is left-adjoint to $g$, and call $\epsilon$ the *unit* and $\eta$ the *co-unit* of the adjunction $(f,g)$.

(4) For a 1-morphism $g:A\to B$, a 2-morphism $\alpha:f\Rightarrow g$ is *invertible* if and only if it is an isomorphism in the category $\mathbf{Hom}_{\mathcal{C}}(A,B)$. We call an invertible 2-morphism a 2-*isomorphism*.

We now introduce terminology to define what it means for a diagram to commute in $\mathcal{C}$, or commute up to 2-isomorphisms.

DEFINITION E.5.2.4. Let $A,B,C,D\in\mathrm{Ob}(\mathcal{C})$ be objects, and $f:A\to B$, $g:B\to C$, $h:A\to D$, $k:D\to C$, 1-morphisms. We consider the following (possibly non-commutative) diagram:

(E.5.2.3)

```latex
\begin{tikzcd}
A \arrow[r, "f"] \arrow[d, "h"'] & B \arrow[d, "g"] \\
D \arrow[r, "k"'] & C
\end{tikzcd}
```

(1) For objects $A,B\in\mathrm{Ob}(\mathcal{C})$, 1-morphisms $f,f':A\rightrightarrows B$, and a 2-morphism $\alpha:f\Rightarrow f'$, we write:

```latex
\begin{tikzcd}
A \arrow[r, bend left, "f"{name=U}] \arrow[r, bend right, "f'"'{name=L}] & B
\arrow[from=U, to=L, Rightarrow, "\alpha"']
\end{tikzcd}
```

to denote the cumulative datum of $((A,B),(f,f'),\alpha)$.

(2) We say that (E.5.2.3) is *oriented* if and only if there exists a 2-morphism $\alpha:g\circ f\Rightarrow k\circ h$. In this case, we say that the diagram (E.5.2.3) is *oriented by $\alpha$*. We also call $\alpha$ the *orientation* of the diagram.

(3) We say that (E.5.2.3) is *commutative* if and only if $g\circ f = k\circ h$ as objects of $\mathbf{Hom}_{\mathcal{C}}(A,C)$. As a consequence, commutative diagrams are oriented (by the identity on $g\circ f = k\circ h$).

(4) We say (E.5.2.3) is 2-*commutative* if and only if it is oriented by a 2-morphism $\alpha:g\circ f\Rightarrow k\circ h$, and $\alpha$ is an isomorphism. We write

```latex
\begin{tikzcd}
A \arrow[r, "f"] \arrow[d, "h"'] & B \arrow[d, "g"] \arrow[dl, Rightarrow, "\alpha"] \\
D \arrow[r, "k"'] & C
\end{tikzcd}
```

Thus, 2-commutative diagrams are oriented diagrams whose orientation is a 2-isomorphism.

REMARK E.5.2.5. We note that [GR, Ch. 2, Rem. 2.1.4] applies to our Definition E.5.2.3 as well, despite our assumption that the objects of $\mathcal{C}$ be allowed to be a class, as opposed to a set. In particular, we have:

(1) If a 1-morphism $f:A\to B$ in $\mathcal{C}$ is an equivalence in the sense of part (1) of Definition E.5.2.3, then we can choose $g=h$ in part (1) of Definition E.5.2.3. The argument to see this is identical to [GR, Ch.2,Rem.2.1.4,(i)], because the objects $A,B$ are fixed, and $\mathbf{Hom}_{\mathcal{C}}(A,B)$ is a small category.

(2) For $f:A\to B$ and $g:B\to C$ equivalences in $\mathcal{C}$, the composition $g\circ f:A\to C$ is also an equivalence. The argument to see this is identical to [GR, Ch.2,Rem.2.1.4(ii)].

(3) Let $f,g:A\rightrightarrows B$ be 1-morphisms, and $\alpha:f\Rightarrow g$ a 2-isomorphism. Then $f$ is an equivalence if and only if $g$ is. In other words, the notion of *equivalence* introduced on 1-morphisms of $\mathcal{C}$ in part (3) of Definition E.5.2.3 propagates along 2-isomorphisms between 1-morphisms. The argument to see this is identical to [GR, Ch.2,Rem.2.1.4,(iii)].

(4) Suppose $(f,g)$ is an adjunction, with $f:A\to B$ and $g:B\to A$ two 1-morphisms. Let $g':B\to A$ be another right-adjoint for $f$. Then $g$ and $g'$ are 2-isomorphic, i.e. there exists a 2-isomorphism $\alpha:g\Rightarrow g'$. The argument to see this is identical to the argument in [GR, Ch.2,Rem.2.1.4(v)].

## PDF page 902

**902** · **CHAPTER E. TOPOLOGICAL STACKS**

(5) Suppose $(f,g)$ is an adjunction, with $f:A\to B$ and $g:B\to A$ two 1-morphisms. Let $\alpha:f\Rightarrow f'$ and $\beta:g\Rightarrow g'$ be 2-isomorphisms. Then $(f',g')$ is also an adjunction. The argument to see this is identical to that in [GR, Ch. 2, Rem. 2.1.4(iv)].

*E.5.2.3. 2-categories and ordinary categories.* We first describe a construction to associate an ordinary category to a 2-category:

CONSTRUCTION E.5.2.6. We let $\mathcal{C}$ be a 2-category. We define $\mathrm{Cat}(\mathcal{C})$ to be the locally small category whose objects are the objects of $\mathcal{C}$, $\mathrm{Ob}(\mathcal{C})$, and whose morphisms are the 1-morphisms of $\mathcal{C}$. Composition of morphisms in $\mathrm{Cat}(\mathcal{C})$ is defined to be the composition of 1-morphisms of $\mathcal{C}$ via the functor $c_{\bullet,\bullet,\bullet}$ of part (3) of Definition E.5.2.1.

We now discuss a construction to associate a 2-category to an ordinary category. This will enable us to “view” ordinary categories as a special instance of 2-categories, and will give us access to the concept of pre-sheaves on an ordinary category, valued in a 2-category.

CONSTRUCTION E.5.2.7. We let $\mathcal{C}$ be a locally small category. We define $2\text{-}\mathrm{Cat}(\mathcal{C})$ to be the 2-category assigned as follows.

(1) We define:

$$
\mathrm{Ob}(2\text{-}\mathrm{Cat}(\mathcal{C})) := \mathrm{Ob}(\mathcal{C}) \tag{E.5.2.4}
$$

which is to say that the objects of $2\text{-}\mathrm{Cat}(\mathcal{C})$ are the objects of $\mathcal{C}$.

(2) For any pair of objects $A,B\in\mathrm{Ob}(2\text{-}\mathrm{Cat}(\mathcal{C}))$, we define the category $\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,B)$ as follows:

(a) we define:

$$
\mathrm{Ob}(\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,B)) := \mathrm{Hom}_{\mathcal{C}}(A,B) \tag{E.5.2.5}
$$

which is to say that the objects of $\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,B)$ are the elements of the Hom-set $\mathrm{Hom}_{\mathcal{C}}(A,B)$ of $\mathcal{C}$.

(b) We define, for any $f,g\in\mathrm{Ob}(\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,B))$ the set $\mathrm{Hom}_{\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}}(f,g)$ to be the singleton set if $f=g$ as elements of $\mathrm{Hom}_{\mathcal{C}}(A,B)$, and the empty set otherwise. We denote by $\mathbf{1}_f$ the only element of $\mathrm{Hom}_{\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}}(f,f)$.

This is to say that the objects of $2\text{-}\mathrm{Cat}(\mathcal{C})$ are defined to be exactly the objects of $\mathcal{C}$, the 1-morphisms of $2\text{-}\mathrm{Cat}(\mathcal{C})$ are defined to be the morphisms of $\mathcal{C}$, and the 2-morphisms of $2\text{-}\mathrm{Cat}(\mathcal{C})$ are defined to be all and only the identities on the 1-morphisms.

(3) We define, for any triple of objects $A,B,C\in\mathrm{Ob}(2\text{-}\mathrm{Cat}(\mathcal{C}))$:

$$
c_{A,B,C}:\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,B)\times\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(B,C)\to\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,C) \tag{E.5.2.6}
$$

as follows:

(a) for any $f\in\mathrm{Ob}(\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,B))$ and $g\in\mathrm{Ob}(\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(B,C))$, we define:

$$
c_{A,B,C}(f,g) := g\circ f \tag{E.5.2.7}
$$

where $g\circ f$ is the composition of $f$ and $g$ as morphisms of $\mathcal{C}$.

(b) for any 1-morphisms $f,f':A\rightrightarrows B$ and $g,g':B\rightrightarrows C$, and for any $\alpha:f\Rightarrow f'$ and $\beta:g\Rightarrow g'$, we define $c_{A,B,C}(\alpha,\beta)$ to be $c_{A,B,C}(\alpha,\beta) := \mathbf{1}_{g\circ f}$ if $f=f'$ and $g=g'$.

To see that the assignment in part (b) of (3) is well-defined, we observe that for $f\neq f'$ or $g\neq g'$, $c_{A,B,C}$ is not defined since either there is no 2-morphism $f\Rightarrow f'$ or there is no 2-morphism $g\Rightarrow g'$.

(4) For every object $A\in\mathrm{Ob}(2\text{-}\mathrm{Cat}(\mathcal{C}))$, we set:

$$
u_A:\mathbf{1}\to\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,A)
$$

## PDF page 903

**E.5. 2-CATEGORICAL PREPARATIONS** · **903**

by defining, having $\mathrm{Ob}(\mathbf{1})=\{\bullet\}$ and $\mathrm{Hom}_{\mathbf{1}}(\bullet,\bullet)=\{e_{\bullet}\}$ (see part (1) of Remark E.5.1.20 and part (2) of Remark E.5.2.2), $u_A(\bullet):=\mathrm{id}_A$, the identity map on the object $A$ of $\mathcal{C}$, and $u_A(e_{\bullet}):=\mathbf{1}_{\mathrm{id}_A}:\mathrm{id}_A\to\mathrm{id}_A$, the identity on $\mathrm{id}_A$.

We now check that the above assignments indeed satisfy the axioms from Definition E.5.2.1. For the Unit Axiom (Axiom (1) from Definition E.5.2.1), we have, for every triple of objects $A,B,C\in\mathrm{Ob}(2\text{-}\mathrm{Cat}(\mathcal{C}))$ and $f\in\mathrm{Ob}(\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,B))$:

$$
c_{A,A,B}(\mathbf{1}_{\mathrm{id}_A},f) = f = c_{A,B,B}(f,\mathbf{1}_{\mathrm{id}_B})
$$

and the same axiom on 2-morphisms is indeed satisfied as the relevant Hom-sets are either empty, in which case the assertion is vacuously true, or contain only the identity endomorphism $\mathbf{1}_{\mathrm{id}_A}$. Finally, the Associativity Axiom (Axiom (2) from Definition E.5.2.1) is satisfied as composition of morphisms in $\mathcal{C}$ is associative, as $\mathcal{C}$ is a category. We deduce that $2\text{-}\mathrm{Cat}(\mathcal{C})$ is a 2-category in the sense of Definition E.5.2.1.

**E.5.3. Pseudo-functors.** The purpose of this subsection is that of providing the language that is necessary to define sub 2-categories and their properties relative to an “ambient” 2-category. All the examples of 2-categories throughout this appendix will be constructed as sub 2-categories of the 2-category $\mathbf{Cat}$ of all small categories (see §E.5.1). We will be returning to the examples of $\mathbf{Cat}$ and its variant $\mathbf{Cat}^*$ from Definition E.5.1.15 after we collect the basic concepts around functors between 2-categories.

*E.5.3.1. Basic notions on pseudo-functors.* The definition below is a special case of [Bor1, Ch.7,Def.7.5.1], and a direct analog of [GR, Ch.2,Def.2.1.14]. We will follow to some large extent the notation of [Bor1, Ch.7] and [GR, Ch.2], to facilitate the reader in consulting the referred source materials.

DEFINITION E.5.3.1. Let $\mathcal{C}$ and $\mathcal{C}'$ be two 2-categories. We call a *pseudo-functor* $\mathcal{C}\to\mathcal{C}'$ the datum of:

(1) A class function $F:\mathrm{Ob}(\mathcal{C})\to\mathrm{Ob}(\mathcal{C}')$.

(2) For all pairs of objects $A,B\in\mathrm{Ob}(\mathcal{C})$, a functor:

$$
F_{A,B}:\mathbf{Hom}_{\mathcal{C}}(A,B)\to\mathbf{Hom}_{\mathcal{C}}(F(A),F(B)).
$$

(3) For all triples of objects $A,B,C\in\mathrm{Ob}(\mathcal{C})$, a 2-isomorphism $\gamma_{A,B,C}$ in $\mathbf{Cat}$ making the following diagram 2-commutative:

(E.5.3.1)

```latex
\begin{tikzcd}
\mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{Hom}_{\mathcal{C}}(B,C) \arrow[r, "c_{A,B,C}"] \arrow[d, "{(F_{A,B},F_{B,C})}"'] & \mathbf{Hom}_{\mathcal{C}}(A,C) \arrow[d, "F_{A,C}"] \\
\mathbf{Hom}_{\mathcal{C}}(F(A),F(B))\times\mathbf{Hom}_{\mathcal{C}}(F(B),F(C)) \arrow[r, "c_{F(A),F(B),F(C)}"'] \arrow[ur, Rightarrow, "\gamma_{A,B,C}"] & \mathbf{Hom}_{\mathcal{C}}(F(A),F(C))
\end{tikzcd}
```

(4) For every object $A\in\mathrm{Ob}(\mathcal{C})$, a natural isomorphism between the two functors defined as the compositions in the diagram (E.5.3.3) below from the upper leftmost vertex to the lower rightmost vertex, between the categories $\mathbf{1}\rightrightarrows\mathbf{Hom}_{\mathcal{C}}(F(A),F(A))$:

(E.5.3.2)

```latex
\begin{tikzcd}
\mathbf{1} \arrow[r, "u_A"] \arrow[d, equal] & \mathbf{Hom}_{\mathcal{C}}(A,A) \arrow[d, "F_{A,A}"] \\
\mathbf{1} \arrow[r, "u_{F(A)}"'] \arrow[ur, Rightarrow, "\delta_A"] & \mathbf{Hom}_{\mathcal{C}}(F(A),F(A))
\end{tikzcd}
```

The datum $(F,F_{\bullet,\bullet},\gamma_{\bullet,\bullet,\bullet},\delta_{\bullet})$ is assumed to satisfy the following properties:

## PDF page 904

**904** · **CHAPTER E. TOPOLOGICAL STACKS**

(1) (Unit Axiom) For every 1-morphism $f:A\to B$, the following diagrams commute:

(E.5.3.3)

```latex
\begin{tikzcd}
F_{A,B}(f)\circ\mathbf{1}_{F(A)} \arrow[r, Rightarrow, "\mathbf{1}_{F_{A,B}(f)}\star(\delta_A)_*"] \arrow[d, Rightarrow, "\mathbf{1}_{F_{A,B}(f)}"'] & F_{A,B}(f)\circ F_{A,A}(\mathbf{1}_A) \arrow[d, Rightarrow, "{\gamma_{A,A,B}(\mathbf{1}_A,f)}"] \\
F_{A,B}(f) \arrow[r, Rightarrow, "\mathbf{1}_{F_{A,B}(f)}"'] & F_{A,B}(f\circ\mathbf{1}_A)
\end{tikzcd}
```

where $(\delta_A)_*$ denotes the 2-morphism $\mathbf{1}_A\Rightarrow F_{A,A}(\mathbf{1}_A)$ induced by $\delta_A$, and

(E.5.3.4)

```latex
\begin{tikzcd}
\mathbf{1}_{F(B)}\circ F_{A,B}(f) \arrow[r, Rightarrow, "(\delta_B)_*\star F_{A,A}(f)"] \arrow[d, Rightarrow, "\mathbf{1}_{F_{A,B}(f)}"'] & F_{B,B}(\mathbf{1}_B)\circ F_{A,B}(f) \arrow[d, Rightarrow, "{\gamma_{A,B,B}(f,\mathbf{1}_B)}"] \\
F_{A,B}(f) \arrow[r, Rightarrow, "\mathbf{1}_{F_{A,B}(f)}"'] & F_{A,B}(\mathbf{1}_B\circ f)
\end{tikzcd}
```

where $(\delta_B)_*$ denotes the 2-morphism $\mathbf{1}_B\Rightarrow F_{B,B}(\mathbf{1}_B)$ induced by $\delta_B$.

(2) (Associativity of Compositions) For all triples of 1-morphisms $f:A\to B$, $g:B\to C$, $h:C\to D$ in $\mathcal{C}$, the following diagram commutes:

(E.5.3.5)

```latex
\begin{tikzcd}
F_{C,D}(h)\circ F_{B,C}(g)\circ F_{A,B}(f) \arrow[r, Rightarrow, "{\mathbf{1}_{F_{C,D}(h)}\star\gamma_{A,B,C}(f,g)}"] \arrow[d, Rightarrow, "{\gamma_{B,C,D}(g,h)\star\mathbf{1}_{F_{A,B}(f)}}"'] & F_{C,D}(h)\circ F_{A,C}(g\circ f) \arrow[d, Rightarrow, "{\gamma_{A,C,D}(g\circ f,h)}"] \\
F_{B,D}(h\circ g)\circ F_{A,B}(f) \arrow[r, Rightarrow, "{\gamma_{A,B,D}(f,h\circ g)}"'] & F_{A,D}(h\circ g\circ f)
\end{tikzcd}
```

We denote by $F:\mathcal{C}\to\mathcal{C}'$ the datum $(F,F_{\bullet,\bullet},\gamma_{\bullet,\bullet,\bullet},\delta_{\bullet})$, and call $(\gamma_{\bullet,\bullet,\bullet},\delta_{\bullet})$ the *coherence constraint* of $F$.

We illustrate the meaning of the two axioms from Definition E.5.3.1 above. Let $f:A\to B$ and $g:B\to C$ be two 1-morphisms. Then we may evaluate $F_{A,B}$ and $F_{B,C}$ on each, and then compose. We obtain:

$$
c_{F(A),F(B),F(C)}(F_{A,B}(f),F_{B,C}(g)) = F_{B,C}(g)\circ F_{A,B}(f)
$$

according to the notation introduced in Terminology E.5.2.4. We may also first compose to obtain $c_{A,B,C}(f,g)$, and then evaluate $F_{A,C}$ on the result, to get $F_{A,C}(g\circ f)$. $\gamma_{A,B,C}(f,g)$ is a 2-isomorphism between the two 1-morphisms $F_{B,C}(g)\circ F_{A,B}(f)$ and $F_{A,C}(g\circ f)$. Specifically, we have the 2-isomorphism:

$$
\gamma_{A,B,C}(f,g):F_{B,C}(g)\circ F_{A,B}(f)\Rightarrow F_{A,C}(g\circ f)
$$

naturally in $f,g$.

EXAMPLE E.5.3.2. In the case of Construction E.5.2.6, to a pseudo-functor between 2-categories $F:\mathcal{C}\to\mathcal{C}'$, we associate the functor $\mathrm{Cat}(F):\mathrm{Cat}(\mathcal{C})\to\mathrm{Cat}(\mathcal{C}')$ given by the class function $\mathrm{Ob}(\mathcal{C})\to\mathrm{Ob}(\mathcal{C}')$ induced by $F$ on objects, and by the effect of $F$ on 1-morphisms prescribed by part (2) of Definition E.5.3.1, on morphisms of $\mathrm{Cat}(\mathcal{C})$ and $\mathrm{Cat}(\mathcal{C}')$, respectively.

EXAMPLE E.5.3.3. In the special case of Construction E.5.2.7, we have an ordinary (locally small) category $\mathcal{C}$, and its associated 2-category $2\text{-}\mathrm{Cat}(\mathcal{C})$. Let $F:\mathcal{C}\to\mathcal{D}$ be a functor between ordinary (locally small) categories. We may associate to it the datum $(F,F_{\bullet,\bullet},\gamma_{\bullet,\bullet,\bullet},\delta_{\bullet})$ of a pseudo-functor $2\text{-}\mathrm{Cat}(\mathcal{C})\to 2\text{-}\mathrm{Cat}(\mathcal{D})$ as per Definition E.5.3.1, by defining the class function $F$ on objects to be the same class function from the objects of $\mathcal{C}$ to the objects of $\mathcal{D}$, and for any pair of objects $A,B\in\mathrm{Ob}(2\text{-}\mathrm{Cat}(\mathcal{C}))$:

$$
F_{A,B}:\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{C})}(A,B)\to\mathbf{Hom}_{2\text{-}\mathrm{Cat}(\mathcal{D})}(F(A),F(B))
$$

## PDF page 905

**E.5. 2-CATEGORICAL PREPARATIONS** · **905**

is defined on objects to be the effect of $F$ on morphisms of $\mathcal{C}$, and on morphisms to be the unique assignment sending the identities to the identities. In this case, $\gamma_{A,B,C}$ and $\delta_A$ are the identity for all $A,B,C$ objects of $2\text{-}\mathrm{Cat}(\mathcal{C})$.

The Unit Axiom from Definition E.5.3.1 encodes the correct behavior of the datum $(F,F_{\bullet,\bullet},\gamma_{\bullet,\bullet,\bullet},\delta_{\bullet})$ with respect to passage from $\mathbf{1}_{F(A)}$ to $F_{A,A}(\mathbf{1}_A)$. Namely, we are *not* assuming that pseudo-functors preserve the identities, i.e. $\mathbf{1}_{F(A)}$ and $F_{A,A}(\mathbf{1}_A)$ may not be equal as elements of the set of objects of the category $\mathbf{Hom}_{\mathcal{C}}(F(A),F(A))$, but they are isomorphic, and the axiom defines a notion of naturality for this isomorphism, codifying the compatibility of a pseudo-functor with it.

We first note that the composition of the leftmost vertical arrow followed by the bottom horizontal arrow in (E.5.3.3) is always a 2-isomorphism. This is due to the fact that in light of the Unit Axiom in the very definition of a 2-category, i.e. Axiom (1) from Definition E.5.2.1.$^{20}$

Specifically, for any 1-morphism $f:A\to B$, the composition $F_{A,B}(f)\circ\mathbf{1}_{F(A)}$ is $F_{A,B}(f)$, which in turn can be written as $F_{A,B}(f\circ\mathbf{1}_A)$. “Writing $F_{A,B}(f)$ as $F_{A,B}(f\circ\mathbf{1}_A)$”, and likewise “writing $\mathbf{1}_B\circ F_{A,B}(f)$ as $F_{A,B}(f)$”, involves passage from one to the other via the composition bifunctor, which by Axiom (2) from Definition E.5.2.1 satisfies $c_{F(A),F(A),F(B)}(\mathbf{1}_{F(A)},F_{A,B}(f)) = F_{A,B}(f)$, and hence $F_{A,B}(c_{A,A,B}(\mathbf{1}_A,f)) = F_{A,B}(f)$. This is the reason why we write $\mathbf{1}_{F_{A,B}(f)}$ for the canonical 2-(iso)morphisms placed as the leftmost vertical arrow and the bottom horizontal arrow in (E.5.3.3) and (E.5.3.4).

Axiom (1) in Definition E.5.3.1 compares the canonical 2-isomorphism $F_{A,B}\circ\mathbf{1}_{F(A)}\Rightarrow F_{A,B}(f\circ\mathbf{1}_A)$ obtained by composition of the two $\mathbf{1}_{F_{A,B}(f)}$ as discussed above, to the 2-morphism obtained instead by using $(\delta_A)_*:\mathbf{1}_{F(A)}\Rightarrow F_{A,A}(\mathbf{1}_A)$ to replace $\mathbf{1}_{F(A)}$ in $F_{A,B}(f)\circ\mathbf{1}_{F(A)}$ with $F_{A,A}(\mathbf{1}_A)$, for then passing to $F_{A,B}(f\circ\mathbf{1}_A)$ using $\gamma_{A,A,B}(\mathbf{1}_A,f)$. The first operation is a 2-isomorphism $F_{A,B}(f)\circ\mathbf{1}_{F(A)}\Rightarrow F_{A,B}(f)\circ F_{A,A}(\mathbf{1}_A)$, given by $\mathbf{1}_{F_{A,B}(f)}\star(\delta_A)_*$. The content of the axiom is that the two compositions, namely $F_{A,B}(f)\circ\mathbf{1}_{F(A)}$ and $F_{A,B}(f\circ\mathbf{1}_A)$, are 2-isomorphic.

As for the Axiom on Associativity of Compositions, it similarly encodes that the two possible results of grouping compositions together in a triple composition are 2-isomorphic.

NOTATION E.5.3.1. We introduce the following notation:

(1) We denote, for any $(f,g)\in\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(A,B))\times\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(B,C))$, the “$(f,g)$-section” $\gamma_{A,B,C}(f,g)$ of the natural transformation $\gamma_{A,B,C}$ evaluated at the object $(f,g)$ of $\mathbf{Hom}_{\mathcal{C}}(A,B)\times\mathbf{Hom}_{\mathcal{C}}(B,C)$, by $\gamma_{f,g}$, omitting $A,B,C$ from the notation when no confusion is expected to arise.

(2) We denote, for any 1-morphism $f:A\to B$, by $F(f)$ the 1-morphism $F_{A,B}(f):F(A)\to F(B)$.

REMARK E.5.3.4. We make the following observations on Definition E.5.3.1. In the special case when $\delta_A$ is the identity for every object $A\in\mathrm{Ob}(\mathcal{C})$, the axioms satisfied by the datum of a pseudo-functor $(F,F_{\bullet,\bullet},\gamma_{\bullet,\bullet,\bullet},\delta_{\bullet})$ as per Definition E.5.3.1 can be rephrased as follows, and when $\mathcal{C}$ is a small 2-category, they recover the axioms from [Ha, Ch. I, §1, (1.5)]:

(1) (Unit Axiom) For all objects $A\in\mathrm{Ob}(\mathcal{C})$, we have $F_{A,A}(\mathbf{1}_A) = \mathbf{1}_{F(A)}$. For all pairs of objects $A,B\in\mathrm{Ob}(\mathcal{C})$, we have $\gamma_{A,B,B}(\cdot,\mathbf{1}_B) = \mathbf{1}_{F_{A,B}}$, and $\gamma_{A,A,B}(\mathbf{1}_A,\cdot) = \mathbf{1}_{F_{A,B}}$. This is [Ha, Ch. I, §1, (1.5), Axioms (i)$'$,(ii)$'$].

(2) (Associativity of Compositions) For all quadruples of objects $A,B,C,D\in\mathrm{Ob}(\mathcal{C})$, one has the identity of 2-isomorphisms in $\mathbf{Cat}$:

$$
\gamma_{A,B,D}(\cdot,\cdot)\odot(\gamma_{B,C,D}(\cdot,\cdot)\star\mathbf{1}_{F_{A,B}}) = \gamma_{A,C,D}(\cdot,\cdot)\odot(\mathbf{1}_{F_{C,D}}\star\gamma_{A,B,C}(\cdot,\cdot)).
$$

This is [Ha, Ch. I, §1, (1.5), Axiom (iii)$'$], upon observing that our conventions are consistent with the ones in *loc.cit.*, as they are with the ones in [GR, Ch. 2], and that the identity in [Ha, Ch. I, §1, (1.5), Axiom (iii)$'$] is equivalent to the one above upon evaluating the functor $\mu'$ of *loc.cit.* on it.

$^{20}$This is not a sentence; what is it meant to be saying? Rewrite as an actual sentence.

## PDF page 906

**906** · **CHAPTER E. TOPOLOGICAL STACKS**

REMARK E.5.3.5. We let $\mathcal{I}$ be a locally small category, and now describe the pseudo-functors from $2\text{-}\mathrm{Cat}(\mathcal{I})$, where $2\text{-}\mathrm{Cat}(\mathcal{I})$ is the 2-category associated to $\mathcal{I}$ constructed in Construction E.5.2.7, to a fixed 2-category $\mathcal{C}$. In the special case when $\mathcal{C}$ is small, the description we shall obtain will match the definition of *weak 2-functor* from part (2) of [SP, Tag 003N], up to a discrepancy concerning the coherence constraint, and specifically the transformation $\gamma_{\bullet,\bullet,\bullet}$. In our conventions, which follow closely those in [GR, Ch. 2], $\gamma_{\bullet,\bullet,\bullet}$ is the inverse of the analogous transformation $\alpha$ from [SP, Tag 003N].

A pseudo-functor $2\text{-}\mathrm{Cat}(\mathcal{I})\to\mathcal{C}$ in the sense of Definition E.5.3.1 is the datum of:

(1) a class function $F:\mathrm{Ob}(\mathcal{I})\to\mathrm{Ob}(\mathcal{C})$.

(2) For each morphism $f:x\to y$ in $\mathcal{I}$, a 1-morphism $F(f):F(x)\to F(y)$ in $\mathcal{C}$.

(3) For every object $x\in\mathcal{I}$, a 2-morphism $\delta_x:F(\mathbf{1}_x)\Rightarrow\mathbf{1}_{F(x)}$ in $\mathcal{C}$.

(4) For every pair of morphisms $f:x\to y$, $g:y\to z$, a 2-morphism $\gamma_{f,g}:F(g)\circ F(f)\Rightarrow F(g\circ f)$ in $\mathcal{C}$.

The above data is then required to satisfy the Unit Axiom and the Associativity of Compositions Axiom as per Definition E.5.3.1, which in this special case take the following form:

(1) $\gamma_{f,g}$ and $\delta_x$ are 2-isomorphisms for all $x\in\mathrm{Ob}(\mathcal{I})$ and all morphisms $f,g$ in $\mathcal{I}$.

(2) (Unit Axiom) For any morphism $f:x\to y$ in $\mathcal{I}$, we have:

$$
\mathbf{1}_{F(f)}\star\delta_x = \gamma_{f,\mathbf{1}_x}
$$

and:

$$
\delta_y\star\mathbf{1}_{F(f)} = \gamma_{\mathbf{1}_y,f}.
$$

(3) (Associativity of Compositions Axiom) For any triple of morphisms $f:x\to y$, $g:y\to z$, $h:z\to w$ in $\mathcal{I}$, we have:

$$
\gamma_{f,h\circ g}\odot(\gamma_{g,h}\star\mathbf{1}_{F(f)}) = \gamma_{g\circ f,h}\odot(\mathbf{1}_{F(h)}\star\gamma_{f,g}).
$$

If we rename $\gamma_{\bullet,\bullet}^{-1}$ as $\alpha_{\bullet,\bullet}$ and $\odot$ as $\circ$ (and we therefore reverse the order of all compositions), we recover the definition of *weak functor* from part (2) of [SP, Tag 003N].

*E.5.3.2. Degrees of faithfulness.* We introduce the following:

DEFINITION E.5.3.6. Let $\mathcal{C}$ and $\mathcal{C}'$ be 2-categories, and $F:\mathcal{C}\to\mathcal{C}'$ a pseudo-functor. We say:

(1) $F$ is *weakly faithful* if and only if for any pair of objects $A,B\in\mathrm{Ob}(\mathcal{C})$, the functor:

$$
F_{A,B}:\mathbf{Hom}_{\mathcal{C}}(A,B)\to\mathbf{Hom}_{\mathcal{C}}(F(A),F(B))
$$

is faithful.

(2) $F$ is *faithful* if and only if for any pair of objects $A,B\in\mathrm{Ob}(\mathcal{C})$, the functor:

$$
F_{A,B}:\mathbf{Hom}_{\mathcal{C}}(A,B)\to\mathbf{Hom}_{\mathcal{C}}(F(A),F(B))
$$

is fully faithful.

(3) $F$ is *strongly faithful* if and only if for any pair of objects $A,B\in\mathrm{Ob}(\mathcal{C})$, the functor

$$
F_{A,B}:\mathbf{Hom}_{\mathcal{C}}(A,B)\to\mathbf{Hom}_{\mathcal{C}}(F(A),F(B))
$$

is fully faithful and the set-function induced on objects is injective.

(4) $F$ is *fully faithful* if and only if for any pair of objects $A,B\in\mathrm{Ob}(\mathcal{C})$, the functor:

$$
F_{A,B}:\mathbf{Hom}_{\mathcal{C}}(A,B)\to\mathbf{Hom}_{\mathcal{C}'}(F(A),F(B))
$$

is an equivalence of categories.

(5) $F$ is *strongly fully faithful* if and only if for any pair of objects $A,B\in\mathrm{Ob}(\mathcal{C})$, the functor:

$$
F_{A,B}:\mathbf{Hom}_{\mathcal{C}}(A,B)\to\mathbf{Hom}_{\mathcal{C}'}(F(A),F(B))
$$

is an isomorphism of categories.

## PDF page 907

**E.5. 2-CATEGORICAL PREPARATIONS** · **907**

(6) $F$ is a 2-*equivalence* if and only if it is fully faithful and for every object $B\in\mathrm{Ob}(\mathcal{C}')$ there exists an object $A\in\mathrm{Ob}(\mathcal{C})$ and an equivalence $F(A)\to B$ in $\mathcal{C}$.

(7) $F$ is a *strong 2-equivalence* if and only if it is fully faithful and for every object $B\in\mathrm{Ob}(\mathcal{C}')$ there exists an object $A\in\mathrm{Ob}(\mathcal{C})$ and an isomorphism $F(A)\to B$ in $\mathcal{C}$.

(8) $F$ is an *isomorphism* if and only if it is strongly fully faithful and a strong 2-equivalence.

(9) $F$ is *strict* if and only if the structure natural transformations $\gamma_{\bullet,\bullet,\bullet}$ and $\delta_{\bullet}$ in the coherence constraint $(\gamma_{\bullet,\bullet,\bullet}^F,\delta_{\bullet}^F)$ for $F$ are the identity.

We can now define the concept of a sub 2-category of a 2-category:

DEFINITION E.5.3.7. Let $\mathcal{C}$ be a 2-category. We say:

(1) $\mathcal{C}'$ is a *sub 2-category* of $\mathcal{C}$ if and only if:

(a) $\mathcal{C}'$ is a 2-category.

(b) The class of the objects of $\mathcal{C}'$ is a sub-class of the class of the objects of $\mathcal{C}$.

(c) The inclusion class function $F:\mathrm{Ob}(\mathcal{C}')\to\mathrm{Ob}(\mathcal{C})$ is part of the datum of a pseudo-functor $(F,F_{\bullet,\bullet},\gamma_{\bullet,\bullet,\bullet},\delta_{\bullet}):\mathcal{C}'\to\mathcal{C}$. We call $F$ the *inclusion functor*.

(d) The inclusion functor $F$ is weakly faithful.

(2) $\mathcal{C}'$ is a *strict sub 2-category* of $\mathcal{C}$ if and only if is is a sub 2-category and the inclusion functor is strict.

(3) $\mathcal{C}'$ is a *full sub 2-category* of $\mathcal{C}$ if and only if $\mathcal{C}'$ is a sub 2-category and the inclusion functor is fully faithful.

(4) $\mathcal{C}'$ is a *strong sub 2-category* of $\mathcal{C}$ if and only if $\mathcal{C}'$ is a sub 2-category and the inclusion functor is strongly faithful.

**E.5.4. Comparing $\mathbf{Cat}^*$ and $\mathbf{Cat}$.** We consider the following assignment.

CONSTRUCTION E.5.4.1. For any effective small category $(X,A,s,t,c,e)$ (see Definition E.5.1.15), we associate the category $\mathcal{C}_{(X,A)}$ such that:

(1) $\mathrm{Ob}(\mathcal{C}_{(X,A)}) := X$.

(2) For any two objects $x,y\in\mathrm{Ob}(\mathcal{C}_{(X,A)})$, we define $\mathrm{Hom}_{\mathcal{C}_{(X,A)}}(x,y) := s^{-1}(x)\cap t^{-1}(y)$.

(3) For any two morphisms $f\in\mathrm{Hom}_{\mathcal{C}_{(X,A)}}(x,y)$ and $g\in\mathrm{Hom}_{\mathcal{C}_{(X,A)}}(y,z)$, we define $g\circ f := c(f,g)$.

For any functor $F=(f_1,f_2):(X,A,s,t,c,e)\to(X',A',s',t',c',e')$:

(1) for any object $x\in\mathcal{C}_{(X,A)}$, we define $\phi_F(x) := f_1(x)$.

(2) For any morphism $f\in\mathrm{Hom}_{\mathcal{C}_{(X,A)}}(x,y)$, we define $\phi_F(f) := f_2(f)$.

We call $\phi_F:\mathcal{C}_{(X,A)}\to\mathcal{C}_{(X',A')}$ the assignment defined above on objects and morphisms.

We have the following consistency checks:

LEMMA E.5.4.2. *For any effective small category $(X,A,s,t,c,e)$, the datum $\mathcal{C}_{(X,A)}$ is a small category. The assignment:*

$$
(X,A,s,t,c,e)\rightsquigarrow\mathcal{C}_{(X,A)} \tag{E.5.4.1}
$$

*is functorial, the functoriality being defined by $\phi$ constructed in Construction E.5.4.1.*

PROOF. The very definition of $\phi$ ensures compatibility with composition of morphisms on source and target, since, for any functor $F=(f_1,f_2):(X,A,s,t,c,e)\to(X',A',s',t',c',e')$, $\phi_F$ is defined to be $f_2$ on morphisms, and $(f_1,f_2)$ is a morphism of effective small categories. In particular, $f_2$ is compatible with the composition laws $c,c'$, which translates into $\phi_F$ being compatible with composition of morphisms, as desired.

$\square$

We have the following:

## PDF page 908

**908** · **CHAPTER E. TOPOLOGICAL STACKS**

LEMMA E.5.4.3. *The assignment:*

$$
\phi:\mathbf{Cat}^*\to\mathbf{Cat} \tag{E.5.4.2}
$$

*defined in Construction E.5.4.1 is an isomorphism of locally small categories.*

PROOF. Indeed, for any two effective small categories $(X,A,s,t,c,e)$ and $(X',A',s',t',c',e')$, the functor $\phi$ induces an injective set-function:

$$
\phi:\mathrm{Hom}_{\mathbf{Cat}^*}((X,A,s,t,c,e),(X',A',s',t',c',e'))\to\mathrm{Hom}_{\mathbf{Cat}}(\mathcal{C}_{(X,A)},\mathcal{C}_{(X',A')}).
$$

To see this, we observe that by design of $\phi$, for any functor $F=(f_1,f_2):(X,A,s,t,c,e)\to(X',A',s',t',c',e')$, $f_2$ is uniquely determined by $\phi_F$. As for $f_1$, one recovers it by computing the effect of $\phi_F$ on objects of $\mathcal{C}_{(X,A)}$, which are, by definition, the set $X$. We now prove surjectivity of the map that $\phi$ induces on Hom-sets. Let $F:\mathcal{C}_{(X,A)}\to\mathcal{C}_{(X',A')}$ be a functor. We may define $f_1:X\to X$ to be $f_1(x):=F(x)$, as $X=\mathrm{Ob}(\mathcal{C}_{(X,A)})$ by definition of $\mathcal{C}_{(X,A)}$. We can reconstruct $A$ as:

$$
A = \coprod_{(x,y)\in\mathrm{Ob}(\mathcal{C}_{(X,A)})\times\mathrm{Ob}(\mathcal{C}_{(X,A)})}\mathrm{Hom}_{\mathcal{C}_{(X,A)}}(x,y)
$$

and so $f_2(a):=F(a)$ defines a pair of set-functions $(f_1,f_2):(X,A)\to(X',A')$.

Compatibility with $s,t,c,e$ follows from the definition of $\mathcal{C}_{(X,A)}$ and the composition of morphisms in $\mathcal{C}_{(X,A)}$. This proves that $\phi$ is fully faithful. For $\mathcal{C}$ a small category, we call $X:=\mathrm{Ob}(\mathcal{C})$, $A:=\coprod_{(x,y)\in X\times X}\mathrm{Hom}_{\mathcal{C}}(x,y)$, and define $s,t:A\rightrightarrows X$ as follows. For any $a\in A$, there exists a unique pair $(x,y)\in X\times X$ such that $a\in\mathrm{Hom}_{\mathcal{C}}(x,y)$. We define $s(a):=x$ and $t(a):=t$. For $a,a'\in A$ such that $s(a)=t(a')$, we have $a\in\mathrm{Hom}_{\mathcal{C}}(x,y)$ and $a'\in\mathrm{Hom}_{\mathcal{C}}(z,x)$, and so the composition $a\circ a'$ makes sense. We denote it by $c(a',a)$, and this provides a set-function $A\times_{s,X,t}A\to A$. Finally, we define $e:X\to A$ by $e(x):=\mathrm{id}_x$. We therefore obtain a 6-tuple $(X,A,s,t,c,e)$ from $\mathcal{C}$, and the axioms (??), (??), (??) and (??) from Definition E.5.1.15 are seen to be satisfied by $(s,t,c,e)$ upon inspection of the defining axioms of a category. This shows that $\mathcal{C}=\mathcal{C}_{(X,A)}$, i.e. $\mathcal{C}$ is isomorphic as a category to a category of the form $\mathcal{C}_{(X,A)}$. This shows that $\phi:\mathbf{Cat}^*\to\mathbf{Cat}$ from (E.5.4.2) is an isomorphism of categories.

$\square$

We can promote $\phi$ to a pseudo-functor as follows:

CONSTRUCTION E.5.4.4. For any natural transformation $T:F\Rightarrow F'$ between functors $F=(f_1,f_2)$, $F'=(f_1',f_2'):(X,A,s,t,c,e)\rightrightarrows(X',A',s',t',c',e')$, we define $\phi(T)$ to be the natural transformation of functors $\phi_F\Rightarrow\phi_{F'}$ characterized by the following property: for any object $x$ in $\mathcal{C}_{(X,A)}$, the datum of $\phi(T)_x$ is the morphism $f_1(x)\to f_1'(x)$ in $\mathcal{C}_{(X',A')}$ given by $T(x)\in(s')^{-1}(f_1(x))\cap(t')^{-1}(f_1'(x)) = \mathrm{Hom}_{\mathcal{C}_{(X',A')}}(f_1(x),f_1'(x))$. Naturality of $\phi(T)_x$ with respect to $x$ is a consequence of (E.5.1.24) from Definition E.5.1.16. See also Remark ??.

LEMMA E.5.4.5. *The locally small categories $\mathbf{Cat}$ and $\mathbf{Cat}^*$ are, in a canonical way, 2-categories, whose composition bifunctors are the bifunctors $c_{\bullet,\bullet,\bullet}$ constructed in Lemma E.5.1.14 and Lemma E.5.1.19. The functor $\phi:\mathbf{Cat}^*\to\mathbf{Cat}$ is a strict isomorphism of 2-categories.*

PROOF. Indeed, since the composition of morphisms in $\mathcal{C}_{(X,A)}$ for $(X,A,s,t,c,e)$ an effective small category, is defined by means of the composition law $c$, and $\phi$ is defined in terms of the component set-functions of functors between effective small categories (see Definition E.5.1.15 and Construction E.5.4.4), $\phi$ is compatible with composition of 1-morphisms and 2-morphisms on the nose, forcing $\gamma_{\bullet,\bullet,\bullet}$ and $\delta_{\bullet}$ to be the identity, so $\phi$ is a strict pseudo-functor. By Lemma E.5.4.3 it induces an essentially surjective functor on Hom-categories. Such functor is also fully faithful because, given a natural transformation of functors $T:F\Rightarrow F'$ between effective small categories $F=(f_1,f_2)$, $F'=(f_1',f_2'):(X,A)\rightrightarrows(X',A')$, $T$ is a set-function $T:X\to A'$,

## PDF page 909

**E.5. 2-CATEGORICAL PREPARATIONS** · **909**

and knowledge of the associated natural transformation is knowledge of a coherent family of set-functions $f_1(x)\to f_1'(x)$ for every $x\in X$.

To reconstruct $T$, one defines $T(x)$ to be the element $a'\in A'$ corresponding to the morphism $f_1(x)\to f_1'(x)$ under $\phi$, and seeing that indeed this construction recovers $T$ is a simple consequence of the definitions. More generally, any natural transformation $T:F\Rightarrow F'$ between functors of small categories $\mathcal{C}\to\mathcal{C}'$ produces, by means of the above construction, a set-function $T:\mathrm{Ob}(\mathcal{C})\to\mathrm{Arrows}(\mathcal{C}')$ satisfying the defining axioms (see Definition E.5.1.16), and hence the functor induced by $\phi$ on Hom-categories is an isomorphism of categories, so $\phi$ is strongly fully faithful. Upon combining strong full faithfulness with Lemma E.5.4.3 and with the strictness of $\phi$ proved in the foregoing, we deduce $\phi$ is a strict isomorphism of 2-categories, as desired.

$\square$

REMARK E.5.4.6. In light of Lemma E.5.4.5, we can now give meaning to the sentence “we view the datum of $(X,A,s,t,c,e)$ as a small category”, which is commonly done when discussing, for instance, groupoids and stacks in groupoids on a site. Conversely, we may “view a small category as the datum of $(X,A,s,t,c,e)$”, for appropriate structure morphisms $(s,t,c,e)$, and this sentence now has an un-ambiguous meaning provided by Lemma E.5.4.5, insofar it refers to the functor $\phi:\mathbf{Cat}^*\to\mathbf{Cat}$ being a strict isomorphism of 2-categories.

We have the following simple but useful Lemma:

LEMMA E.5.4.7. *Let $\mathcal{A}$ and $\mathcal{B}$ be small categories. If all the morphisms of $\mathcal{A}'$ are isomorphisms, then for any pair of functors $F,F':\mathcal{A}\rightrightarrows\mathcal{B}$, any natural transformation $t:F\Rightarrow F'$ is an isomorphism of functors.*

PROOF. For every object $a$ of $\mathcal{A}$, $t_a:F(a)\to F'(a)$ is a morphism in $\mathcal{A}'$. By assumption, every morphism in $\mathcal{A}'$ is an isomorphism, and hence for every object $a$ of $\mathcal{A}$, there exists a necessarily unique inverse $t_a^{-1}$ to $t_a$ in $\mathcal{A}'$. This gives a natural transformation $t^{-1}:F'\Rightarrow F$. That $t^{-1}$ is the inverse of $t$ follows from the definition of $t_a^{-1}$ for every object $a$ of $\mathcal{A}$.

$\square$

We now consider the inclusion of the category $\mathbf{Groupoids}$ into the category $\mathbf{Cat}^*$, assigned by sending the datum of a groupoid in sets $(X,R,s,t,c,e,i)$ (see Definition E.4.1.1) to the effective small category $(X,R,s,t,c,e)$ (“forget $i$”). We call:

$$
u_{\mathrm{gpd}}:\mathbf{Groupoids}\to\mathbf{Cat}^* \tag{E.5.4.3}
$$

the fully faithful inclusion functor of ordinary categories.

LEMMA E.5.4.8. *The category $\mathbf{Groupoids}$ is a 2-category upon endowing it with the composition bifunctor constructed on effective small categories in Lemma E.5.1.14. The functor $u_{\mathrm{gpd}}:\mathbf{Groupoids}\to\mathbf{Cat}^*$ from (E.5.4.3) extends to a strongly fully faithful strict pseudo-functor.*

PROOF. All we need to check is that for any two groupoids $(X,R,s,t,c,e,i)$ and $(X',R',s',t',c',e',i')$ and any functor $F=(f_1,f_2):(X,R)\to(X',R')$, any natural transformation $T:X\to R'$ is invertible. This is indeed the case, as we may define $T^{-1}$ to be $i'\circ T$, and verify it is indeed inverse to $T$ upon proceeding similarly to Lemma E.5.4.7.

$\square$

REMARK E.5.4.9. The pseudo-functor $\phi:\mathbf{Groupoids}\to\mathbf{Cat}$ induces a strict isomorphism of 2-categories between the 2-category $\mathbf{Groupoids}$ and the sub 2-category of all small categories whose morphisms are all isomorphisms. We may therefore view any such category in its effective-small-category incarnation, and we shall do so without mentioning $\phi$, knowing that interchanging between the two perspectives amounts to appealing to $\phi$ being a strict isomorphism of 2-categories. We will call $\mathbf{Groupoids}$ both the category defined in Definition E.4.1.1, and the image of $\phi$, and we shall be identifying their 2-category structures.

We have the following example of a pseudo-functor that is not strongly fully faithful (nor fully faithful) but is strongly faithful.

## PDF page 910

**910** · **CHAPTER E. TOPOLOGICAL STACKS**

LEMMA E.5.4.10. *The category of topological groupoids* $\mathbf{CGWH}\text{-}\mathbf{Grpd}$ *is a 2-category. Moreover, the forgetful functor* $u : \mathbf{CGWH}\text{-}\mathbf{Grpd} \to \mathbf{Groupoids}$ *is a strict faithful pseudo-functor.*

PROOF. The forgetful functor induces injective set-functions on objects of the Hom-categories by faithfulness of the forgetful functor $\mathbf{CGWH} \to \mathbf{Sets}$. For any two objects of $\mathbf{CGWH}\text{-}\mathbf{Grpd}$, the induced functor between Hom-categories is faithful for the same reason. Strictness of $u$ follows from the fact that morphisms between topological groupoids are defined analogously to morphisms of groupoids in sets (see Definition E.4.1.1) and hence the structure maps of the coherence constraint of $u$ are the identity. $\square$

**E.5.5. 2-category of 2-commutative diagrams.** In this section we shall describe in detail the 2-category of 2-commutative diagrams in a 2-category. The concept of 2-commutativity for diagrams in a 2-category was introduced in Definition E.5.2.4. This construction will enable us to discuss 2-categorical fibre products in a concrete manner in §E.5.7 below without a general discussion on 2-limits.

E.5.5.1. *Construction of the 2-category of 2-commutative diagrams.* We fix a 2-category $\mathcal{C}$ and objects $A, B, C$, with 1-morphisms $f : B \to A$, $g : C \to A$.

CONSTRUCTION E.5.5.1. We define the class $\mathrm{Diagrams}(f, g)$, whose elements are 4-tuples $(D, a, b, \alpha)$ where $D \in \mathrm{Ob}(\mathcal{C})$, $a : D \to B$ and $b : D \to C$ are 1-morphisms, and $\phi : f \circ a \Rightarrow g \circ b$ is a 2-isomorphism. We represent the elements of $\mathrm{Diagrams}(f, g)$ pictorially as (not necessarily commutative) diagrams:

(E.5.5.1)

```latex
\begin{tikzcd}
D \arrow[r, "a"] \arrow[d, "b"'] & B \arrow[d, "f"] \\
C \arrow[r, "g"'] \arrow[ur, Leftrightarrow, "\phi"'] & A
\end{tikzcd}
```

We note that $\mathrm{Diagrams}(f, g)$ is a class, since it is contained in the union of the sets:

$$\mathrm{Ob}(\mathbf{Hom}_{\mathcal{C}}(D, B) \times \mathbf{Hom}_{\mathcal{C}}(D, C)) \times \mathrm{Arrows}(\mathbf{Hom}_{\mathcal{C}}(D, A))$$

indexed by the elements $D$ of the class $\mathrm{Ob}(\mathcal{C})$. In particular, $\mathrm{Diagrams}(f, g)$ is a set if $\mathcal{C}$ is a *small* 2-category.

NOTATION E.5.5.1. We note that in Definition E.5.2.4, we denoted the 2-isomorphism rendering a diagram 2-commutative in the 2-category $\mathcal{C}$ as follows:

```latex
\begin{tikzcd}
D \arrow[r, "a"] \arrow[d, "b"'] & B \arrow[d, "f"] \arrow[dl, Rightarrow, "\phi"] \\
C \arrow[r, "g"'] & A
\end{tikzcd}
```

It is our preference to favor a more symmetric notation, in light of the definition of 1-morphisms between 2-commutative diagrams, to be discussed below, in order to avoid conveying the incorrect impression of a choice being made of a preferred order between the morphisms $f \circ a$ and $g \circ b$.

CONSTRUCTION E.5.5.2. For any two 2-commutative diagrams $(D, a, b, \phi)$ and $(D', c, d, \psi)$, we define the category $\mathbf{Hom}((D, a, b, \phi), (D', c, d, \psi))$ whose:

(1) objects are triples $(k, \alpha, \beta)$ where:

(a) $k : D' \to D$ is a 1-morphism in $\mathcal{C}$.

(b) $\alpha : c \Rightarrow a \circ k$, $\beta : d \Rightarrow b \circ k$ are 2-isomorphisms in $\mathcal{C}$, such that the following identity of 2-morphisms $f \circ c \Rightarrow g \circ b \circ k$ in $\mathcal{C}$ holds:

$$(\mathbf{1}_{g} \star \beta) \odot \psi = (\phi \star \mathbf{1}_{k}) \odot (\mathbf{1}_{f} \star \alpha). \tag{E.5.5.2}$$

## PDF page 911

**E.5. 2-CATEGORICAL PREPARATIONS** · **911**

(2) Morphisms $(k, \alpha, \beta) \Rightarrow (k', \alpha', \beta')$ are 2-morphisms $\gamma : k \Rightarrow k'$ such that the following identity as 2-morphisms $c \Rightarrow a \circ k'$ in $\mathcal{C}$ holds:

$$\alpha' = (\mathbf{1}_{a} \star \gamma) \odot \alpha$$

and the following identity as 2-morphisms $d \Rightarrow b \circ k'$ in $\mathcal{C}$ holds:

$$\beta' = (\mathbf{1}_{b} \star \gamma) \odot \beta.$$

We compose morphisms of $\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$ by composing the 2-morphisms $\gamma$ using $\odot$ within 2-morphisms in $\mathcal{C}$, and hence $\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$ is indeed a (small) category.

NOTATION E.5.5.2. We depict the objects of $\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$ pictorially as follows:

(E.5.5.3)

```latex
\begin{tikzcd}
D' \arrow[dr, "k"] \arrow[drr, bend left, "c"] \arrow[ddr, bend right, "d"'] & & \\
& D \arrow[r, "a"] \arrow[d, "b"'] & B \arrow[d, "f"] \\
& C \arrow[r, "g"'] \arrow[ur, Leftrightarrow, "\phi"'] & A
\end{tikzcd}
\qquad
\begin{tikzcd}
D' \arrow[r, bend left, "c"{name=U}] \arrow[r, bend right, "a\circ k"'{name=L}] & B
\arrow[from=U, to=L, Rightarrow, "\alpha"]
\end{tikzcd}
\qquad
\begin{tikzcd}
D' \arrow[r, bend left, "d"{name=U}] \arrow[r, bend right, "b\circ k"'{name=L}] & C
\arrow[from=U, to=L, Rightarrow, "\beta"]
\end{tikzcd}
```

where condition (E.5.5.2) encodes commutativity of the following diagram of 2-(iso)morphisms in $\mathcal{C}$:

(E.5.5.4)

```latex
\begin{tikzcd}
f\circ c \arrow[r, Rightarrow, "{\mathbf 1}_{f}\star\alpha"] \arrow[d, Rightarrow, "\psi"'] & f\circ a\circ k \arrow[d, Rightarrow, "\phi\star{\mathbf 1}_{k}"] \\
g\circ d \arrow[r, Rightarrow, "{\mathbf 1}_{g}\star\beta"'] & g\circ b\circ k
\end{tikzcd}
```

We depict the morphisms of $\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$ as follows:

(E.5.5.5)

```latex
\begin{tikzcd}
& & B \arrow[dr, "f"] & \\
D' \arrow[urr, bend left, "c"] \arrow[r, bend left, "k"{name=U}] \arrow[r, bend right, "k'"'{name=L}] \arrow[drr, bend right, "d"'] & D \arrow[ur, "a"] \arrow[dr, "b"'] & & A \\
& & C \arrow[ur, "g"'] &
\arrow[from=U, to=L, Rightarrow, "\gamma"]
\end{tikzcd}
\qquad
\begin{tikzcd}
c \arrow[r, Rightarrow, "\alpha"] \arrow[dr, Rightarrow, "\alpha'"'] & a\circ k \arrow[d, Rightarrow, "\mathbf 1_a\star\gamma"] \\
& a\circ k'
\end{tikzcd}
\qquad
\begin{tikzcd}
d \arrow[d, Rightarrow, "\beta"'] \arrow[dr, Rightarrow, "\beta'"] & \\
b\circ k \arrow[r, Rightarrow, "\mathbf 1_b\star\gamma"'] & b\circ k'
\end{tikzcd}
```

Succintly, we write:

```latex
\begin{tikzcd}
(D', c, d, \psi) \arrow[r, bend left, "{(k,\alpha,\beta)}"{name=U}] \arrow[r, bend right, "{(k',\alpha',\beta')}"'{name=L}] & (D, a, b, \phi)
\arrow[from=U, to=L, Rightarrow, "\gamma"]
\end{tikzcd}
```

LEMMA E.5.5.3. *Let $(D, a, b, \phi)$, $(D', c, d, \psi)$ be two 2-commutative diagrams, and $k, k', k''$ be three morphisms $(D', c, d, \psi) \to (D, a, b, \phi)$ of 2-commutative diagrams. Given $\gamma : k \Rightarrow k'$ and $\gamma' : k' \Rightarrow k''$ be two morphisms in $\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$, the assignment:*

$$(\gamma, \gamma') \rightsquigarrow \gamma' \odot \gamma$$

*endows $\mathbf{Hom}(((D', c, d, \psi), (D, a, b, \phi))$ with the structure of a small category.*

## PDF page 912

**912** · **CHAPTER E. TOPOLOGICAL STACKS**

PROOF. Indeed, since $\odot$ is associative on 2-morphisms of $\mathcal{C}$ by Axiom (2) of Definition E.5.2.1, the assignment $(\gamma, \gamma') \rightsquigarrow \gamma' \odot \gamma$ defines an associative composition law

$$\mathrm{Hom}(k, k') \times \mathrm{Hom}(k', k'') \to \mathrm{Hom}(k, k'').$$

As the objects of $\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$ are contained in the product of the set of 1-morphisms $D' \to D$, the set of 2-morphisms $c \Rightarrow k \circ a$ in $\mathcal{C}$, and the set of 2-morphisms $d \Rightarrow k \circ b$ in $\mathcal{C}$, the class of the objects of $\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$ is a set. Moreover, morphisms between two such objects $(k, \alpha, \beta)$ and $(k', \alpha', \beta')$ are contained in the set of 2-morphisms $k \Rightarrow k'$, and hence are themselves a set. It follows that $\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$ is a small category. $\square$

For a triple $(D, a, b, \phi)$, $(D', c, d, \psi)$, $(D'', r, s, \lambda)$ of elements of $\mathrm{Diagrams}(f, g)$, we define a functor

$$c(\bullet, \bullet) : \mathbf{Hom}((D'', r, s, \lambda), (D', c, d, \psi)) \times \mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi)) \to \mathbf{Hom}((D'', r, s, \lambda), (D, a, b, \phi))$$

by setting, for objects $(k, \alpha, \beta) : (D', c, d, \psi) \to (D, a, b, \phi)$ and $(k', \alpha', \beta') : (D'', r, s, \lambda) \to (D', c, d, \psi)$:

$$c((k', \alpha', \beta'), (k, \alpha, \beta)) := (k \circ k', (\alpha' \star \mathbf{1}_{k}) \odot \alpha, (\beta' \star \mathbf{1}_{k}) \odot \beta) \tag{E.5.5.6}$$

and given morphisms

(E.5.5.7)

```latex
\begin{tikzcd}[column sep=large]
(D'', r, s, \lambda) \arrow[r, bend left, "{(k',\alpha',\beta')}"{name=U1}] \arrow[r, bend right, "{(k_2,\alpha_2,\beta_2)}"'{name=L1}] & (D', c, d, \psi) \arrow[r, bend left, "{(k,\alpha,\beta)}"{name=U2}] \arrow[r, bend right, "{(k_1,\alpha_1,\beta_1)}"'{name=L2}] & (D, a, b, \phi)
\arrow[from=U1, to=L1, Rightarrow, "\gamma_2"]
\arrow[from=U2, to=L2, Rightarrow, "\gamma_1"]
\end{tikzcd}
```

we define

$$c(\gamma_{2}, \gamma_{1}) := \gamma_{1} \star \gamma_{2} \tag{E.5.5.8}$$

where $\gamma_{1} \star \gamma_{2}$ is the morphism making the following joined diagram 2-commute

(E.5.5.9)

```latex
\begin{tikzcd}[column sep=huge]
(D, a, b, \phi) \arrow[r, bend left, "{c((k,\alpha,\beta),(k',\alpha',\beta'))}"{name=U}] \arrow[r, bend right, "{c((k_1,\alpha_1,\beta_1),(k_2,\alpha_2,\beta_2))}"'{name=L}] & (D'', r, s, \lambda)
\arrow[from=U, to=L, Rightarrow, "\gamma_2\star\gamma_1"]
\end{tikzcd}
```

LEMMA E.5.5.4. *Let $\mathcal{C}$ be a 2-category, and $A, B, C$ objects of $\mathcal{C}$, with 1-morphisms $f : B \to A$, $g : C \to A$. The datum of:*

*(1) The class $\mathrm{Diagrams}(f, g)$ constructed in Construction E.5.5.1.*

*(2) For all pairs of 2-commutative diagrams $(D, a, b, \phi)$ and $(D', c, d, \psi)$, the category:*

$$\mathbf{Hom}((D', c, d, \psi), (D, a, b, \phi))$$

*constructed in Construction E.5.5.2.*

*(3) The bifunctor $c(\bullet, \bullet)$ constructed in (E.5.5.6) and (E.5.5.8).*

*is a 2-category, denoted $\mathbf{Diagrams}(f, g)$.*

PROOF. We have to check that indeed $c((k', \alpha', \beta'), (k, \alpha, \beta))$ is an object of $\mathbf{Hom}((D'', r, s, \lambda), (D, a, b, \phi))$. To see this, we are to check that the following diagram of 2-morphisms in $\mathcal{C}$:

(E.5.5.10)

```latex
\begin{tikzcd}
f\circ r \arrow[r, Rightarrow, "{\mathbf 1}_{f}\star\alpha'"] \arrow[d, Rightarrow, "\lambda"'] & f\circ c\circ k' \arrow[r, Rightarrow, "{\mathbf 1}_{f}\star\alpha\star{\mathbf 1}_{k'}"] \arrow[d, Rightarrow, "\psi\star{\mathbf 1}_{k'}"'] & f\circ a\circ(k\circ k') \arrow[d, Rightarrow, "\phi\star{\mathbf 1}_{k\circ k'}=\phi\star{\mathbf 1}_{k}\star{\mathbf 1}_{k'}"] \\
g\circ s \arrow[r, Rightarrow, "{\mathbf 1}_{g}\star\beta'"'] & g\circ d\circ k' \arrow[r, Rightarrow, "{\mathbf 1}_{g}\star\beta\star{\mathbf 1}_{k'}"'] & g\circ b\circ(k\circ k')
\end{tikzcd}
```

is commutative. This is in turn checked using Axiom (2) from Definition E.5.2.1 on associativity of horizontal compositions, to deduce commutativity of the rightmost square, alongside the identity $\mathbf{1}_{k \circ k'} = \mathbf{1}_{k} \star \mathbf{1}_{k'}$, and,

## PDF page 913

**E.5. 2-CATEGORICAL PREPARATIONS** · **913**

upon calling $\alpha'' := (\alpha' \star \mathbf{1}_{k}) \odot \alpha$ and $\beta'' := (\beta' \star \mathbf{1}_{k}) \odot \beta$, the identity:

$$(\mathbf{1}_{f} \star \alpha \star \mathbf{1}_{k'}) \circ (\mathbf{1}_{f} \star \alpha') = (\mathbf{1}_{f} \circ \mathbf{1}_{f}) \star ((\alpha' \star \mathbf{1}_{k'}) \odot \alpha) = \mathbf{1}_{f} \star \alpha''$$

and:

$$(\mathbf{1}_{g} \star \beta \star \mathbf{1}_{k'}) \odot (\mathbf{1}_{g} \star \beta') = (\mathbf{1}_{g} \circ \mathbf{1}_{g}) \star ((\beta' \star \mathbf{1}_{k'}) \odot \beta) = \mathbf{1}_{g} \star \beta''.$$

Both of the above identities follow from Axioms (1) and (2) of Definition E.5.2.1. We deduce that the definition of $c(\bullet, \bullet)$ is well-posed. That it satisfies the axioms from Definition E.5.2.1 is a consequence of $\mathcal{C}$ being a 2-category. $\square$

**E.5.6. 2-final objects in $\mathbf{Diagrams}(f, g)$.** We will now define the concept of 2-fibre products, and we shall then discuss a series of examples of 2-categories of interest that contain 2-fibre products. First, we introduce the concept of *final objects* in a 2-category. One way to assign conditions on objects of a 2-category $\mathcal{C}$ is to assign such conditions on the ordinary category $\mathrm{Cat}(\mathcal{C})$ associated to $\mathcal{C}$ (see Construction E.5.2.6). We recall that an object $x$ in a locally small category $\mathcal{D}$ is *weakly terminal* if and only if for every object $y \in \mathrm{Ob}(\mathcal{D})$, there exists a morphism $y \to x$ in $\mathcal{D}$ (see [$\mathbf{Ka}$, §2], especially the discussion after [$\mathbf{Ka}$, Thm. 2.1]).

DEFINITION E.5.6.1. Let $\mathcal{C}$ be a 2-category. An object $A$ of $\mathcal{C}$ is *final in $\mathcal{C}$* if and only if:

(1) As an object of $\mathrm{Cat}(\mathcal{C})$, $A$ is weakly terminal.

(2) For any object $B$ of $\mathcal{C}$ and any two 1-morphisms $f, g : B \rightrightarrows A$, there exists a unique 2-isomorphism $\alpha : f \Rightarrow g$ in $\mathcal{C}$.

Several ambiguities arise around the concept of final objects in a 2-category, and one has to start distinguishing among varying degrees of strength of the notions of final objects. We refer the reader to [$\mathbf{GR}$, Ch. 2, §2.5] for a discussion of 2-limits and 2-colimits and related (non-)uniqueness aspects, and especially the discussion between [$\mathbf{GR}$, Ch. 2, §2, Def. 2.5.14] and [$\mathbf{GR}$, Ch. 2, §2, Prop. 2.5.15], for a useful special situation when final objects can be defined.

The definition of final objects provided in Definition E.5.6.1 is sufficient for all our purposes. In particular, by introducing a suitable diagram 2-category $\mathbf{Diagrams}(f, g)$ as provided by Lemma E.5.5.4, we can define the notion of 2-fibre products that will be used to assign conditions on 1-morphisms of stacks in groupoids. Such notion can be introduced in wider generality, and we refer the interested reader to [$\mathbf{GR}$, Ch. 2, §2, Rem. 2.5.2,(v)].

We can now assign the following:

DEFINITION E.5.6.2. Let $\mathcal{C}$ be a 2-category, $A, B, C \in \mathrm{Ob}(\mathcal{C})$, $f : B \to A$ and $g : C \to A$ two 1-morphisms. We define a *2-fibre product* for $(f, g)$ in $\mathcal{C}$ to be any final object of the 2-category $\mathbf{Diagrams}(f, g)$.

The above Definition E.5.6.2 in particular means that a 2-fibre product of $f, g$ is the datum of an object $P$ of $\mathcal{C}$, equipped with 1-morphisms $a : P \to B$, $b : P \to C$ and a 2-isomorphism $\phi : f \circ a \Rightarrow g \circ b$ making the following diagram 2-commute:

```latex
\begin{tikzcd}
P \arrow[r, "b"] \arrow[d, "a"'] & C \arrow[d, "g"] \\
B \arrow[r, "f"'] \arrow[ur, Leftrightarrow, "\phi"'] & A
\end{tikzcd}
```

such that every other object of $\mathbf{Diagrams}(f, g)$ has a 1-morphism to $(P, a, b, \phi)$, and for any two 1-morphisms $p = (k, \alpha, \beta) : (D, a', b', \phi') \to (P, a, b, \phi)$ and $q = (k', \alpha', \beta') : (D'', a'', b'', \phi'') \to (P, a, b, \phi)$, there exists a unique 2-isomorphism $\gamma : p \Rightarrow q$ in $\mathbf{Diagrams}(f, g)$, i.e. a unique 2-isomorphism:

$$\gamma : k \Rightarrow k'$$

## PDF page 914

**914** · **CHAPTER E. TOPOLOGICAL STACKS**

in $\mathcal{C}$ such that:

$$(\mathbf{1}_{a} \star \gamma) \odot \alpha = \alpha', \quad (\mathbf{1}_{b} \star \gamma) \odot \beta = \beta'.$$

NOTATION E.5.6.1. We denote by $(B \times^{2}_{f, A, g} C, p_{1}, p_{2}, \phi)$ any 2-fibre product $(P, a, b, \phi)$ in $\mathbf{Diagrams}(f, g)$, if it exists.

**E.5.7. 2-fibre products and 1-fibre products.** We have collected basic examples of 2-categories and of pseudo-functors. We will now briefly focus on those 2-categories all of whose 2-morphisms are 2-isomorphisms. These will be the only 2-categories of interest throughout the development of the sought-for theory of stacks in groupoids on a suitable site of topological spaces.

In this section, we shall recall results concerning the existence of 2-fibre products in 2-categories of interest. Our main source within the literature will be [$\mathbf{SP}$, Tags 003O, 02XG, 02XJ, 003S], to which we shall refer the reader for the relevant arguments, with occasional exceptions. This will conclude the 2-categorical preparations needed later in this appendix.

We begin with a definition:

DEFINITION E.5.7.1. Let $\mathcal{C}$ be a 2-category. We say that $\mathcal{C}$ is a *strict $(2, 1)$-category* if and only if every 2-morphism in $\mathcal{C}$ is a 2-isomorphism.

The notion of strict $(2, 1)$-category is also known, in the literature, under the terminology of *groupoid-enriched category* (see [$\mathbf{FM}$, §1]). For every pair of objects $A, B \in \mathrm{Ob}(\mathcal{C})$ of a strict $(2, 1)$-category $\mathcal{C}$, the category $\mathbf{Hom}_{\mathcal{C}}(A, B)$ is a groupoid (see [$\mathbf{SP}$, Tag 003I]) whose set of objects is the set of 1-morphisms $f : A \to B$, and whose set of morphisms is the set of 2-morphisms $f \Rightarrow f'$, all isomorphisms.

E.5.7.1. *Strict $(2, 1)$-categories of interest.* We will now discuss four examples of strict $(2, 1)$-categories, ultimately focusing on the example of stacks in groupoids over a site, for which we will discuss existence of 2-fibre products.

EXAMPLE E.5.7.2. We recall that upon fixing a small category $\mathcal{D}$, we may consider the following datum:

(1) the class of all pairs $(\mathcal{S}, p)$ where $\mathcal{S}$ is a small category and $p : \mathcal{S} \to \mathcal{D}$ is a functor.

(2) For any two pairs $(\mathcal{S}, p)$ and $(\mathcal{S}', p')$, the category $\mathbf{Hom}((\mathcal{S}, p), (\mathcal{S}', p'))$ whose:

(a) objects are functors $F : \mathcal{S} \to \mathcal{S}'$ such that $p' \circ F = p$.

(b) Morphisms $t : F \Rightarrow F'$ for $F, F' : (\mathcal{S}, p) \to (\mathcal{S}', p')$ are natural transformations of functors such that $p'(t_{A}) = \mathbf{1}_{p(A)}$ for every object $A \in \mathrm{Ob}(\mathcal{S})$.

We note that for any two pairs $(\mathcal{S}, p)$ and $(\mathcal{S}', p')$, there is a faithful forgetful functor:

$$\mathbf{Hom}((\mathcal{S}, p), (\mathcal{S}', p')) \to \mathbf{Hom}_{\mathbf{Cat}}(\mathcal{S}, \mathcal{S}')$$

given by sending a functor $F : \mathcal{S} \to \mathcal{S}'$ to itself forgetting its compatibility with $p$ and $p'$, and sending a natural transformation $t : F \Rightarrow F'$ to itself. The bifunctor $(\circ, \star)$ constructed in §E.5.1 (see Definition E.5.1.11) restricts to a bifunctor:

$$c_{(\mathcal{S}, p), (\mathcal{S}', p'), (\mathcal{S}'', p'')} : \mathbf{Hom}((\mathcal{S}, p), (\mathcal{S}', p')) \times \mathbf{Hom}((\mathcal{S}', p'), (\mathcal{S}'', p'')) \to \mathbf{Hom}((\mathcal{S}, p), (\mathcal{S}'', p''))$$

which satisfies the Axioms from Definition E.5.2.1 by Lemma E.5.1.14. We denote the resulting 2-category by $\mathbf{Cat}/\mathcal{D}$. We refer to it as the *2-category of categories over $\mathcal{D}$.* The compositions within $\mathbf{Cat}/\mathcal{D}$ are inherited from those on $\mathbf{Cat}$, and hence the worked example of $\mathbf{Cat}$ (see Definition E.5.1.20 and Lemma E.5.1.14) can be used to compute compositions within $\mathbf{Cat}/\mathcal{D}$.

We note that the 2-category described in Example E.5.7.2 is not a strict $(2, 1)$-category. However, we can associate to any 2-category a strict $(2, 1)$-category by re-defining the sets of 2-morphisms to be comprised only of those 2-morphisms that are isomorphisms (see [$\mathbf{SP}$, Tag 02X8], and specifically [$\mathbf{SP}$, Tag 003K]).

Within the strict $(2, 1)$-category $(\mathbf{Cat}/\mathcal{D})^{\mathrm{strict}}$ associated to $\mathbf{Cat}/\mathcal{D}$ from Example E.5.7.2, we make the following Construction.

## PDF page 915

**E.5. 2-CATEGORICAL PREPARATIONS** · **915**

CONSTRUCTION E.5.7.3. We let $F : (\mathcal{X}, p_{\mathcal{X}}) \to (\mathcal{S}, p_{\mathcal{S}})$ and $G : (\mathcal{Y}, p_{\mathcal{Y}}) \to (\mathcal{S}, p_{\mathcal{S}})$ be morphisms of categories over $\mathcal{D}$. We define $\mathcal{X} \times_{F, \mathcal{S}, G} \mathcal{Y}$ to be the small category whose:

(1) objects are 4-tuples $(A, x, y, \phi)$ with $A \in \mathrm{Ob}(\mathcal{D})$, $x \in \mathrm{Ob}(\mathcal{X}_{A})$, $y \in \mathrm{Ob}(\mathcal{Y}_{A})$, $\phi : F(x) \to G(y)$ is an isomorphism in $\mathcal{S}$.

(2) Morphisms $(A, x, y, \phi) \to (A', x', y', \phi')$ are given by pairs $(a, b)$ with $a : x \to x'$ a morphism in $\mathcal{X}$, $b : y \to y'$ a morphism in $\mathcal{Y}$, satisfying the following properties:

(a) $p_{\mathcal{X}}(a) = p_{\mathcal{Y}}(b)$ as morphisms of $\mathcal{D}$.

(b) As morphisms of $\mathcal{S}$, we have the identity:

$$\phi' \circ F(a) = G(b) \circ \phi.$$

We further define the functors $p_{1} : \mathcal{X} \times^{2}_{F, \mathcal{S}, G} \mathcal{Y} \to \mathcal{X}$ and $p_{2} : \mathcal{X} \times^{2}_{F, \mathcal{S}, G} \mathcal{Y} \to \mathcal{Y}$ to be the forgetful functors. We note that $\mathcal{X} \times^{2}_{F, \mathcal{S}, G} \mathcal{Y}$ can be made into an object of $(\mathbf{Cat}/\mathcal{D})^{\mathrm{strict}}$ by equipping it with the projection to $\mathcal{D}$ given by the composition $\pi := p_{\mathcal{X}} \circ p_{1} = p_{\mathcal{Y}} \circ p_{2}$. We call $\psi : F \circ p_{\mathcal{X}} \to G \circ p_{\mathcal{Y}}$ the natural transformation of functors assigned on the arbitrary object $\xi := (A, x, y, \phi)$ by:

$$\psi_{\xi} := \phi : F(p_{\mathcal{X}}(\xi)) = F(x) \to G(y) = G(p_{\mathcal{Y}}(\xi)).$$

We denote by:

$$\mathcal{X} \times^{2}_{F, \mathcal{S}, G} \mathcal{Y} \tag{E.5.7.1}$$

the datum $(\mathcal{X} \times^{2}_{F, \mathcal{S}, G} \mathcal{Y}, p_{1}, p_{2}, \psi)$.

For the strict $(2, 1)$-category associated to $\mathbf{Cat}/\mathcal{D}$, we have the following:

LEMMA E.5.7.4. *Let $\mathcal{D}$ be a small category. Let $F : \mathcal{X} \to \mathcal{S}$ and $G : \mathcal{Y} \to \mathcal{S}$ be 1-morphisms of categories over $\mathcal{D}$. A 2-fibre product in the strict $(2, 1)$-category $(\mathbf{Cat}/\mathcal{D})^{\mathrm{strict}}$ of all small categories over $\mathcal{D}$ for $(F, G)$ exists, and it is equivalent to $\mathcal{X} \times^{2}_{\mathcal{S}} \mathcal{Y}$ from Construction E.5.7.3.*

PROOF. This is [$\mathbf{SP}$, Tag 0040]. We further refer to the reader to [$\mathbf{Ac}$, Ch. I, Lemma 1.2.1]. $\square$

We recall here for the reader's convenience the following definition (see [$\mathbf{SP}$, Tag 02XK]):

DEFINITION E.5.7.5. Let $\mathcal{D}$ be a small category, $p : \mathcal{S} \to \mathcal{D}$ a small category over $\mathcal{D}$. For any pair of objects $A, B \in \mathrm{Ob}(\mathcal{S})$, a *strongly $\mathcal{D}$-cartesian morphism* $f : A \to B$ is a morphism in $\mathcal{S}$ such that for every object $C \in \mathrm{Ob}(\mathcal{C})$ the map:

$$\mathrm{Hom}_{\mathcal{S}}(C, A) \to \mathrm{Hom}_{\mathcal{S}}(C, B) \times_{\mathrm{Hom}_{\mathcal{D}}(p(C), p(B))} \mathrm{Hom}_{\mathcal{D}}(p(C), p(A))$$

assigned by sending $g : C \to B$ to $(f \circ g, p(g))$, is a bijection.

We observe that for any object $A$ of $\mathcal{S}$ with $p(A) = D$ in $\mathcal{D}$, and any morphism $\phi : D' \to D$ in $\mathcal{D}$, if a strongly cartesian morphism $f : A' \to A$ exists such that $p(f) = \phi$, then the pair $(A', f)$ is unique up to unique isomorphism in $\mathcal{S}$ by Yoneda's Lemma. We may therefore denote refer to the pair $(A', f)$ via the notation $\phi^{*}A \to A$. Strongly cartesian morphisms satisfy the following basic permanence properties:

LEMMA E.5.7.6. *Let $\mathcal{D}$ be a small category, $p : \mathcal{S} \to \mathcal{D}$ a small category over $\mathcal{D}$.*

*(1) Strongly cartesian morphisms in $\mathcal{S}$ are stable under finite compositions.*

*(2) For any pair of objects $A, B \in \mathrm{Ob}(\mathcal{S})$, if $f : A \to B$ is an isomorphism, then $f$ is strongly cartesian.*

*(3) Let $f : A \to B$ be a strongly cartesian morphism between objects of $\mathcal{S}$. If $p(f)$ is an isomorphism in $\mathcal{D}$, then $f$ is an isomorphism.*

PROOF. We refer the reader to [$\mathbf{SP}$, Tag 02XL] and [$\mathbf{Ac}$, Ch. I, Lemma 1.3.1]. $\square$

Following [$\mathbf{SP}$, Tag 02XM], we recall the following:

## PDF page 916

**916** · **CHAPTER E. TOPOLOGICAL STACKS**

DEFINITION E.5.7.7. Let $\mathcal{D}$ be a small category and $p : \mathcal{S} \to \mathcal{D}$ a small category over $\mathcal{D}$. We say $p : \mathcal{S} \to \mathcal{D}$ is a *fibered category* if and only if for every object $A \in \mathrm{Ob}(\mathcal{S})$, and any morphism $\phi : D \to p(A)$ in $\mathcal{D}$, there exists a strongly cartesian morphism $f : \phi^{*}A \to A$ with $p(f) = \phi$.

EXAMPLE E.5.7.8. (The 2-category of fibered categories over a fixed category) We let $\mathcal{D}$ be a small category. We define $\mathbf{Fib}/\mathcal{D}$ to be the sub 2-category of the 2-category $\mathbf{Cat}/\mathcal{D}$ assigned as follows:

(1) The objects of $\mathbf{Fib}/\mathcal{D}$ are small fibered categories $p : \mathcal{S} \to \mathcal{D}$.

(2) The 1-morphisms $F : (\mathcal{S}, p) \to (\mathcal{S}', p')$ are 1-morphisms in $\mathbf{Cat}/\mathcal{D}$ that, in addition, satisfy the property of preserving strongly cartesian morphisms.

(3) The 2-morphisms of $\mathbf{Fib}/\mathcal{D}$ are those natural transformations of functors $t : F \Rightarrow F'$, for 1-morphisms $F, F' : (\mathcal{S}, p) \to (\mathcal{S}', p')$, such that $t$ is a 2-morphism in $\mathbf{Cat}/\mathcal{D}$.

We define the composition bifunctor:

$$c(\bullet, \bullet) : \mathbf{Hom}_{\mathbf{Fib}/\mathcal{D}}((\mathcal{S}, p), (\mathcal{S}', p')) \times \mathbf{Hom}_{\mathbf{Fib}/\mathcal{D}}((\mathcal{S}', p'), (\mathcal{S}'', p'')) \to \mathbf{Hom}_{\mathbf{Fib}/\mathcal{D}}((\mathcal{S}, p), (\mathcal{S}'', p''))$$

to be the restriction of the composition bifunctor on $\mathbf{Cat}/\mathcal{D}$, which is in turn the restriction of the composition bifunctor $(\circ, \star)$ from §E.5.1. The above datum is a 2-category, denoted $\mathbf{Fib}/\mathcal{D}$. We shall refer to it as the *2-category of categories fibered over $\mathcal{D}$.*

The above example is [$\mathbf{SP}$, Tag 02XP], and as noted in *loc.cit.*, $\mathbf{Fib}/\mathcal{D}$ is a genuine 2-category. In order to state the next Lemma, we therefore pass to its associated strict $(2, 1)$-category, $(\mathbf{Fib}/\mathcal{D})^{\mathrm{strict}}$. The following Lemma is [$\mathbf{SP}$, Tag 02XQ]:

LEMMA E.5.7.9. *Let $\mathcal{D}$ be a small category. Then the strict $(2, 1)$-category associated to $\mathbf{Fib}/\mathcal{D}$ contains 2-fibre products, and they are computed by the 2-fibre products in $(\mathbf{Cat}/\mathcal{D})^{\mathrm{strict}}$ from Lemma E.5.7.4. Moreover, for any object $T$ of $\mathcal{D}$, and any 1-morphisms $f : \mathcal{X} \to \mathcal{S}$ and $g : \mathcal{Y} \to \mathcal{S}$ of categories fibered over $\mathcal{D}$, we have a canonical isomorphism of fibre categories:*

$$(\mathcal{X} \times^{2}_{f, \mathcal{S}, g} \mathcal{Y})_{T} = \mathcal{X}_{T} \times^{2}_{f_{T}, \mathcal{S}_{U}, g_{T}} \mathcal{Y}_{T}$$

*where the 2-fibre product $\mathcal{X}_{U} \times^{2}_{f_{U}, \mathcal{S}_{U}, g_{U}} \mathcal{Y}_{U}$ is formed in $\mathbf{Cat}$.*

PROOF. This is [$\mathbf{SP}$, Tag 02XQ] and [$\mathbf{SP}$, Tag 02XI]. We further refer the reader to [$\mathbf{Ac}$, Ch.I,Lemma 1.3.6] and to [$\mathbf{Ac}$, Ch.I,Lemma 1.2.2]. $\square$

EXAMPLE E.5.7.10. We may now consider the full sub 2-category $\mathbf{Groupoids}/\mathcal{D}$ of $\mathbf{Fib}/\mathcal{D}$ of those fibered categories $p : \mathcal{S} \to \mathcal{D}$ whose fibre categories over $\mathcal{D}$ are all groupoids. Then $\mathbf{Groupoids}/\mathcal{D}$ is a strict $(2, 1)$-category with 2-fibre products.

LEMMA E.5.7.11. *Let $\mathcal{D}$ be a small category. Then the strict $(2, 1)$-category $\mathbf{Groupoids}/\mathcal{D}$ of small categories fibered in groupoids over $\mathcal{D}$ has 2-fibre products, and they are computed by the 2-fibre products in $(\mathbf{Cat}/\mathcal{D})^{\mathrm{strict}}$.*

PROOF. This is [$\mathbf{SP}$, Tag 0041]. We further refer the reader to [$\mathbf{Ac}$, Ch.I,Lemma 1.5.3]. $\square$

REMARK E.5.7.12. In Lemma E.5.7.11, we may choose $\mathcal{D} = \mathbf{1}$, the final object in $\mathbf{Cat}$ (see part (1) of Remark E.5.1.20). In this case, $\mathbf{Groupoids}/\mathcal{D} = \mathbf{Groupoids}$ as strict $(2, 1)$-categories, and the Lemma implies the existence of 2-fibre products of groupoids in sets, described by Construction E.5.7.3.

Finally, the last example is the one of our interest.

LEMMA E.5.7.13. *Let $\mathcal{D}$ be a small category equipped with the structure of a site (in the sense of [$\mathbf{SP}$, Tag 00VH]). We define $\mathbf{Stacks}/\mathcal{D}$ to be the full sub 2-category of stacks in groupoids over $\mathcal{D}$. This is a strict $(2, 1)$-category and has 2-fibre products, and they are computed as the stackification of the 2-fibre products in $\mathbf{Groupoids}/\mathcal{D}$.*

## PDF page 917

**E.5. 2-CATEGORICAL PREPARATIONS** · **917**

PROOF. This is [$\mathbf{SP}$, Tag 02ZL]. $\square$

E.5.7.2. *1-fibre products.* We want a notion of fibre products for stacks in groupoids on a site that is rarely used within the literature. It will enable us to compute the stack-theoretic intersection of certain “graph” and “diagonal” sub-stacks of a topological stack of key interest to our work. We review the construction here concerning such an alternate version of fibre products for categories over a fixed small category $\mathcal{D}$, and we will recall criteria for its existence which, contrary to 2-fibre products and as illustrated in Lemma E.5.7.4 , does not always hold within the strict $(2, 1)$-category of stacks in groupoids on a site. Our main source within the literature for the material within this subsection is [$\mathbf{Ac}$, Ch.I-II], with particular emphasis on [$\mathbf{Ac}$, Ch. I, Lemma 1.2.3, Prop. 1.3.1,Thm. 1,Thm. 2] and [$\mathbf{Ac}$, Ch. II, Thm. 4].

DEFINITION E.5.7.14. Let $\mathcal{C}$ be a 2-category, $A, B, C \in \mathrm{Ob}(\mathcal{C})$, $f : B \to A$, $g : C \to A$ two 1-morphisms in $\mathcal{C}$. We define the *1-fibre product* for $(f, g)$ in $\mathcal{C}$, denoted $B \times^{1}_{f, A, g} C$, to be the fibre product of $(f, g)$ in the ordinary locally small category $\mathrm{Cat}(\mathcal{C})$ of Construction E.5.2.6.

LEMMA E.5.7.15. *The 2-category $\mathbf{Cat}$ contains 1-fibre products.*

PROOF. Let $A, B, C \in \mathrm{Ob}(\mathcal{C})$, $f : B \to A$, $g : C \to A$ two 1-morphisms in $\mathbf{Cat}$. We define $B \times^{1}_{f, A, g} C$ to be the category whose class of objects is:

$$\mathrm{Ob}(B \times^{1}_{f, A, g} C) := \mathrm{Ob}(B) \times_{f, \mathrm{Ob}(A), g} \mathrm{Ob}(C)$$

and for any two objects $(x, y)$, $(x', y')$, we define the set of morphisms to be:

$$\mathrm{Hom}((x, y), (x', y')) := \mathrm{Hom}_{B}(x, x') \times_{f, \mathrm{Hom}_{A}(z, z'), g} \mathrm{Hom}_{C}(y, y')$$

where $z := f(x) = g(y)$ and $z' := f(x') = g(y')$. Composition of morphisms in $B \times^{1}_{f, A, g} C$ is defined component-wise. The forgetful functors $p_{1} : B \times^{1}_{f, A, g} C \to B$ and $p_{2} : B \times^{1}_{f, A, g} C \to C$ satisfy $f \circ p_{1} = g \circ p_{2}$ as 1-morphisms in $\mathbf{Cat}$. For the proof that $(B \times^{1}_{f, A, g} C, p_{1}, p_{2})$ verifies the universal property of fibre products in $\mathrm{Cat}(\mathbf{Cat})$, we refer the reader to [$\mathbf{Ac}$, Ch.I,Lemma 1.2.3], applied to $\mathcal{C} = \mathbf{1}$, the final object in $\mathbf{Cat}$ (see part (1) of Remark E.5.1.20). $\square$

In the 2-category of all small categories over a fixed small category $\mathcal{D}$, 1-fibre products exist. This is the content of the following:

LEMMA E.5.7.16. *Let $\mathcal{D}$ be a small category. The 2-category $\mathbf{Cat}/\mathcal{D}$ contains 1-fibre products.*

PROOF. To see this, it is enough to check that 1-fibre products in $\mathbf{Cat}$ are contained in the sub 2-category $\mathbf{Cat}/\mathcal{D}$. Equivalently, that given objects $(A, p_{A} : A \to \mathcal{D})$,$(B, p_{B} : B \to \mathcal{D})$, $(C, p_{C} : C \to \mathcal{D})$ of $\mathbf{Cat}/\mathcal{D}$, and 1-morphisms $f : B \to A$ and $g : C \to A$ in $\mathbf{Cat}/\mathcal{D}$, the 1-fibre product $B \times^{1}_{f, A, g} C$ formed in $\mathbf{Cat}$ is itself a category over $\mathcal{D}$. This is seen by defining $p : B \times^{1}_{f, A, g} C \to \mathcal{D}$ as the composition $p_{A} \circ f \circ p_{1} = p_{A} \circ g \circ p_{2}$, and then checking that the resulting object of $\mathbf{Cat}/\mathcal{D}$ indeed satisfies the universal property of fibre products in $\mathrm{Cat}(\mathbf{Cat}/\mathcal{D})$. We refer the reader to the proof of [$\mathbf{Ac}$, Ch.I,Lemma 1.2.3] for this verification. $\square$

It is not always the case that 1-fibre products exist in $\mathbf{Fib}/\mathcal{D}$, the 2-category of all small categories fibered over the fixed small category $\mathcal{D}$. For a discussion on 1-fibre products in fibered categories we refer the reader to [$\mathbf{Ac}$, Ch.I,p.31-33], with emphasis on [$\mathbf{Ac}$, Ch. I, Examples 4, 5]. The obstruction to the existence of 1-fibre products of fibered categories is the fact that it is not generally true that, given 1-morphisms $f : B \to A$, $g : C \to A$, for all objects $U$ of $\mathcal{D}$ we have $(d^{*}x, d^{*}y) \in \mathrm{Ob}(B \times^{1}_{f, A, g} C)$ for all $(x, y) \in \mathrm{Ob}(B \times^{1}_{f, A, g} C)$ and $d : U' \to U$ a morphism in $\mathcal{D}$. This is also the only obstruction. We have the following definition, which is [$A\mathbf{c}$, Ch. I, Def. 1.3.5]:

DEFINITION E.5.7.17. Let $(A, p_{A})$,$(B, p_{B})$,$(C, p_{C})$ be three small categories fibered over $\mathcal{D}$, and $f : B \to A$, $g : C \to A$ be two 1-morphisms of small categories fibered over $\mathcal{D}$. The 1-fibre product in $\mathbf{Cat}/\mathcal{D}$,

## PDF page 918

**918** · **CHAPTER E. TOPOLOGICAL STACKS**

$B \times^{1}_{f, A, g} C$, has *enough component-wise pullbacks* if and only if for all $(x, y) \in \mathrm{Ob}(B \times^{1}_{f, A, g} C)$ and $d : U' \to U$ any morphism in $\mathcal{D}$, we have:

(1) $(d^{*}x, d^{*}y)$ is an object of $B \times^{1}_{f, A, g} C$.

(2) $(d^{*}x \to x, d^{*}y \to y)$ is a morphism of $B \times^{1}_{f, A, g} C$.

TERMINOLOGY E.5.7.1. We note that the terminology being adopted here of “1-fibre products” corresponds to the terminology “fibre products” of [$\mathbf{Ac}$, Ch.I], and that the condition of having “enough component-wise pullbacks” corresponds to having “componentwise pullbacks”, as defined in [$\mathbf{Ac}$, Ch. I, Def. 1.3.5].

LEMMA E.5.7.18. *Let $\mathcal{D}$ be a small category, and $(A, p_{A})$, $(B, p_{B})$, $(C, p_{C})$ be three small categories fibered over $\mathcal{D}$. Let $f : B \to A$, $g : C \to A$ be two 1-morphisms of small categories fibered over $\mathcal{D}$, such that the 1-fibre product in $\mathbf{Cat}/\mathcal{D}$, $B \times^{1}_{f, A, g} C$, has enough component-wise pullbacks. Then a 1-fibre product for $(f, g)$ exists in the 2-category $\mathbf{Fib}/\mathcal{D}$, and it is computed by the 1-fibre product $B \times^{1}_{f, A, g} C$ for $(f, g)$ in $\mathbf{Cat}/\mathcal{D}$.*

PROOF. We refer the reader to [$\mathbf{Ac}$, Ch.I,Thm.1] for the proof of the first assertion in the Lemma. To verify that $B \times^{1}_{f, A, g} C$ satisfies the universal property, it is enough to observe: as soon as $B \times^{1}_{f, A, g} C$ is an object of $\mathbf{Fib}/\mathcal{D}$ it induces an object in $\mathrm{Cat}(\mathbf{Fib}/\mathcal{D})$, the forgetful functor $\mathrm{Cat}(\mathbf{Fib}/\mathcal{D}) \to \mathrm{Cat}(\mathbf{Cat}/\mathcal{D})$ induced by the forgetful pseudo-functor $\mathbf{Fib}/\mathcal{D} \to \mathbf{Cat}/\mathcal{D}$ is conservative, and conservative functors reflect representable limits. $\square$

REMARK E.5.7.19. In Lemma E.5.7.18, we may choose $\mathcal{D} = \mathbf{1}$, the final object in $\mathbf{Cat}$ (see part (1) of Remark E.5.1.20). In this case, $\mathbf{Fib}/\mathcal{D} = \mathbf{Cat}$ as 2-categories. The Lemma implies the existence of 1-fibre products of small categories, defined in Definition E.5.7.14.

Within $\mathbf{Cat}/\mathcal{D}$, 1-fibre products and 2-fibre products are related according to the following:

LEMMA E.5.7.20. *Let $(A, p_{A})$, $(B, p_{B})$, $(C, p_{C})$ be three categories over $\mathcal{D}$, and $f : B \to A$, $g : C \to A$ two 1-morphisms of categories over $\mathcal{D}$. There exists a canonical 1-morphism of categories over $\mathcal{D}$:*

$$p : B \times^{1}_{f, A, g} C \to B \times^{2}_{f, A, g} C \tag{E.5.7.2}$$

*such that:*

*(1) $p$ is a fully faithful functor of small categories.*

*(2) If $(A, p_{A})$,$(B, p_{B})$,$(C, p_{C})$ are fibered categories over $\mathcal{D}$, and $B \times^{1}_{f, A, g} C$ in $\mathbf{Cat}/\mathcal{D}$ has enough component-wise pullbacks, then $p$ is a 1-morphism of fibered categories over $\mathcal{D}$.*

PROOF. We refer the reader to [$\mathbf{Ac}$, Ch. I, Prop. 1.3.1] for the proof of the Lemma. $\square$

We note that the functor $p$ from (E.5.7.2) in Lemma E.5.7.20 above may not be essentially surjective (see [$\mathbf{Ac}$, Ch. I, Example 7] for an explicit example).

LEMMA E.5.7.21. *Let $\mathcal{D}$ be a small category. Let $(A, p_{A})$, $(B, p_{B})$, $(C, p_{C})$ be three small categories fibered in groupoids over $\mathcal{D}$, and $f : B \to A$, $g : C \to A$ two 1-morphisms of categories fibered in groupoids over $\mathcal{D}$. Then a 1-fibre product for $(f, g)$ exists in the 2-category $\mathbf{Groupoids}/\mathcal{D}$ of all small categories fibered in groupoids over $\mathcal{D}$ if and only if a 1-fibre product for $(f, g)$ exists in the 2-category $\mathbf{Fib}/\mathcal{D}$ of all small categories fibered over $\mathcal{D}$.*

PROOF. The inclusion functor $\mathbf{Groupoids}/\mathcal{D} \to \mathbf{Fib}/\mathcal{D}$ is strict and strongly fully faithful, and hence the induced ordinary functor $\mathrm{Cat}(\mathbf{Groupoids}/\mathcal{D}) \to \mathrm{Cat}(\mathbf{Fib}/\mathcal{D})$ is fully faithful. As fully faithful functors reflect representable limits, a 1-fibre product for $(f, g)$ exists in $\mathbf{Groupoids}/\mathcal{D}$ if and only if $B \times^{1}_{f, A, g} C$, formed in $\mathbf{Cat}/\mathcal{D}$, has enough component-wise pullbacks. Indeed, if so then $B \times^{1}_{f, A, g} C$ is fibered over $\mathcal{D}$ by Lemma E.5.7.18, and fibered in groupoids, hence an object of $\mathbf{Groupoids}/\mathcal{D}$. As the forgetful inclusion functor $\mathrm{Cat}(\mathbf{Groupoids}/\mathcal{D}) \to \mathrm{Cat}(\mathbf{Fib}/\mathcal{D})$ is fully faithful and hence reflects representable limits, $B \times^{1}_{f, A, g} C$

## PDF page 919

**E.5. 2-CATEGORICAL PREPARATIONS** · **919**

is a fibre product in $\mathrm{Cat}(\mathbf{Groupoids}/\mathcal{D})$ if and only if it is a fibre product in $\mathrm{Cat}(\mathbf{Fib}/\mathcal{D})$. Conversely, if a 1-fibre product for $(f, g)$ exists in $\mathbf{Groupoids}/\mathcal{D}$, then its image under the forgetful functor to $\mathbf{Fib}/\mathcal{D}$ is also a 1-fibre product for $(f, g)$, in the 2-category $\mathbf{Fib}/\mathcal{D}$. This is so because $\mathrm{Cat}(\mathbf{Groupoids}/\mathcal{D}) \to \mathrm{Cat}(\mathbf{Fib}/\mathcal{D})$ preserves representable fibre products. It follows $B \times^{1}_{f, A, g} C$ has enough component-wise pullbacks. $\square$

REMARK E.5.7.22. In Lemma E.5.7.21, we may choose $\mathcal{D} = \mathbf{1}$, the final object in $\mathbf{Cat}$ (see part (1) of Remark E.5.1.20). In this case, $\mathbf{Groupoids}/\mathcal{D} = \mathbf{Groupoids}$ as strict $(2, 1)$-categories. The Lemma implies the existence of 1-fibre products of groupoids in sets, since they exist in $\mathbf{Fib}/\mathcal{D} = \mathbf{Cat}$ by Remark E.5.7.19.

We will need a criterion for the existence of 1-fibre products in $\mathbf{Fib}/\mathcal{D}$. First, we recall a key construction:

CONSTRUCTION E.5.7.23. We let $\mathcal{D}$ be a small category, and $F : \mathcal{D}^{\mathrm{opp}} \to \mathbf{Groupoids}$ a functor. We define the category $\mathcal{S}_{F}$ whose objects are defined to be the set:

$$\mathrm{Ob}(\mathcal{S}_{F}) := \{(U, x) \mid U \in \mathrm{Ob}(\mathcal{D}), x \in \mathrm{Ob}(F(U))\} \tag{E.5.7.3}$$

and, for any pair of objects $(U', x')$ and $(U, x)$ of $\mathcal{S}_{F}$, we define the set of morphisms to be:

$$\mathrm{Hom}_{\mathcal{S}_{F}}((U', x'), (U, x)) := \coprod_{f \in \mathrm{Hom}_{\mathcal{D}}(U', U)} \mathrm{Hom}_{F(U')}(x', F(f)(x)). \tag{E.5.7.4}$$

Composition of morphisms is defined as follows. For $(f, \phi) \in \mathrm{Hom}_{\mathcal{S}_{F}}((U', x'), (U, x))$, with $f \in \mathrm{Hom}_{\mathcal{D}}(U', U)$ and $\phi \in \mathrm{Hom}_{F(U')}(x', F(f)(x))$, and for $(U'', x'') \in \mathrm{Ob}(\mathcal{S}_{F})$ and $(g, \psi) \in \mathrm{Hom}_{\mathcal{S}_{F}}((U'', x''), (U', x'))$, we define:

$$(g, \psi) \circ (f, \phi) := (g \circ f, F(g)(\phi) \circ \psi). \tag{E.5.7.5}$$

We further define the forgetful functor

$$p_{F} : \mathcal{S}_{F} \to \mathcal{D} \tag{E.5.7.6}$$

by $p_{F}(U, x) := U$, and $p_{F}(f, \phi) := f$.

Such fibered categories (E.5.7.6) are called *split.* We'll be interested in the case $\mathcal{D} = \mathbf{CGWH}_{\alpha}$ and $F$ the “functor of points” oof a fixed groupoid in $\mathbf{CGWH}_{\alpha}$. The category over $\mathcal{D}$ assigned by $(\mathcal{S}_{F}, p_{F})$ is a fibered category by [$\mathbf{SP}$, Tag 02XV]. Since $F(U)$ is a groupoid for every object $U$ in $\mathcal{D}$, $(\mathcal{S}_{F}, p_{F})$ is fibered in groupoids by [$\mathbf{SP}$, Tag 003V]. We further note that formation of $\mathcal{S}_{F}$ is natural in $F$, in the sense that the assignment $F \rightsquigarrow \mathcal{S}_{F}$ is a strict pseudo-functor $\mathbf{Functors}(\mathcal{D}^{\mathrm{opp}}, \mathbf{Groupoids}) \to \mathbf{Fib}/\mathcal{D}$, where the source is an ordinary category regarded as a 2-category with all its 2-morphisms being the identities.

LEMMA E.5.7.24. *Let $\mathcal{D}$ be a small category, and $F, G, H$ three functors $\mathcal{D}^{\mathrm{opp}} \to \mathbf{Groupoids}$. Let $t : F \Rightarrow H$, $s : G \Rightarrow H$ two natural transformations. Then there exists a canonical isomorphism of categories over $\mathcal{D}$:*

$$\mathcal{S}_{F} \times^{1}_{t, \mathcal{S}_{H}, s} \mathcal{S}_{G} \to \mathcal{S}_{F \times_{t, H, s} G} \tag{E.5.7.7}$$

*In particular, $\mathcal{S}_{F} \times^{1}_{t, \mathcal{S}_{H}, s} \mathcal{S}_{G}$ has enough component-wise pullbacks, and is the 1-fibre product of $t, s$ in $\mathbf{Groupoids}/\mathcal{D}$.*

PROOF. By [$\mathbf{Ac}$, Ch. I, Thm. 2], if $F, G, H$ are valued in $\mathbf{Cat}$ then $\mathcal{S}_{F} \times^{1}_{t, \mathcal{S}_{H}, s} \mathcal{S}_{G}$ as a small category over $\mathcal{D}$ contains enough component-wise pull-backs, and it is a 1-fibre product in $\mathbf{Fib}/\mathcal{D}$, which implies by Lemma E.5.7.21 that it is a 1-fibre product in $\mathbf{Groupoids}/\mathcal{D}$. $\square$

We now assume the fixed small category $\mathcal{D}$ is endowed with the structure of a site, so stackification of categories fibered in groupoids over $\mathcal{D}$ (denoted $(\cdot)^{\mathrm{a}}$) makes sense. We refer the reader to [$\mathbf{SP}$, Tag 02ZM] for background on stacks associated to categories fibered over a site. The following Lemma asserts that if 1-fibre products exist in $\mathbf{Groupoids}/\mathcal{D}$ then they do in the strict $(2, 1)$-category of stacks in groupoids over $\mathcal{D}$ and are computed by the stack associated to the 1-fibre product of categories fibered in groupoids over $\mathcal{D}$.

## PDF page 920

**920** · **CHAPTER E. TOPOLOGICAL STACKS**

**Lemma E.5.7.25.** *Let $\mathcal{D}$ be a small category endowed with the structure of a site. Let $(A, p_A), (B, p_B), (C, p_C)$ be three small categories fibered in groupoids over $\mathcal{D}$, and $f : B \to A, g : C \to A$ two $1$-morphisms of categories fibered in groupoids over $\mathcal{D}$. If a $1$-fibre product exists for $(f, g)$ in $\mathbf{Groupoids}/\mathcal{D}$ then a $1$-fibre product of the $1$-morphisms $(f^\mathrm{a}, g^\mathrm{a})$ of stacks in groupoids over $\mathcal{D}$ exists, and it is computed by the stack associated to the category $B \times^1_{f,A,g} C$ fibered in groupoids over $\mathcal{D}$, i.e., upon calling $\mathcal{X} := B^\mathrm{a}, \mathcal{Y} := C^\mathrm{a}, \mathcal{S} := A^\mathrm{a}$, then:*

$$
\mathcal{X} \times^1_{f^\mathrm{a},\mathcal{S},g^\mathrm{a}} \mathcal{Y} = (B \times^1_{f,A,g} C)^\mathrm{a}. \tag{E.5.7.8}
$$

*Proof.* We refer the reader to [Ac, Ch.II,Thm.4] for the proof that the stackification pseudo-functor $(\cdot)^\mathrm{a} : \mathbf{Groupoids}/\mathcal{D} \to \mathbf{Stacks}/\mathcal{D}$ preserves $1$-fibre products, if they exist. $\square$

We will be applying Lemma E.5.7.24 and Lemma E.5.7.25 to show$^{21}$ that the stackification of the split fibered category $\mathcal{S}_F$ for

$$
F := \mathrm{Hom}(\cdot, (X_1, \mathcal{R}_1) \times_{(Y,\mathcal{R})} (X_2, \mathcal{R}_2))
$$

(given $(X_i, \mathcal{R}_i) \to (Y, \mathcal{R})$ in $\mathbf{CGWH}_{\alpha}$) is a $1$-fibre product $[X_1/\mathcal{R}_1] \times^1_{[Y/\mathcal{R}]} [X_2/\mathcal{R}_2]$ of (quotient) stacks in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$. The analogous result holds for the stackification of the split category fibered in groupoids induced by the $2$-fibre product of $\alpha$-small topological groupoids, which computes the $2$-fibre product of (quotient) stacks in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$.

We conclude this section by discussing an example of a situation where $1$-fibre products of stacks in groupoids over a site indeed exist not only as a category over the base site, but as a stack in groupoids.

**Lemma E.5.7.26.** *Let $A, B, C$ be three categories fibered in groupoids over a small category $\mathcal{D}$, and let $f : B \to A$ and $g : C \to A$ two $1$-morphisms. If $A$ is fibered in sets then the $1$-fibre product $B \times^1_{f,A,g} C$ as a category over $\mathcal{D}$ is fibered in groupoids and isomorphic to the $2$-fibre product $B \times^2_{f,A,g} C$.*

*Proof.* For any object $U$ of $\mathcal{D}$, the objects of $(B \times^2_{f,A,g} C)_U = B_U \times^2_{f_U,A_U,g_U} C_U$ are triples $(x, y, \phi)$ with $x \in \mathrm{Ob}(B_U)$, $y \in \mathrm{Ob}(C_U)$, and $\alpha$ an isomorphism $\alpha : f_U(x) \to g_U(y)$. Since $A$ is fibered in sets, $A_U$ is a discrete category, forcing $f_U(x) = g_U(x)$. It follows that the very construction of $2$-fibre products agrees, in this case, with that of $1$-fibre products. In particular, the functor $p$ of Lemma E.5.7.20, which is fully faithful by the Lemma, is surjective on objects, and hence an isomorphism of categories over $\mathcal{D}$. In particular, $B \times^1_{f,A,g} C$ contains enough component-wise pullbacks, and hence it is a fibered category over $\mathcal{D}$ by Lemma E.5.7.18. $\square$

**E.6. Stacks on $\mathbf{CGWH}_{\alpha,\tau}$**

We are now ready to introduce stacks over the site $\mathbf{CGWH}_{\alpha,\tau}$. We follow the definition of [SP, Tag 0026F] closely throughout.

**E.6.1. Basic concepts.** We now give a $2$-categorical generalization of Construction E.5.7.23 of split fibered categories in sets and in groupoids.

**Construction E.6.1.1.** We let $F : 2\text{-}\mathrm{Cat}(\mathbf{CGWH}_{\alpha,\tau}^{\mathrm{opp}}) \to \mathbf{Cat}$ be a (necessarily strict) pseudo-functor between $2$-categories (see Example E.5.2.7 for the construction $2\text{-}\mathrm{Cat}(\cdot)$, and Definition E.5.3.1 for the concept of a pseudo-functor between $2$-categories). We define the datum $\mathcal{S}_F$ of a class $\mathrm{Ob}(\mathcal{S}_F)$ defined as the class of all pairs $(U, x)$ with $U$ an object of $\mathbf{CGWH}_{\alpha,\tau}$, and $x$ an object of the groupoid $F(U)$. Since both the category $F(U)$ and the category $\mathbf{CGWH}_{\alpha}$ are small, the class $\mathrm{Ob}(\mathcal{S}_F)$ is, in fact, a set.

Given two pairs $(U, x)$, $(U', x')$, we define the set:

$$
\mathrm{Hom}_{\mathcal{S}_F}((U', x'), (U, x)) := \{(\phi, f) \mid \phi \in \mathrm{Hom}_{\mathbf{CGWH}_{\alpha}}(U', U), f \in \mathrm{Hom}_{F(U')}(x', F(\phi)(x))\}. \tag{E.6.1.1}
$$

$^{21}$where?

## PDF page 921

**E.6. STACKS ON CGWH$_{\alpha,\tau}$** · **921**

Composition of morphisms:

$$
\mathrm{Hom}_{\mathcal{S}_F}((U'', x''), (U', x')) \times \mathrm{Hom}_{\mathcal{S}_F}((U', x'), (U, x)) \to \mathrm{Hom}_{\mathcal{S}_F}((U'', x''), (U, x)) \tag{E.6.1.2}
$$

is defined as:

$$
((\phi, f), (\psi, g)) \rightsquigarrow (\psi, g) \circ (\phi, f) := (\psi \circ \phi, F(f)(\psi) \circ \phi). \tag{E.6.1.3}
$$

We further define the assignment:

$$
p_F : \mathcal{S}_F \to \mathbf{CGWH}_{\alpha,\tau}, \quad (U, x) \rightsquigarrow p_F(U, x) := U, \; (\phi, f) \rightsquigarrow p_F(\phi, f) := \phi \tag{E.6.1.4}
$$

**Lemma E.6.1.2.** *Let:*

$$
F : 2\text{-}\mathrm{Cat}(\mathbf{CGWH}_{\alpha,\tau}^{\mathrm{opp}}) \to \mathbf{Cat}
$$

*be a strict pseudo-functor between $2$-categories. The datum $\mathcal{S}_F$ is a small category, the assignment $p_F : \mathcal{S}_F \to \mathbf{CGWH}_{\alpha,\tau}$ is a functor, and the pair $(\mathcal{S}_F, p_F)$ is a fibered category. Moreover, if:*

(1) *$F$ factors as a functor through the inclusion pseudo-functor $\mathbf{Groupoids} \to \mathbf{Cat}$, then $(\mathcal{S}_F, p_F)$ is fibered in groupoids.*

(2) *$F$ factors as a functor through the inclusion pseudo-functor $\mathbf{Sets} \to \mathbf{Cat}$ (sending a set to the discrete category over it, then $(\mathcal{S}_F, p_F)$ is fibered in sets).*

*Proof.* A verification of the assertion on $\mathcal{S}_F$ being a category can be found in [Ac, Ch.I,$\S$1.4,p.40,41]. Since $\mathrm{Ob}(\mathcal{S}_F)$ constructed in Construction E.6.1.1 is a set by design, $\mathcal{S}_F$ is a small category. A verification of the assertion that $p_F : \mathcal{S}_F \to \mathbf{CGWH}_{\alpha,\tau}$ is a functor is a direct consequence of the definition of the composition of morphisms of $\mathcal{S}_F$ in (E.6.1.3) of Construction E.6.1.1. A verification of the assertion on $p_F : \mathcal{S}_F \to \mathbf{CGWH}_{\alpha,\tau}$ being a fibered category can be found in [Ac, Ch.I,$\S$1.4,p.41,42,43]. That $p_F$ is a fibration in discrete categories is seen by forming, for any object $U$ of $\mathbf{CGWH}_{\alpha,\tau}$, the fibre category $(\mathcal{S}_F)_U$ and observing that

$$
\mathrm{Ob}((\mathcal{S}_F)_U) = F(U)
$$

and for any two objects $x, x' \in (\mathcal{S}_F)_U$,

$$
\mathrm{Hom}_{(\mathcal{S}_F)_U}(x', x) = \mathrm{Hom}_{F(U)}(x', x)
$$

and hence $(\mathcal{S}_F)_U = F(U)$. The Lemma therefore follows from [SP, Tag 003V] and [SP, Tag 02Y2]. $\square$

**Remark E.6.1.3.** We make the following observations on the preceding lemma.

(i) In part (1), the pseudo-functor $F$ “factoring through” the inclusion pseudo-functor $\mathbf{Groupoids} \to \mathbf{Cat}$ means that $F$ is the composition of a pseudo-functor $F' : 2\text{-}\mathrm{Cat}(\mathbf{CGWH}_{\alpha,\tau}^{\mathrm{opp}}) \to \mathbf{Groupoids}$ followed by the inclusion pseudo-functor $\mathbf{Groupoids} \to \mathbf{Cat}$. Likewise, in part (2), the pseudo-functor $F$ “factoring through” the inclusion pseudo-functor $\mathbf{Sets} \to \mathbf{Cat}$ means that $F$ is the composition of a pseudo-functor $F' : 2\text{-}\mathrm{Cat}(\mathbf{CGWH}_{\alpha,\tau}^{\mathrm{opp}}) \to \mathbf{Sets}$ followed by the inclusion pseudo-functor $\mathbf{Sets} \to \mathbf{Cat}$.

(ii) The fibered category $(\mathcal{S}_F, p_F)$ constructed in Construction E.6.1.1 and Lemma E.6.1.2 is an example of a *split* fibered category. The general notion of split fibered category is rendered invariant under isomorphism of fibered categories by declaring (see [SP, Tag 02XW]) that split fibered categories are precisely those fibered categories over a fixed small category that are isomorphic in the $2$-category $\mathbf{Fib}/\mathcal{D}$ (see part (2) of Definition E.5.2.3) to a fibered category of the form $(\mathcal{S}_F, p_F)$. To assign this concept using equivalences in $\mathbf{Fib}/\mathcal{D}$ as opposed to isomorphisms would render it unimportant, insofar every fibered category is equivalent to a split one (see [SP, Tag 004A]).

A reference for background around the following definition is [GR, Def.3.4.10(i)].

**Definition E.6.1.4.** For a small category $(\mathcal{X}, p)$ fibered in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$, and for any $\alpha$-small compactly generated weakly Hausdorff space $T$, a covering sieve $F \in J_1(T)$ is called of *effective descent* if and

## PDF page 922

**922** · **CHAPTER E. TOPOLOGICAL STACKS**

only if the functor:

$$
\mathbf{Hom}(\mathcal{S}_T, \mathcal{X}) \to \mathbf{Hom}(\mathcal{S}_F, \mathcal{X})
$$

between the Hom-categories within the $2$-category of small categories fibered in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$, is an equivalence of categories.

**Remark E.6.1.5.** As in [GR, Rem.3.4.11], if $F$ is the covering sieve generated by the set of morphisms $\{T_i \to T, i \in I\}$, we have a diagram of functors:

$$
\mathbf{Hom}(\mathcal{S}_F, \mathcal{X}) \to \prod_{i \in I} \mathbf{Hom}(\mathcal{S}_{T_i}, \mathcal{X}) \rightrightarrows \prod_{(i,j) \in I \times I} \mathbf{Hom}(\mathcal{S}_{T_{ij}}, \mathcal{X}) \tag{E.6.1.5}
$$

with $T_{ij} := T_i \times_T T_j$, and with the first functor $e : \mathbf{Hom}(\mathcal{S}_F, \mathcal{X}) \to \prod_{i \in I} \mathbf{Hom}(\mathcal{S}_{T_i}, \mathcal{X})$ being induced by the morphisms of pre-sheaves of sets $h_{T_i} \to F$ and the two rightmost functors being induced by the morphisms of pre-sheaves of sets $h_{T_{ij}} \to h_{T_i}$ induced by the two projections $T_{ij} \to T_i$ and $T_{ij} \to T_j$. The above diagram is a $2$-equalizer in the $2$-category of all small categories (see [GR, Lemma 3.4.6]). The condition in Definition E.6.1.4 ensures that $\mathbf{Hom}(\mathcal{S}_F, \mathcal{X})$ is equivalent to $\mathbf{Hom}(\mathcal{S}_T, \mathcal{X})$, and it avoids any mention of $2$-equalizers by replacing a covering with the sieve it generates, and repackaging the $2$-equalizer property of (E.6.1.5) into that of Definition E.6.1.4.

We are now ready to assign the notion of stacks in groupoids on topological spaces:

**Definition E.6.1.6.** A *stack in groupoids* on $\mathbf{CGWH}_{\alpha,\tau}$ is the datum of a small category $p : \mathcal{X} \to \mathbf{CGWH}_{\alpha,\tau}$ fibered in groupoids which satisfies the following conditions:

(1) For any object $T$ of $\mathbf{CGWH}_{\alpha,\tau}$ and any two objects $x, y \in \mathcal{X}_T$, the pre-sheaf $\mathrm{Isom}(x, y)$ (see [SP, Tag 02ZB]) on the site $\mathbf{CGWH}_{\alpha,\tau}/T$ is a sheaf.

(2) For any object $T$ of $\mathbf{CGWH}_{\alpha,\tau}$, any covering sieve $F \in J_1(T)$ is of effective descent.

**Remark E.6.1.7.** The above Definition is formally the same as in [SP, Tag 026F]. The definition also agrees with [GR, Def.5.1.1] for $\varphi = p$ and $i = 2$ under the additional assumption that $p$ be a fibration in groupoids.

**E.6.2. Quotient stacks associated to $\alpha$-small topological groupoids.** We first assign a definition:

**Definition E.6.2.1.** Let $(X, \mathcal{R}, s, t, c, e, i)$ be a topological groupoid (see Definition E.4.2.3). We say that $(X, \mathcal{R}, s, t, c, e, i)$ is $\alpha$-*small* if and only if the compactly generated weakly Hausdorff spaces $X$ and $\mathcal{R}$ are $\alpha$-small (see Definition E.3.2.1(2))

We make the following:

**Construction E.6.2.2.** We define the following functor:

$$
F_{(X,\mathcal{R})} : \mathbf{CGWH}_{\alpha}^{\mathrm{opp}} \to \mathbf{Groupoids} \tag{E.6.2.1}
$$

by the assignment, for $T$ varying across arbitrary objects in $\mathbf{CGWH}_{\alpha}$:

$$
T \rightsquigarrow F_{(X,\mathcal{R})}(T) := (h_X(T), h_{\mathcal{R}}(T), h_s(T), h_t(T), h_c(T), h_e(T), h_i(T)) \tag{E.6.2.2}
$$

where for a morphism $f : X \to Y$ in $\mathbf{CGWH}_{\alpha}$, we write $h_f$ for the natural transformation of functors $h_X \to h_Y$ induced by $f$. We further define the natural transformation of functors $F_{(X,X)} \to F_{(X,\mathcal{R})}$ induced under [SP, Tag 001P] by the morphism of $\alpha$-small topological groupoids:

$$
p : \mathbf{Const}_X \to (X, \mathcal{R}, s, t, c, e, i) \tag{E.6.2.3}
$$

where $\mathbf{Const}_X = (X, X, \mathrm{id}, \mathrm{id}, \mathrm{id}, \mathrm{id}, \mathrm{id})$ is the constant groupoid on $X$ from (E.4.2.2) and $p$ is the morphism defined by $(\mathrm{id}_X, e)$.

## PDF page 923

**E.6. STACKS ON CGWH$_{\alpha,\tau}$** · **923**

**Remark E.6.2.3.** We observe that for any $\alpha$-small topological groupoid $(X, \mathcal{R}, s, t, c, e, i)$, $F_{(X,\mathcal{R})}$ from (E.6.2.1) assigned in (E.6.2.2) is a sheaf of groupoids in sets on $\mathbf{CGWH}_{\alpha,\tau}$ since both $h_X$ and $h_{\mathcal{R}}$ are sheaves of sets.

**Definition E.6.2.4.** Let $(X, \mathcal{R}, s, t, c, e, i)$ be an $\alpha$-small topological groupoid. We define:

(1) the split category fibered in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$:

$$
p_{(X,\mathcal{R})} : \mathcal{S}_{(X,\mathcal{R})} \to \mathbf{CGWH}_{\alpha,\tau}. \tag{E.6.2.4}
$$

to be the split fibered category $(\mathcal{S}_F, p_F)$ from (E.6.1.4), for $F := F_{(X,\mathcal{R})}$ from (E.6.2.1) defined in (E.6.2.2).

(2) We denote the stack associated to $p_{(X,\mathcal{R})}$ by $[X/\mathcal{R}]$, and write:

$$
p_{[X/\mathcal{R}]} : [X/\mathcal{R}] \to \mathbf{CGWH}_{\alpha,\tau}. \tag{E.6.2.5}
$$

for the canonical $1$-morphism induced by $p_{(X,\mathcal{R})}$ under stackification.

(3) Let $G$ be an $\alpha$-small compactly generated weakly Hausdorff topological group $G$, $X$ an object of $\mathbf{CGWH}_{\alpha}$, $a : G \times X \to X$ a continuous action of $G$ on $X$. We define the split category fibered in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$:

$$
p_{(X,G)} : \mathcal{S}_{(X,G)} \to \mathbf{CGWH}_{\alpha,\tau}. \tag{E.6.2.6}
$$

to be the split fibered category $(\mathcal{S}_F, p_F)$ from (E.6.1.4), for $F := F_{(X,\mathcal{R})}$ from (E.6.2.2), where $(X, \mathcal{R}, s, t, c, e, i)$ is the action groupoid associated to the action $a$ of $G$ on $X$ (see Construction E.4.2.12).

(4) Let $X$ be an $\alpha$-small compactly generated weakly Hausdorff space. We define the split category fibered in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$:

$$
p_X : \mathcal{S}_X \to \mathbf{CGWH}_{\alpha,\tau}. \tag{E.6.2.7}
$$

to be the split fibered category $(\mathcal{S}_F, p_F)$ from (E.6.1.4), for $F := F_{(X,\mathcal{R})}$ from (E.6.2.2), where $(X, \mathcal{R}, s, t, c, e, i)$ is the constant groupoid $\mathbf{Const}_X$ on $X$ (see (E.4.2.2)).

(5) Let $X$ be an $\alpha$-small compactly generated weakly Hausdorff space. We define the split category fibered in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$:

$$
p_{\underline{X}} : \underline{X} \to \mathbf{CGWH}_{\alpha,\tau}. \tag{E.6.2.8}
$$

to be the split fibered category $(\mathcal{S}_F, p_F)$ from (E.6.1.4), for $F := h_X$ from (E.6.2.2).

**Remark E.6.2.5.** For any object $X$ in $\mathbf{CGWH}_{\alpha}$, we have two ways to associate a stack in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$ to $X$.

(1) through the assignment $X \rightsquigarrow \mathcal{S}_X$ from (E.6.2.7).

(2) Through the assignment $X \rightsquigarrow \underline{X}$ from (E.6.2.8)

The two split fibered categories $\mathcal{S}_X$ and $\underline{X}$ are isomorphic as categories fibered in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$ (and hence as categories fibered in setoids by [SP, Tag 02Y1], and fibered in sets by [SP, Tag 04S8]). For any object $T$ of $\mathbf{CGWH}_{\alpha}$, the isomorphism is induced on $T$-fibre categories by the canonical isomorphism in $\mathbf{CGWH}_{\alpha}$:

$$
\mathrm{can} : \mathrm{coeq}(\mathrm{id}_X, \mathrm{id}_X : X \rightrightarrows X) \to X \tag{E.6.2.9}
$$

We further observe that since the topology on $\mathbf{CGWH}_{\alpha,\tau}$ is sub-canonical, both $\mathcal{S}_X$ and $\underline{X}$ are stacks in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$. They are therefore isomorphic as stacks in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$ (i.e. not merely equivalent) and the isomorphism is canonical.

We further observe that by [SP, Tag 04SF], there exists a functor between small categories:

$$
\mathbf{Hom}((\mathcal{S}_X, p_X), (\mathcal{S}_Y, p_Y)) \to \mathrm{Hom}(h_X, h_Y) \tag{E.6.2.10}
$$

## PDF page 924

**924** · **CHAPTER E. TOPOLOGICAL STACKS**

where $\mathbf{Hom}((\mathcal{S}_X, p_X), (\mathcal{S}_Y, p_Y))$ is the Hom-category in the $2$-category of stacks in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$, which is also the Hom-category of the $2$-category of small categories fibered in groupoids over $\mathbf{CGWH}_{\alpha}$, and where $\mathrm{Hom}(X, Y)$ is the discrete category of morphisms of sheaves of sets (equivalent to the discrete category of continuous maps $\mathrm{Hom}_{\mathbf{CGWH}_{\alpha}}(X, Y)$). The functor in (E.6.2.10) sends a $1$-morphism of categories fibered in groupoids to its $2$-isomorphism class, and $2$-morphisms to identities. It is surjective on objects and a bijection on isomorphism classes of objects.

The dependency of $\mathcal{S}_X$ and $\underline{X}$, both split fibered categories, on $X$ is as follows: for any object $X$ of $\mathbf{CGWH}_{\alpha}$, and for the homeomorphism $\mathrm{can}$ of (E.6.2.9), there exists a canonical $1$-morphism:

$$
\underline{X} \to \mathcal{S}_X \tag{E.6.2.11}
$$

determined by the natural transformation of sheaves of groupoids $\mathrm{can}$:

$$
\mathrm{can} : (\mathrm{coeq}(\mathrm{id}, \mathrm{id} : h_X \rightrightarrows h_X), \mathrm{coeq}(\mathrm{id}, \mathrm{id} : h_X \rightrightarrows h_X), \mathrm{id}, \mathrm{id}, \mathrm{id}, \mathrm{id}, \mathrm{id}) \to (h_X, h_X, \mathrm{id}, \mathrm{id}, \mathrm{id}, \mathrm{id}, \mathrm{id}) \tag{E.6.2.12}
$$

and for any other $1$-morphism as in (E.6.2.11) in the same $2$-isomorphism class, there exists a unique $2$-isomorphism relating the two; see [SP, Tag 02Y2]). In particular, the two available ways to assign a stack in groupoids over $\mathbf{CGWH}_{\alpha,\tau}$ to any object of $\mathbf{CGWH}_{\alpha,\tau}$ are un-ambiguous, up to unique $1$-isomorphism, itself unique up to unique $2$-isomorphism. We shall be using the notation $\underline{X}$ and $\mathcal{S}_X$ interchangeably.

**Definition E.6.2.6.** We define:

$$
\pi : \underline{X} \to [X/\mathcal{R}] \tag{E.6.2.13}
$$

to be the $1$-morphism of stacks in groupoids over $\mathbf{CGWH}_{\alpha}$ induced by the morphism $p$ of $\alpha$-small topological groupoids from (E.6.2.3).

**E.6.3. Inertia stack and coarse space.** Inertia stacks are designed to keep track of automorphisms of objects of a stack that lift the identity on the base in a suitable sense, depending on the situation.

The general construction for fibered categories is in [SP, Tag 04Z2], and we refer to [SP, Tag 034I,(2)] for the definition of the absolute inertia fibered category. We now recall the definition in [SP, Tag 034I,(2)], spelled out within the intended framework of this appendix.

**Definition E.6.3.1.** Let $p : \mathcal{X} \to \mathbf{CGWH}_{\alpha}$ be a stack in topological groupoids over $\mathbf{CGWH}_{\alpha,\tau}$. The *inertia stack* $\mathcal{I}_{\mathcal{X}}$ of $\mathcal{X}$ is the category $\mathcal{I}_{\mathcal{X}}$ fibered over $\mathbf{CGWH}_{\alpha}$ whose:

(1) objects are pairs $(x, f)$ with $x$ an object of $\mathcal{X}$ and $f : x \to x$ an automorphism with $p(f) = \mathrm{id}$.

(2) Morphisms $(x, f) \to (y, g)$ are given by morphisms $\phi : x \to y$ in $\mathcal{X}$ making the following diagram commute:

```latex
\begin{tikzcd}
x \arrow[r, "\phi"] \arrow[d, "f"'] & y \arrow[d, "g"] \\
x \arrow[r, "\phi"'] & y
\end{tikzcd}
```

The category $\mathcal{I}_{\mathcal{X}}$ is equipped with a functor $q : \mathcal{I}_{\mathcal{X}} \to \mathbf{CGWH}_{\alpha}$ defined on objects as $(x, f) \mapsto p(x)$.

Before discussing inertia groups, their meaning, and how they can be viewed as being classified by $\mathcal{I}_{\mathcal{X}}$, we recall the following basic result which is [SP, Tag 034H].

**Lemma E.6.3.2.** *Let $\mathcal{X}$ be a stack in topological groupoids over $\mathbf{CGWH}_{\alpha,\tau}$. Then there is an equivalence in the $(2,1)$-category of categories over $\mathbf{CGWH}_{\alpha}$:*

$$
\mathcal{I}_{\mathcal{X}} \to \mathcal{X} \times_{\Delta, (\mathcal{X} \times_{\mathbf{CGWH}_{\alpha}} \mathcal{X}), \Delta} \times\mathcal{X}
$$

*and $q : \mathcal{I}_{\mathcal{X}} \to \mathbf{CGWH}_{\alpha}$ makes $\mathcal{I}_{\mathcal{X}}$ into a fibered category.*

## PDF page 925

**E.6. STACKS ON CGWH$_{\alpha,\tau}$** · **925**

**Remark E.6.3.3.** We further recall (see [SP, Tag 042H] and [SP, Tag 04Z3]) that for a stack in topological groupoids $\mathcal{X}$, there is always a canonical $1$-morphism:

$$
\iota : \mathcal{I}_{\mathcal{X}} \to \mathcal{X}
$$

defined on objects as $(x, f) \mapsto x$ and on morphisms as $(\phi : (x, f) \to (y, g)) \mapsto \phi$, with the last $\phi : x \to y$ regarded as a morphism in $\mathcal{X}$. There moreover exists a section

$$
\varepsilon : \mathcal{X} \to \mathcal{I}_{\mathcal{X}}
$$

defined on objects as $x \mapsto (x, \mathrm{id}_x)$ and on morphisms by sending $\phi : x \to y$ to $\phi : (x, \mathrm{id}_x) \to (y, \mathrm{id}_y)$ viewed as a morphism in $\mathcal{I}_{\mathcal{X}}$.

**Terminology E.6.3.1.** For a stack $\mathcal{X}$ in topological groupoids, we say the inertia stack is *trivial* if the canonical $1$-morphism:

$$
\iota : \mathcal{I}_{\mathcal{X}} \to \mathcal{X}
$$

is an equivalence. We shall see how this means that all the inertia groups of $\mathcal{X}$ at all points of $\mathcal{X}$ are trivial.

We will only ever be interested in the inertia stacks and groups of quotient stacks in topological groupoids. We therefore describe the inertia stack of such a stack in topological groupoids here below. First, a definition.

**Definition E.6.3.4.** Let $(X, \mathcal{G}, s, t, c, e, i)$ be a topological groupoid. Its *inertia group* $I_{[\mathcal{G} \rightrightarrows X]}$ is defined as the fibre product in $\mathbf{CGWH}_{\alpha}$:

$$
I_{[\mathcal{G} \rightrightarrows X]} := X \times_{\Delta, X \times X, (s,t)} \mathcal{G}.
$$

This is made into a relative topological group over $X$ by the continuous multiplication law over $X$ induced by the composition law $c$ on $[\mathcal{G} \rightrightarrows X]$.

**Lemma E.6.3.5.** *Let $(X, \mathcal{G}, s, t, c, e, i)$ be a topological groupoid. Then $I_{[\mathcal{G} \rightrightarrows X]}$ is closed in $\mathcal{G}$ with respect to the topology induced by the second projection:*

$$
I_{[\mathcal{G} \rightrightarrows X]} = X \times_{\Delta, X \times X, (s,t)} \mathcal{G} \to \mathcal{G}.
$$

*Moreover, if $X$ is Hausdorff then $I_{[\mathcal{G} \rightrightarrows X]}$ can be computed in $\mathbf{Spaces}$.*

*Proof.* Set-theoretically, $I_{[\mathcal{G} \rightrightarrows X]}$ is the union $\bigcup_{x \in X} I_x$, and so $I_{[\mathcal{G} \rightrightarrows X]}$ is the set-theoretic equalizer of $s, t$. It is also the topological equalizer, since the forgetful functor $\mathbf{CGWH}_{\alpha} \to \mathbf{Sets}$ is faithful and commutes with small limits. Thus $I_{[\mathcal{G} \rightrightarrows X]}$ is closed in $\mathcal{G}$ by Lemma E.2.3.9 as long as $\Delta : X \to X \times X$ is a closed immersion in $\mathbf{Spaces}$, which it is by Lemma E.2.1.6 since all objects in $\mathbf{CGWH}_{\alpha}$ are weakly Hausdorff. If $X$ is Hausdorff then by Lemma E.2.3.1 $I_{[\mathcal{G} \rightrightarrows X]}$ can be computed in $\mathbf{Spaces}$ because $X \times X$ can, and $X \times_{\Delta, X \times X, (s,t)} \mathcal{G}$ is a fibre product in $\mathbf{Spaces}$ by Lemma E.2.3.9. $\square$

We have the following description of the inertia stack of the quotient stack $[X/\mathcal{G}]$ in terms of the chart $\mathcal{G} \rightrightarrows X$ for $[X/\mathcal{G}]$:

**Lemma E.6.3.6.** *Let $(X, \mathcal{G}, s, t, c, e, i)$ be a topological groupoid. We set $\mathcal{G}' := \mathcal{G} \times_{s, X} I_{[\mathcal{G} \rightrightarrows X]}$, and further define:*

(1) $s' : \mathcal{G}' \to I_{[\mathcal{G} \rightrightarrows X]}$, *by $s'(r, g) := g$.*

(2) $t' : \mathcal{G}' \to I_{[\mathcal{G} \rightrightarrows X]}$, *by $t'(r, g) := c(r, c(g, i(r)))$.*

(3) $c' : \mathcal{G}' \times_{s', I_{[\mathcal{G} \rightrightarrows X]}, t'} \mathcal{G}' \to \mathcal{G}'$, *by $c'((r, g), (r', g')) := (c(r, r'), g)$.*

*Then $(I_{[\mathcal{G} \rightrightarrows X]}, \mathcal{G}', s', t', c')$ together with the uniquely determined unit section $e'$ and inverse map $i'$, is a topological groupoid. Moreover, we have a canonical equivalence of stacks in topological groupoids:*

$$
\mathcal{I}_{[X/\mathcal{G}]} = [I_{[\mathcal{G} \rightrightarrows X]}/\mathcal{G}'].
$$

## PDF page 926

**926** · **CHAPTER E. TOPOLOGICAL STACKS**

*Proof.* The proof proceeds in a manner that is identical to the case of groupoids in schemes, and we record it here to provide more details and to remind the reader of the construction of the morphism:

$$
\mathcal{I}_{[X/\mathcal{G}]_{\mathrm{prestack}}} \to [I_{[\mathcal{G} \rightrightarrows X]}/\mathcal{G}']_{\mathrm{prestack}}.
$$

We refer the reader to [SP, Tag 06PB] for the direct analog for groupoids in schemes. By [SP, Tag 06NS], it is enough to prove this on the level of pre-stacks.

We need to show that there is an equivalence of fibered categories:

$$
\mathcal{I}_{[X/\mathcal{G}]_{\mathrm{prestack}}} \to [I_{[\mathcal{G} \rightrightarrows X]}/\mathcal{G}']_{\mathrm{prestack}}.
$$

For $T$ in $\mathbf{CGWH}_{\alpha}$, a $T$-object in the inertia fibred category $\mathcal{I}_{[X/\mathcal{G}]_{\mathrm{prestack}}}$ is the datum of an object $x$ in the fibre category over $T$ and an automorphism $g$ of $x$. We may interpret $x$ as a morphism $x : T \to X$, and $g$ as a morphism $g : T \to \mathcal{G}$, such that $s \circ g = t \circ g = x$. This means that $g$ factors through $I_{[\mathcal{G} \rightrightarrows X]}$. A morphism in the inertia fibred category $(x, g) \to (y, h)$ over the space $T$ is the datum of a morphism $r : T \to \mathcal{G}$ such that $s \circ r = x$ and $t \circ r = y$, and the diagram:

```latex
\begin{tikzcd}
x \arrow[r, "r"] \arrow[d, "g"'] & y \arrow[d, "h"] \\
x \arrow[r, "r"'] & y
\end{tikzcd}
```

commutes. This is by [SP, Tag 034H], and means the identity:

$$
c(r, g) = c(h, r)
$$

using the composition law $c$. Incorporating the effect of the inverse map $i$, we can also write:

$$
c(c(r, g), i \circ r) = c(r, c(g, i \circ r))
$$

which means “$r \circ (g \circ r^{-1}) = h$” and “$(r \circ g) \circ r^{-1} = h$”, respectively. Once again this gives a unique element of $\mathcal{G}'$ acting as a morphism between objects, i.e. elements in $I_{[\mathcal{G} \rightrightarrows X]}$. Not only this constructs a morphism of fibred categories $\mathcal{I}_{[X/\mathcal{G}]_{\mathrm{prestack}}} \to [I_{[\mathcal{G} \rightrightarrows X]}/\mathcal{G}']_{\mathrm{prestack}}$, but it proves it is both fully faithful and essentially surjective. $\square$

We have the following simple criterion for the triviality of the inertia stack of the quotient stack associated to a topological groupoid:

**Lemma E.6.3.7.** *Let $(X, \mathcal{G}, s, t, c, e, i)$ be a topological groupoid. Assume $(s, t) : \mathcal{G} \to X \times X$ is injective. Then the canonical $1$-morphism:*

$$
\iota : \mathcal{I}_{[X/\mathcal{G}]} \to [X/\mathcal{G}]
$$

*is an equivalence.*

*Proof.* The section $\varepsilon$ to $\iota$ discussed in Remark E.6.3.3 shows that the functor

$$
\mathcal{I}_{[X/\mathcal{G}]} \to [X/\mathcal{G}]
$$

is essentially surjective. If $(s, t) : \mathcal{G} \to X \times X$ is injective then the morphism $I_{[\mathcal{G} \rightrightarrows X]} \to X$ given by the first projection in the construction of $I_{[\mathcal{G} \rightrightarrows X]}$ $^{22}$ is also injective, hence surjective by the existence of a section to $\iota$. This forces $\iota$ to be faithful. Moreover, it also forces $\mathcal{G}' \to \mathcal{G}$ to be an isomorphism, and therefore $\iota$ is fully faithful, hence an equivalence. $\square$

We further have the following representability criterion:$^{23}$

$^{22}$Clarify here with a reference

$^{23}$There seems to be no actual discussion of coarse spaces anywhere here, complementing this result, yet coarse spaces are the entire purpose of all of this effort. Must address it.

## PDF page 927

**E.6. STACKS ON CGWH$_{\alpha,\tau}$** · **927**

**Proposition E.6.3.8.** *Let $[\mathcal{G} \rightrightarrows X]$ be a topological groupoid. Assume:*

(1) *$(s, t) : \mathcal{G} \to X \times X$ is a closed immersion,*

(2) *the continuous map $X \to X/\mathcal{G}$ is a quotient map.*

*Then $[X/\mathcal{G}]$ is representable, and the representing object of $\mathbf{CGWH}_{\alpha}$ is the quotient topological space $X/\mathcal{G}$. Equivalently, there is a canonical equivalence:*

$$
[X/\mathcal{G}] \simeq \underline{X/\mathcal{G}}.
$$

The condition on the map $X \to X/\mathcal{G}$ being a quotient map is typically easy to arrange. The usual obstruction to representability is the discrepancy between the intrinsic topology on $\mathcal{G}$ and the induced topology on $\mathcal{G}$ from $X \times X$, with the latter product being in $\mathbf{Spaces}$. If $X$ is Hausdorff this is indeed the case. More generally, this can fail and then one can get a quotient stack in topological groupoids which is not representable despite having trivial inertia stack.

*Proof of Proposition E.6.3.8.* Under the assumptions of the Proposition, $X/\mathcal{G}$ is compactly generated and weakly Hausdorff. By Lemma E.6.3.7, the inertia stack of $[X/\mathcal{G}]$ is trivial. This implies that not only $X/\mathcal{G}$ is an object of $\mathbf{CGWH}_{\alpha}$ (it is $\alpha$-small since $X$ is), but that the morphism $[X/\mathcal{G}] \to X/\mathcal{G}$ is representable, and so $[X/\mathcal{G}]$ is itself representable. Let $T$ be the representing object. By Yoneda’s Lemma, the morphism $[X/\mathcal{G}] \to X/\mathcal{G}$ is therefore induced by a unique continuous map $T \to X/\mathcal{G}$. Moreover, the morphism $X \to [X/\mathcal{G}]$ is always representable by quotient maps, which forces $X \to T$ to be itself a quotient map. One checks, by assumption (1) and Lemma E.6.3.7, that the induced equivalence relation $R := X \times_T X$ on $X$ yields a trivial inertia stack $\mathcal{I}_{[R \rightrightarrows X]}$, which forces the map $R \to \mathcal{G}$ to be surjective. By the final assertion in Lemma E.2.3.5, the map $R \to \mathcal{G}$ is therefore a closed immersion and hence a homeomorphism, and $T$ receives a homeomorphic quotient map from $X/\mathcal{G}$ which is a section to the map $T \to X/\mathcal{G}$, so the Proposition is proved. $\square$

We now recall foundational material about inertia groups, highlighting how to view them as fibers of the morphism $\iota : \mathcal{I}_{\mathcal{X}} \to \mathcal{X}$.

**Lemma E.6.3.9.** *Let $(X, \mathcal{G}, s, t, c, e, i)$ be a topological groupoid. For a point $x \in X$, let $I_x = \{y \in \mathcal{G} : s(y) = x = t(y)\}$. Then $I_x$ equipped with the topology induced by $\mathcal{G}$ is a topological group.*

*Proof.* A quick way to see this is by observing that the first projection $I_{[\mathcal{G} \rightrightarrows X]} \to X$ makes $I_{[\mathcal{G} \rightrightarrows X]}$ into a relative topological group over $X$, whose multiplication $X$-morphism is induced by the composition law on $\mathcal{G}$ of $[\mathcal{G} \rightrightarrows X]$. The fiber of $I_{[\mathcal{G} \rightrightarrows X]} \to X$ over $x$ is exactly $I_x$ with the induced topology from the topology on $\mathcal{G}$. $\square$

**Lemma E.6.3.10.** *Let $(X, G, s, t, c, e, i)$ be a locally compact Hausdorff topological group. Then all the topological groups $I_x$ are locally compact Hausdorff.*

*Proof.* Closed subspaces of locally compact Hausdorff topological spaces are locally compact Hausdorff, and $I_x$ is closed in $\mathcal{G}$ since $x \in X$ is closed (as $X$ is weakly Hausdorff). $\square$

For $x : T \to \mathcal{X}$, define a sheaf $\mathcal{I}_{x:\underline{T} \to \mathcal{X}}$ of groups on $\mathbf{CGWH}_{\alpha,\tau}$ whose sections interpolate the topological groups $I_y$. For any object $T'$ of $\mathbf{CGWH}_{\alpha}$, let

$$
\mathcal{I}_{x:\underline{T} \to \mathcal{X}}(T')
$$

denote the set of pairs $(f, \phi)$ with $f : T' \to T$ a morphism and $\phi$ an automorphism of $f^*(x)$ as an object of $\mathcal{X}(T')$. The map

$$
\mathcal{I}_{x:\underline{T} \to \mathcal{X}} \to h_T
$$

sending a $T'$-section $(f, \phi)$ to $f \in h_T(T')$ makes $\mathcal{I}_{x:\underline{T} \to \mathcal{X}}$ into a sheaf of groups over $T$.

For the canonical map $x : \underline{X} \to \mathcal{X} := [X/\mathcal{G}]$, $\mathcal{I}_{x:\underline{X} \to \mathcal{X}}$ is nothing but $I_{[\mathcal{G} \rightrightarrows X]}$ from Definition E.6.3.4, with its own map to $X$.

## PDF page 928

**928** · **CHAPTER E. TOPOLOGICAL STACKS**

**Notation E.6.3.1.** We often abbreviate $\mathcal{I}_{x:\underline{T} \to \mathcal{X}}$ as $\mathcal{I}_x$ when no confusion is expected to arise.

**Lemma E.6.3.11.** *Let $(X, \mathcal{G}, s, t, c, e, i)$ be a topological groupoid and $\mathcal{X} = [X/\mathcal{G}]$ its quotient stack. Let $T$ be an object of $\mathbf{CGWH}_{\alpha}$. Then for any $T$-point $x : \underline{T} \to \mathcal{X}$ of $\mathcal{X}$, we have a cartesian diagram:*

```latex
\begin{tikzcd}
\mathcal{I}_{x:\underline{T} \to \mathcal{X}} \arrow[r] \arrow[d] & \mathcal{I}_{\mathcal{X}} \arrow[d, "\iota"] \\
\underline{T} \arrow[r, "x"'] & \mathcal{X}
\end{tikzcd}
```

*Proof.* We let $T' \to T$ be a morphism of spaces, and consider the induced diagram of maps of topological groupoids

(E.6.3.1)

```latex
\begin{tikzcd}
\mathcal{I}_{x:\underline{T} \to \mathcal{X}}(T') \arrow[r] \arrow[d] & \mathcal{I}_{\mathcal{X}}(T') \arrow[d, "\iota"] \\
h_{T}(T') \arrow[r, "x"'] & \mathcal{X}(T')
\end{tikzcd}
```

where $\mathcal{X}(T')$ is short-hand notation for the topological groupoid of morphisms $\underline{T'} \to \mathcal{X}$ and the maps in (E.6.3.1) are defined as follows. The bottom horizontal map is the map sending $f \in h_T(T')$ to the composition $f^*x = x \circ f : \underline{T'} \to \underline{T} \to \mathcal{X}$, an object of the groupoid $\mathcal{X}(T')$. The left vertical map is $(f, \phi) \mapsto f$, and the top horizontal map is

$$
(f, \phi) \mapsto ((f^*(x), f^*(x)), \phi) \in (\mathcal{X} \times_{\Delta, \mathcal{X} \times \mathcal{X}, \Delta} \mathcal{X})(T').
$$

The right vertical map $\iota$ sends an element $(a, \phi)$ of $\mathcal{I}_{\mathcal{X}}(T')$ (with $a \in X(T')$ and $\phi \in \mathcal{G}(T')$ an automorphism of $a$ such that $\Delta_{X}(a) = (s, t)(\phi)$ in $X \times X$) to $a \in X(T')$ viewed as an object of $\mathcal{X}(T')$.

We have:

$$
\mathcal{X}(T') = [\mathcal{G}(T') \rightrightarrows X(T')], \; \mathcal{I}_{\mathcal{X}}(T') = [\mathcal{G}' \rightrightarrows I_{[\mathcal{G}(T') \rightrightarrows X(T')]}]
$$

where $\mathcal{G}'$ refers to the notation from Lemma E.6.3.6. The groupoid-theoretic fibre product thereby recovers the description of $\mathcal{I}_{x:\overline{T} \to \mathcal{X}}(T')$ as in the construction of $\mathcal{I}_{x:\overline{T} \to \mathcal{X}}$. $\square$

**Remark E.6.3.12.** In the special case $T = X$ and $x$ is the quotient $\underline{X} \to [X/\mathcal{G}]$, $\mathcal{I}_{x:\underline{T} \to \mathcal{X}} = I_{[\mathcal{G} \rightrightarrows X]}$ and for any point $y \in X$ the induced morphism $y : \underline{\{y\}} \to \underline{X} \to \mathcal{X}$ fits into the assertion of the Lemma with $T = \{y\}$ and gives:

$$
\mathcal{I}_{y:\underline{\{y\}} \to \mathcal{X}} = \underline{\{y\}} \times_{y, \mathcal{X}, \iota} \mathcal{I}_{\mathcal{X}} = \{y\} \times_{y, X} I_{[\mathcal{G} \rightrightarrows X]} = I_y.
$$

In other words, the inertia stack interpolates the inertia groups of all points of $X$.

**E.6.4. Equivalences.** In this subsection we focus on stacks in topological groupoids that are equipped with a chart, introduce related some concepts and establish some consistency checks.

We have associated a stack in topological groupoids to a topological groupoid in a functorial manner. We will now compare the two notions to study how far this functorial assignment is from being fully faithful.

**Lemma E.6.4.1.** *Let $(X, \mathcal{G}, s, t, c, e, i)$ and $(X', \mathcal{G}', s', t', c', e', i')$ be two topological groupoids, and:*

$$
f : [\mathcal{G} \rightrightarrows X] \to [\mathcal{G}' \rightrightarrows X']
$$

*a morphism of topological groupoids. We write $f = (f_1, f_2)$ to denote the map $f_1 : X \to X'$ on Ob-sets and the map $f_2 : \mathcal{G} \to \mathcal{G}'$ on Mor-sets. Let $f$ also denote the induced morphism:*

$$
f : [X/\mathcal{G}] \to [X'/\mathcal{G}']
$$

*of quotient stacks. The following are equivalent:*

(1) *$f$ is fully faithful.*

## PDF page 929

**E.6. STACKS ON CGWH$_{\alpha,\tau}$** · **929**

(2) *The natural map:*

$$
\mathcal{G} \to (X \times X) \times_{X' \times X'} \mathcal{G}'
$$

*is an isomorphism.*

*Proof.* The argument is identical to that in the proof of [SP, Tag 046S], noting that one has to use the topology on $\mathbf{CGWH}_{\alpha,\tau}$ to work locally and pick local sections, and that the analog of [SP, Tag 044V] still holds for topological groupoids and their quotient stacks, with an identical proof. $\square$

**Lemma E.6.4.2.** *Let $(X, \mathcal{G}, s, t, c, e, i)$ and $(X', \mathcal{G}', s', t', c', e', i')$ be two topological groupoids, and:*

$$
f : [\mathcal{G} \rightrightarrows X] \to [\mathcal{G}' \rightrightarrows X']
$$

*a morphism of topological groupoids. We write $f = (f_1, f_2)$ to denote the map $f_1 : X \to X'$ on Ob-sets and the map $f_2 : \mathcal{G} \to \mathcal{G}'$ on Mor-sets. Let $f$ also denote the induced morphism:*

$$
f : [X/\mathcal{G}] \to [X'/\mathcal{G}']
$$

*of quotient stacks. The following are equivalent:*

(1) *$f$ is an equivalence.*

(2) *$f$ satisfies the following two conditions:*

(a) *the natural map*

$$
\mathcal{G} \to (X \times X) \times_{X' \times X'} \mathcal{G}'
$$

*is an isomorphism,*

(b) *the composition*

$$
X \times_{f_1, X', t'} \mathcal{G} \xrightarrow{\mathrm{pr}_2} \mathcal{G}' \xrightarrow{s'} X'
$$

*is a submersion.*

*Proof.* Just as for the analog of the result for groupoids on algebraic spaces (see [SP, Tag 046T]), one uses [SP, Tag 046N] which characterizes equivalences between stacks on a site. The argument to check that the assumptions of [SP, Tag 046N] are satisfied, using full faithfulness of $f$ which is a consequence of Lemma E.6.4.1, is identical to the argument in [SP, Tag 046T] upon replacing all objects in the site with objects in $\mathbf{CGWH}_{\alpha}$ and replacing the fppf topology on algebraic spaces with the topology on $\mathbf{CGWH}_{\alpha,\tau}$. $\square$

**Definition E.6.4.3.** Let $(X, \mathcal{G}, s, t, c, e, i)$ and $(X', \mathcal{G}', s', t', c', e', i')$ be two topological groupoids, and:

$$
f : [\mathcal{G} \rightrightarrows X] \to [\mathcal{G}' \rightrightarrows X']
$$

a morphism of topological groupoids. We write $f = (f_1, f_2)$ to denote the map $f_1 : X \to X'$ on Ob-sets and the map $f_2 : \mathcal{G} \to \mathcal{G}'$ on Mor-sets. Let $f$ also denote the induced morphism:

$$
f : [X/\mathcal{G}] \to [X'/\mathcal{G}']
$$

of quotient stacks. We say $f$ is a *standard Morita equivalence* if and only if:

(1) $f_1 : X \to X'$ is a submersion,

(2) the induced map $\mathcal{G}' \to (X \times X) \times_{(f_1, f_1), X' \times X', (s', t')} \mathcal{G}'$ is an isomorphism.

We have the following:

**Lemma E.6.4.4.** *Suppose $(X, \mathcal{G}, s, t, c, e, i)$ and $(X', \mathcal{G}', s', t', c', e', i')$ are two topological groupoids, and:*

$$
f : [\mathcal{G} \rightrightarrows X] \to [\mathcal{G}' \rightrightarrows X']
$$

*is a morphism of topological groupoids. If $f$ is a standard Morita equivalence then the induced morphism of quotient stacks:*

$$
f : [X/\mathcal{G}] \to [X'/\mathcal{G}']
$$

## PDF page 930

**930** · **CHAPTER E. TOPOLOGICAL STACKS**

*is an equivalence.*

*Proof.* Indeed, submersiveness of $f_1$ implies submersiveness of $X \times_{f_1, X', t'} \mathcal{G}' \to \mathcal{G}'$ (by Lemma E.2.3.6(6)), and since $\mathcal{G}' \to X'$ is submersive (as it has a continuous section) we get the result by Lemma E.6.4.2. $\square$

A partial converse holds:

**Lemma E.6.4.5.** *Suppose $(X, \mathcal{G}, s, t, c, e, i)$ and $(X', \mathcal{G}', s', t', c', e', i')$ are two topological groupoids, and*

$$
f : [\mathcal{G} \rightrightarrows X] \to [\mathcal{G}' \rightrightarrows X']
$$

*is a morphism of topological groupoids. Suppose that the induced morphism between quotient stacks*

$$
f : [X/\mathcal{G}] \to [X'/\mathcal{G}']
$$

*is an equivalence. Then there exists a topological groupoid $(X'', \mathcal{G}'', s'', t'', c'', e'', i'')$ and morphisms of topological groupoids*

$$
g : [\mathcal{G}'' \rightrightarrows X''] \to [\mathcal{G} \rightrightarrows X], \; h : [\mathcal{G}'' \rightrightarrows X''] \to [\mathcal{G}' \rightrightarrows X']
$$

*such that $g$ and $h$ are standard Morita equivalences, and $f \circ g = h$.*

Not all equivalences of quotient stacks are induced by a morphism of topological groupoids. However, they are up to standard Morita equivalence.

**Lemma E.6.4.6.** *Suppose $(X, \mathcal{G}, s, t, c, e, i)$ and $(X', \mathcal{G}', s', t', c', e', i')$ are two topological groupoids, and we are given a morphism between quotient stacks*

$$
f : [X/\mathcal{G}] \to [X'/\mathcal{G}'].
$$

*Then there exists a topological groupoid $(X'', \mathcal{G}'', s'', t'', c'', e'', i'')$, a standard Morita equivalence*

$$
g : [\mathcal{G}'' \rightrightarrows X''] \to [\mathcal{G} \rightrightarrows X]
$$

*and a morphism of topological groupoids*

$$
h : [\mathcal{G}'' \rightrightarrows X''] \to [\mathcal{G}' \rightrightarrows X']
$$

*such that $f \circ g = h$.*

*Proof.* The idea is to form the $2$-fiber product:

```latex
\begin{tikzcd}
\mathcal{X} := [X/\mathcal{G}]\times_{[X'/\mathcal{G}']}\underline{X}' \arrow[r] \arrow[d] & \underline{X}' \arrow[d] \\
{[X/\mathcal{G}]} \arrow[r] & {[X'/\mathcal{G}']}
\end{tikzcd}
```

and observe that there exists an induced epimorphism:

$$
\underline{X} \times_{[X/\mathcal{G}]} \underline{X}' \to \mathcal{X}
$$

with $\underline{X} \times_{[X/\mathcal{G}]} \underline{X}'$ representable. Let $X''$ be the representing object, so there are evident maps $X'' \rightrightarrows X, X'$. Then one checks that upon calling $\mathcal{G}'' := \underline{X}'' \times_{[X/\mathcal{G}]} \underline{X}''$, and upon defining the structure maps to make a topological groupoid $[\mathcal{G}'' \rightrightarrows X'']$ accordingly, the resulting morphism of topological groupoids $g : [\mathcal{G}'' \rightrightarrows X''] \to [\mathcal{G} \rightrightarrows X]$ (using $\mathcal{G}'' \to X \times_{[X/\mathcal{G}]} X = \mathcal{G}$) is a standard Morita equivalence. One then uses $\mathcal{G}' \to X' \times_{[X'/\mathcal{G}']} X' = \mathcal{G}'$ (resting on $f : [X/\mathcal{G}] \to [X'/\mathcal{G}']$) to define

$$
h : [\mathcal{G}'' \rightrightarrows X''] \to [\mathcal{G}' \rightrightarrows X'],
$$

and this works. $\square$

## PDF page 931

E.6.  STACKS ON CGWHα,τ                                              931

Remark E.6.4.7. Standard Morita equivalences in $\mathbf{CGWH}_{\alpha,\tau}$-$\mathbf{Grpd}$ satisfy the right-Ore conditions. The localization of the category of topological groupoids at the class of standard Morita equivalences is equivalent, as a 2-category, to the 2-category of stacks in topological groupoids $\mathcal{X} \to \mathbf{CGWH}_{\alpha,\tau}$ equipped with a representable epimorphism $\underline{X} \to \mathcal{X}$ from an object of $\mathbf{CGWH}_{\alpha}$.

Example E.6.4.8. For $X$ in $\mathbf{CGWH}_{\alpha}$ equipped with a continuous action by a locally compact Hausdorff topological group $G$ and a closed subgroup $H \subset G$ whose action on $X$ is free,$^{24}$ the topological quotient $X/H$ belongs$^{25}$ to $\mathbf{CGWH}_{\alpha}$ and is equipped with an evident continuous action by the topological group $G/H$. We then have$^{26}$

$$[X/G] = [(X/H)/(G/H)].$$

For a number field $F$, a finite set $S$ of places of $F$ containing the Archimedean places, and a finite place $v_{0} \in S$, we apply this to $X = \{0\} \times \prod_{v \in S-\{v_{0}\}} F_{v}^{\times}$, $G = \left(\prod_{v \in S} F_{v}^{\times}\right)^{1}$, and $H = \left(\prod_{v \in S-\{v_{0}\}} F_{v}^{\times}\right)^{1}$. Since $X/H \simeq \mathbf{R}_{>0}$ (via $|\cdot|_{F,S}$) and $G/H = \mathcal{O}^{\times}_{F_{v_{0}}}$ (with trivial action on $X/H$), we get $[X/G] = [\mathbf{R}_{>0}/\mathcal{O}^{\times}_{F_{v_{0}}}]$.$^{27}$

$^{24}$do we need more precision than set-theoretic freeness?
$^{25}$give reference
$^{26}$explain, including with references
$^{27}$This should be expanded, including the groups without norm-1 condition to make the contact with $\mathbf{R}_{>0}/q_{v_0}^{\mathbf{Z}}$ as the coarse space for a specific quotient stack. It also has to be explained how exactly this relates to the preceding discussion, or put it elsewhere.

## PDF page 932
