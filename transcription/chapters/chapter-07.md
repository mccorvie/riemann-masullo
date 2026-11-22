## PDF page 311

**CHAPTER 7** · **Schauder Bases of Idelic Zeta functions**

**7.1.** Polar Multiplicities 312

**7.1.1.** Almost periodic functions 312

**7.1.2.** Asymptotic expansion of $\Phi_{F,S}(f)(g)$ as $|g|_{F,S}\to 0^+$ 315

**7.1.3.** Polar Multiplicities 323

**7.1.4.** Spectral bi-orthogonal sequences 326

**7.2.** Poles of the $S$-idelic Zeta functions 332

**7.2.1.** Principal parts 332

**7.2.2.** Local poles and global zeros 338

**7.3.** Paley-Wiener Levels and Schauder Bases of Principal Parts 340

**7.3.1.** Orbital Schauder Bases 340

**7.3.2.** Paley-Wiener Levels 350

**7.3.3.** Orbital Schauder Bases on the Paley-Wiener Levels 357

**7.3.4.** Poles of the $\Gamma$-factors 364

**7.4.** Nuclearity 366

**7.4.1.** Spectral Nuclearity 366

**7.4.2.** Orbital Nuclearity - non-Archimedean places 367

**7.4.3.** Orbital Nuclearity - Archimedean places 367

**7.5.** Strong Co-Primality 374

In this Chapter we construct Schauder bases on certain important subquotients of the separable nuclear Fréchet spaces:

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S})),\quad \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}(\mathbf{A}_F))
$$

with $F$ a number field, $\chi$ a continuous character of $J_{F,S}$, respectively $C_F$.

The constructions are made in the $S$-local case, and then propagated globally using the slow growth of the reciprocal of the Hecke $L$-function $L_f(s,\chi)$ on the 1-line, and classical zero-free regions.

For the purposes of applications, the $S$-local Schauder bases will be the main instrument in use in later Chapters.

We recall from [Jar, Part II,Ch.14,§14.2,p.292] that for $E$ a Hausdorff locally convex topological $\mathbf{C}$-vector space, $\{x_m\}_{m\ge 0}\subset E$ is a Schauder basis if and only if:

(1) For every $u\in E$, there exists a unique sequence $\{c_m(u)\}_{m\ge 0}\subset\mathbf{C}$ of complex numbers such that

$$
u = \sum_{m\ge 0} c_m(u)x_m
$$

the convergence of the sum being in $E$.

(2) Formation of each $c_m$ is continuous on $E$.

Condition (1) identifies the concept of topological basis (see [Jar, Part II,Ch.14,§14.2,p.292]) while the datum $\{(x_m, f_m)\}_{m\ge 0}$ with $\{x_m\}_{m\ge 0}\subset E$, and $\{f_m\}_{m\ge 0}\subset E'$, such that the linear span of the $x_m$'s is dense

**311**

## PDF page 312

**312** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

in $E$, and the linear span of the $f_m$'s separates the points of $E$ (equivalently, is weakly dense in $E'$) is termed a Markushevich basis; see [Jar, Part II,Ch.14,§14.1,p.289].

For $\{x_m\}_{m\ge 0}\subset E$ a Schauder basis, upon denoting $f_m := c_m$, then $\{(x_m, f_m)\}_{m\ge 0}$ is a Markushevich basis for the duality $\langle E, E'\rangle$ (see [Jar, Part II,Ch.14,§14.2,Prop.1,p.292]).

Hausdorff locally convex topological $\mathbf{C}$-vector spaces with a Schauder basis satisfy several additional properties. We refer the reader to [Jar, Part II,Ch.14] for more on Schauder bases, unconditional and absolute bases, and to [Kal] for more on properties of Hausdorff locally convex topological vector spaces in the presence of Schauder basic sequences within their closed subspaces, as well as some terminology.

We recall from [Kal, §3,p.95] that a Schauder basis $\{b_k\}_{k\ge 0}$ in a Hausdorff locally convex topological $\mathbf{C}$-vector space $E$ is simple if and only if the finite rank projection operators $P_N := \sum_{0\le k\le N}\langle\varphi_k,\cdot\rangle_{E',E}b_k$, for $\{\varphi_k\}_{k\ge 0}$ the dual basic sequence of $\{b_k\}_{k\ge 0}$, are a bounded set in $\mathscr{L}_\beta(E)$, i.e. they are strongly bounded.

We further recall from [Kal, §1,Def.1.1,p.91] that a Schauder basis $\{b_k\}_{k\ge 0}$ of $E$ is regular if and only if there exists a 0-neighborhood $V$ such that $b_k\not\in V$ for all $k\ge 0$.

Finally, from [Kal, §1,Def.1.2], a Schauder basis is normalized if and only if it is bounded and regular.

The example to keep in mind is that of $E = \mathcal{S}(\mathbf{T})$, for $\mathbf{T}$ the circle group $\mathbf{R}/\mathbf{Z}$, with $x_m = e^{2\pi i m x}$, as a function of $x\in\mathbf{R}$ descended to $\mathbf{R}$ by 1-periodicity, for each $m\in\mathbf{Z}$, and with $f_m$ the $m$th Fourier coefficient functional. Then $\{x_m\}_{m\in\mathbf{Z}}$ is an absolute Schauder basis for $E$, and its dual basis $\{f_m\}_{m\in\mathbf{Z}}$ is an unconditional Schauder basis for $E'_\beta$ (see Lemma 4.2.1.2, with $\gamma = e$, below, noting that the exponential isomorphism $x\mapsto e^x$ induces a linear topological isomorphism $\mathcal{S}(\mathbf{T})\simeq\mathcal{S}(\mathbf{R}_{>0}/e^{\mathbf{Z}})$).

**7.1. Polar Multiplicities**

In this section we discuss the poles of the $S$-idelic Zeta functions.

This will serve the two-fold purpose of later selecting the Sobolev degree that suffices for a Sobolev space of the global idele class group to serve as ambient for the Trace Formula which is the main subject of study of this work, and it will serve the purpose, at the end of this Chapter, of discussing the existence of periodic orbits and fixed loci of the action of $C_F$ on certain sub-loci of the global adeles.

This section will enable us to sharpen the analogy between our trace formula, and Selberg's Trace Formula (see [Iwaniec, Ch.10], by appealing to a paper of P. Sarnak on the uniform distribution of long horocycles on the space of elements of a Riemann surface, equipped with the Poincaré metric, for which we refer the reader to [Sarnak, §0,Thm.1,p.719].

**7.1.1. Almost periodic functions.** Pioneering work of Harald Bohr from [Bohr1, Bohr2, Bohr3] investigated self-approximation conditions on a large class of functions directly related to Dirichlet series: “almost periodic” functions (we do not review its definition since the present discussion is purely for motivation; what we will really need is “strongly recurrent” (Definition B.5.3.1). These are functions that are holomorphic on a vertical strip $\mathbf{C}_I$ of bounded width of the complex $s$-plane, and, while not necessarily periodic, recur enough often over $\mathbf{C}_I$ to allow the study of their distribution of values. Examples of almost periodic functions are finite sums and finite products of vertically periodic functions with different, possibly $\mathbf{Q}$-linearly independent, vertical periods.

An example of such function is any finite partial sum of a Dirichlet series. Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places, and $S_f$ the subset of $S$ of all of the finite places of $F$ contained in $S$. Then the function:

$$
\prod_{v\in S_f}(1-q_v^{-s-it_v}) \tag{7.1.1.1}
$$

is, for $q_v := N(\mathfrak{p}_v)$ for $\mathfrak{p}_v$ the unique prime ideal of $\mathcal{O}_F$ corresponding to the finite place $v$, almost periodic.

## PDF page 313

**7.1. POLAR MULTIPLICITIES** · **313**

Each factor is periodic of period $2\pi i/\log(q_v)$. For finite places $v, v'$ contained in $S$ with different residue characteristics, the real numbers $\log(q_v)$ and $\log(q_{v'})$ are $\mathbf{Q}$-linearly independent, and the function in (7.1.1.1) is not periodic.

However, it recurs enough often for us to find a sequence of vertical segments within the vertical strips $\mathbf{C}_I$ (with $I$ an open interval containing $0\in\mathbf{R}$) the absolute value of whose ordinates tend to $+\infty$, and on which the function in (7.1.1.1) remains bounded below a positive threshold $N_S > 0$ fixed at the beginning.

For instance, it has zeros at $\{2\pi i\mathbf{Z}/\log(q_v), v\in S_f\}$.

The reciprocal function

$$
\prod_{v\in S_f}(1-q_v^{-s-it_v})^{-1} \tag{7.1.1.2}
$$

is, however, not holomorphic and is even unbounded over some $\mathbf{C}_I$. The question of whether there exists a sequence of ordinates whose absolute value tends to $+\infty$, and such that on the corresponding vertical segments contained in $\mathbf{C}_I$, (7.1.1.2) is uniformly bounded, is a non-trivial one.

We cannot use [Bohr, Ch.2,§46,p.35] applied to the restriction of the function (7.1.1.1) to $i\mathbf{R}$ since the function has zeros within $\mathbf{C}_I$ on $i\mathbf{R}$. For this reason, we use a weaker notion than almost periodicity: strong recurrence.

In §B.5.3.1 we review the notion of (strong) “recurrence” for a holomorphic function on a vertical strip $\mathbf{C}_I$, for $I\subset\mathbf{R}$ a non-empty open interval, the study of which was initiated in B. Bagchi's PhD thesis [Ba1, Ch.1,2]. Strong recurrence is a vertical self-approximation property of holomorphic functions on vertical strips. We refer the reader to [Ba1, Ch.1, §1.4] (respectively [Ba1, Ch.2, §2.3]) for further background of a general character (respectively specific to the holomorphic functions of interest to number theory), and to [Ba2, §3] for applications. It is indeed weaker than almost periodicity (for analytic functions on vertical strips of bounded width, as defined in [Bohr4, Appendix II,§104,p.101]), in light of [Bohr, Ch.2,§47,Corollary,p.37] and [Ba1, Ch.2,§2.4,Prop.2.4.2,p.46] (since, by [Bohr4, Appendix II,§106,p.104], an almost periodic analytic function on $\mathbf{C}_I$ has uniformly strongly recurrent vertical sections in the sense of [Ba1, Ch.2,§2.4,Def.2.4.1]). It can be thought of as a “local” analog of almost periodicity.

The following Lemma also follows from Proposition B.5.3.3, to which the reader is referred, whose proof is direct and rests upon the Kronecker-Weyl Theorem (see Theorem B.5.2.1).

Recall that for $F$ a number field, $v$ a finite place of $F$, we denote by $q_v$ the absolute norm of the unique prime ideal $\mathfrak{p}_v\subset\mathcal{O}_F$ associated to $v$.

Lemma 7.1.1.1. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We write $S_f := S\cap\Sigma_{F,f}$. Assume $\mathrm{Pic}(\mathcal{O}_{F,S}) = 1$.*

*Let $\delta > 0$ be an arbitrary real number. Let $\chi\in\widehat{C_F}$ be a continuous caracter, unramified outside $S$. Let $t_v\log(q_v)$ be a choice of logarithm for $\chi(\mathfrak{p}_v)$, for each $v\in S_f$ at which $\chi$ is unramified.*

*There exists a real number $N_S > 0$ and a sequence $\{T_k\}_{k\in\mathbf{Z}}\subset\mathbf{R}$, such that:*

(1) *$T_k\ge 0$ if $k\ge 0$ and $T_k\le 0$ if $k\le 0$, with $T_k\le T_{k+1}$ for every $k\in\mathbf{Z}$.*

(2) $\lim_{|k|\to +\infty}|T_k| = +\infty$.

(3) For all $k\in\mathbf{Z}$, we have:

$$
\prod_{v\in S_f}|1-q_v^{-\sigma-iT_k+it_v}|^{-1}\le N_S \tag{7.1.1.3}
$$

for all $\sigma\in[-\delta,1+\delta]$.

For $A\subset\mathbf{R}$ a subset, we recall that the upper density of $A$ is defined to be

$$
\bar{d}(A) := \limsup_{T\to +\infty}\frac{\lambda(A\cap[-T,T])}{2T} \tag{7.1.1.4}
$$

## PDF page 314

**314** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

where $\lambda$ is the Lebesgue measure on $\mathbf{R}$, normalized so as to give the interval $[0,1]$ volume 1.

Let $I\subset\mathbf{R}$ be an open interval containing 0. The proof of Lemma 7.1.1.1 rests on the concept of “strongly recurrent” holomorphic function on $\mathbf{C}_I$: for $\phi$ a holomorphic function on $\mathbf{C}_I$, we say that $\phi$ is strongly recurrent over $\mathbf{C}_I$ if and only if for every compact subset $K\subset\mathbf{C}_I$, and for every real number $\varepsilon > 0$, the subset:

$$
\{t\in\mathbf{R} : \sup_{s\in K}|\phi(s+it)-\phi(s)| < \varepsilon\}
$$

has positive upper-density.

The idea to prove Lemma 7.1.1.1 is to use discreteness of the zeros of $\phi(s) := \prod_{v\in S_f}(1-q_v^{-s-it_v})$ within $\mathbf{C}_I$, to find a compact subset $K\subset\mathbf{C}_I$ with non-empty interior, on which $|\phi(s)|$ is nowhere vanishing and bounded below by a positive constant $M$, for then choosing $\varepsilon > 0$ small enough compared to $M$, and access the strong recurrence of $\phi$ over $\mathbf{C}_I$, on the compact subset $K$ and for such choice of $\varepsilon$, to keep the values of $1/\phi(s)$ bounded in absolute value over the vertical translates $K+it$, for $t$ in a set of positive upper-density in $\mathbf{R}$.

Proof of Lemma 7.1.1.1. We consider the space $\mathscr{H}(\mathbf{C}_I)$ of holomorphic functions on the vertical strip $\mathbf{C}_I$, with $I\subset\mathbf{R}$ any open interval containing $0\in\mathbf{R}$, upon topologizing $\mathscr{H}(\mathbf{C}_I)$ with the topology of uniform convergence on compact subsets as in [Ba1, Ch.2,§2.2.2]. In [Ba1, Ch.2,§2.2.3], $\mathscr{H}(\mathbf{C}_I)$ is equipped with the vertical-shift action of $\mathbf{R}$, a continuous flow.

The holomorphic function $\phi$ defined in (7.1.1.1) is strongly recurrent as a holomorphic function on $\mathbf{C}_I$ due to the vertical periodicity of its finitely many factors and [Ba1, Ch.2,Prop.2.3.3].

This means that for any compact subset $K\subset\mathbf{C}_I$ with non-empty interior, and any real number $\varepsilon > 0$, we have:

$$
\bar{d}(\{t\in\mathbf{R} : \sup_{s\in K}|\phi(s+it)-\phi(s)| < \varepsilon\}) > 0. \tag{7.1.1.5}
$$

Since the set of zeros of $\phi$ is discrete in $\mathbf{C}_I$ and entirely contained in $i\mathbf{R}\subset\mathbf{C}_I$, there exists a compact subset $K_0$ of $\mathbf{C}_I$ with non-empty interior, such that its interior has non-empty intersection with $i\mathbf{R}$, and such that $|\phi(s)|$, as a real valued function on $K_0$, is nowhere vanishing and bounded below by a positive constant $M > 0$.

We may replace $K_0$ with the union of $K_0$ and two large enough compact boxes with non-empty interior $B_1, B_2\subset\mathbf{C}$ such that the intersection of $K_0\cup B_1\cup B_2$ with the boundary of $\mathbf{C}_{[-\delta,1+\delta]}$ ($\delta > 0$ being fixed in the statement of the Lemma) is the union of two vertical segments, one within the vertical line $-\delta+i\mathbf{R}$, the other within the vertical line $1+\delta+i\mathbf{R}$. We further choose $B_1$ and $B_2$ such that $K_0\cup B_1\cup B_2$ has connected and simply connected interior, containing a horizontal segment of the form $[-\delta,1+\delta]+iT$ for some $T\in\mathbf{R}$, such that $(-\delta,1+\delta)+iT$ is entirely contained in the interior of $K_0\cup B_1\cup B_2$.

We now rename $K_0\cup B_1\cup B_2$ as $K_0$, and choose $I\subset\mathbf{R}$ strictly larger than $[-\delta,1+\delta]$.

Since $\phi$ only has zeros on the line $i\mathbf{R}$, we may rename as $M$ the new strictly positive lower bound for $|\phi(s)|$ over $K_0$.

Upon choosing $K = K_0$ and $\varepsilon := M/2$ in (7.1.1.5), we deduce that there exists a subset $A\subset\mathbf{R}$ of positive upper-density, such that on each of the vertical translates $K_0+it$ as $t\in A$, the function $|\phi(s)|$ satisfies:

$$
|\phi(s)|\ge M-\varepsilon = \frac{M}{2} > 0. \tag{7.1.1.6}
$$

Indeed, we have:

$$
||\phi(s+it)|-|\phi(s)||\le |\phi(s+it)-\phi(s)| < \varepsilon
$$

for all $s\in K_0$ and all $t\in A$, and hence:

$$
-\varepsilon < |\phi(s+it)|-|\phi(s)| < \varepsilon \tag{7.1.1.7}
$$

## PDF page 315

**7.1. POLAR MULTIPLICITIES** · **315**

for all $s\in K_0$ and all $t\in A$. From (7.1.1.7), it follows that we have:

$$
M-\varepsilon\le |\phi(s)|-\varepsilon < |\phi(s+it)|
$$

and hence (upon renaming $s+it$ as $s$) (7.1.1.6) holds for all $s\in K_0+it$ and all $t\in A$. We deduce that we have:

$$
|1/\phi(s)|\le 1/(M-\varepsilon)
$$

for all $s\in\bigcup_{t\in A}(K_0+it)$. Upon choosing any point $s_0\in K_0\cap i\mathbf{R}$ in the interior of $K_0$ such that the horizontal segment $L := [-\delta,1+\delta]+s_0$ is contained in $K_0$ and its interior is contained in the interior of $K_0$, we deduce that we have:

$$
|1/\phi(s)|\le 1/(M-\varepsilon)
$$

for all $s\in\bigcup_{t\in A}\{L+it\}$.

Since $A$ has positive upper-density $\delta_A > 0$ in $\mathbf{R}$, for $0 < \delta < \delta_A$ there exists a sequence $\{T'_k\}_{k\in\mathbf{N}}\subset\mathbf{R}_{>0}$ such that $T'_{k+1}\ge T'_k$ for all $k\ge 0$, $\lim_{k\to +\infty}T'_k = +\infty$, and such that each intersection $A\cap[-T'_k,T'_k]$ satisfies:

$$
\lambda(A\cap[-T'_k,T'_k])\ge 2\delta T'_k. \tag{7.1.1.8}
$$

Since the lower bound is tending toward $\infty$ as $k$ grows, for each integer $k\ge 0$ we therefore find an integer $m_k > k$ such that $(A\cap[-T'_{m_k},T'_{m_k}])-(A\cap[-T'_k,T'_k])$ is non-empty.

We denote, for each integer $k\ge 0$, by $m^{(N)}(k)$ the integer defined by the recursion $m^{(1)}(k) := m_k$, and $m^{(N+1)}(k) := m_{m^{(N)}(k)} > m^{(N)}(k)$, and call $T''_k := T'_{m^{(k)}(0)}$. This defines a subsequence of $\{T'_k\}_{k\ge 0}$, which therefore satisfies $T''_k\le T''_{k+1}$, $\lim_{k\to +\infty}T''_k = +\infty$, and, for every integer $k\ge 1$, the set $(A\cap[-T''_{k+1},T''_{k+1}])-(A\cap[-T''_k,T''_k])$ is non-empty.

We choose, for each integer $k\ge 0$, $T'''_k\in(A\cap[-T''_{k+1},T''_{k+1}])-(A\cap[-T''_k,T''_k])$, and we obtain:

$$
|1/\phi(s_0+iT'''_k)|\le 1/(M-\varepsilon)
$$

for all $k\in\mathbf{N}$. We now define $T_k := \mathrm{Im}(s_0)+T'''_k$ for $k\ge 0$. We obtain that for every integer $k\ge 0$, we have

$$
|1/\phi(\sigma+iT_k)|\le 1/(M-\varepsilon)
$$

for all $\sigma\in[-\delta,1+\delta]$. We have arranged the $T_k$ to satisfy $\lim_{k\to +\infty}|T_k| = +\infty$. We now observe that if $|1/\phi(\sigma+iT_k)|\le 1/(M-\varepsilon)$, then we also have $|1/\phi(\sigma-iT_k+2it_v)|\le 1/(M-\varepsilon)$, since we have

$$
|1/\phi(\sigma-iT_k+2it_v)| = |\overline{1/(\sigma+iT_k)}|
$$

for all $\sigma\in[-\delta,1+\delta]$ and for each integer $k\ge 0$. We now consider the countable subset of $i\mathbf{R}$ given by

$$
V = \{iT_k, k\in\mathbf{N}\}\cup\{-iT_k+2it_v, k\in\mathbf{N}\}
$$

and relabel it according to the following rule: we order the ordinates of $V\cap i[0,+\infty)$ increasingly and label them by the nonnegative integers. We order the ordinates of $V\cap i(-\infty,0)$ increasingly (i.e. according to the total order inherited from the real line) and label them by the negative integers, themselves equipped with their natural total ordering.

We rename the elements of $-iV$ as $T_k$ for $k\in\mathbf{Z}$. Upon choosing $N_S := M-\varepsilon > 0$, we see that $\{T_k\}_{k\in\mathbf{Z}}$ satisfies the requirements of the Lemma.

$\square$

The Lemma says that the reciprocals of the partial Euler products of the Hecke $L$-function $L(s,\chi)$ are meromorphic functions with slow growth near their poles, in the sense of Definition B.3.1.1. The Lemma provides access to the Asymptotic Residue Theorem (see Theorem B.3.2.1).

**7.1.2. Asymptotic expansion of $\Phi_{F,S}(f)(g)$ as $|g|_{F,S}\to 0^+$.** The following Theorem passes Proposition 2.4.1.1 and its general version of Theorem 2.4.2.1, through the lens of the Mellin transform. We further refer the reader to Theorem B.2.1.7.

## PDF page 316

**316** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

We will be using Theorem 7.1.2.3 throughout this Chapter as a source of motivation for the search of certain Schauder bases for subquotients of the nuclear Fréchet spaces

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))
$$

as well as a means to explain the description of certain periodic orbits associated to the non-Archimedean places of a number field $F$, to be discussed at the end of this Chapter, exhibiting them as analogs of the periodic orbits that serve as the supports of the orbital measures in [Sarnak, §0,Thm.1].

The role of the periodic orbits found throughout our work is in fact the same as that of the periodic orbits of the horocycle flow on the space of elements of a Riemann surface, that features in Sarnak's paper [Sarnak], which the higher rank version of our work will recast as a special case of the $\mathrm{GL}_2$-analog of Theorem 7.1.2.3 below.

Throughout this work we refer to “order of pole” at $s_0\in\Omega$ of a meromorphic complex valued function $f : \Omega\to\mathbf{C}$ on a domain of the complex $s$-plane $\Omega\subset\mathbf{C}$ as the nonnegative integer $N\ge 0$ such that $a_m(f,s_0)$, the $m$th coefficient of the Laurent series expansion of $f$ centered at $s = s_0$ for $m\in\mathbf{Z}$, vanishes for $m < -N$, minimal (among the nonnegative integers) with respect to this property, i.e. $a_{-N}(f,s_0)\ne 0$. We therefore say $f$ has a pole of order $N$ at $s = s_0$.

We require the following

Definition 7.1.2.1. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $f\in\mathcal{S}(\mathbf{A}_{F,S})$ be a Schwartz-Bruhat function.

We define the polar $S$-multiplicity of $c$ to be the order of pole

$$
m_S(f,c) := -\mathrm{ord}_c Z_S(f,\cdot)\ge 1 \tag{7.1.2.1}
$$

of the meromorphic function $Z_S(f,\cdot)$ on $\Omega(J_{F,S})$ at $c$ when it has a pole there, and define $m_S(f,c) := 0$ if $Z_S(f,\cdot)$ has no pole at $c$. We define, for each integer $m\in\mathbf{Z}$:

$$
a_m(f,c) \tag{7.1.2.2}
$$

to be the $m$th coefficient of the Laurent series expansion centered at $c\in\Omega(J_{F,S})$.

Recall from §3.1.1 that the connected components of $\Omega(J_{F,S})$ are parametrized as $\chi|\cdot|^s_{F,S}$ for $\chi\in\widehat{J_{F,S}}$ a unitary base-point and $s\in\mathbf{C}$. Orders of poles and coefficients of principal parts are all defined relative to a parametrization, and are seen to be independent of the parametrization, which is why they are denoted as in (7.1.2.1) and (7.1.2.2) without reference to a choice of holomorphic parametrization of the connected components of $\Omega(J_{F,S})$.

We recall the definition of the meromorphic function $\rho_S$ on $\Omega(J_{F,S})$ and the exact location of its poles. We have:

$$
\rho_S(c) := \prod_{v\in S}\rho_v(c_v)
$$

where $c_v$ is the image of $c\in\Omega(J_{F,S})$ in $\Omega(F^\times_v)$, the Riemann surface of continuous quasi-characters of the local field $F_v$. The meromorphic function $\rho_v$ is the explicit meromorphic function from [CF, Ch.XV,§§2.5], obtained from the local functional equations. We further refer the reader to (3.3.1.3) from Lemma 3.3.1.1.

Lemma 7.1.2.2. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\chi\in\widehat{J_{F,S}}$ be a continuous character of $J_{F,S}$. Let $S_\chi$ be the finite set of finite places in $S$ at which $\chi$ is ramified, and define $S_f := S\cap\Sigma_{F,f}$,*

*Identify the connected component $\Omega(J_{F,S})(\chi)$ of $\chi$ with $\mathbf{C}$ via the parameterization $\chi|\cdot|^s_{F,S}$ (so $s$ is well-defined up to an overall vertical shift under change of unitary base point $\chi$).*

*The poles of $\rho_S$ on $\Omega(J_{F,S})(\chi)$ are precisely points $c_{v,m,\chi}$ for $v\in S-S_\chi$ and certain integers $m$ (depending on $v$) with $m\le 0$ for Archimedean $v$, defined as follows:*

## PDF page 317

**7.1. POLAR MULTIPLICITIES** · **317**

(1) *for $v$ Archimedean we write $\chi_v = \chi_0|\cdot|^{it_{\chi_v}}_v$ with a unique $t_{\chi_v}\in\mathbf{R}$ and a unitary $\chi_0$ that is either trivial or the sign character of $F^\times_v = \mathbf{R}^\times$ for real $v$ and $\chi_0 : z\mapsto (z/|z|)^k$ for a unique integer $k\in\mathbf{Z}$ for complex $v$, and define*

$$
c_{v,m,\chi} = \chi|\cdot|^{m-it_{\chi_v}}_{F,S}
$$

*where $m$ varies as follows depending on $\chi_0$: $m\in -2\mathbf{N}$ when $\chi_0 = 1$ for real $v$, $m\in -1-2\mathbf{N}$ when $\chi_0 = \mathrm{sgn}$ for real $v$, and $m\in (|k|/2)-\mathbf{N}$ for complex $v$;*

(2) *for $v$ non-Archimedean (so $\chi$ is unramified at $v$: $v\not\in S_\chi$) and $q_v$ the size of the residue field at $v$, we write $\chi_v = |\cdot|^{it_{\chi_v}}_v$ with a unique $t_{\chi_v}\in[0,2\pi/\log(q_v))$ and define*

$$
c_{v,m,\chi} = \chi|\cdot|^{(2\pi i/\log(q_v))m-it_{\chi_v}}_{F,S}
$$

for all $m\in\mathbf{Z}$.

Beware that for such poles $c$, the pole-order $m_S(c) = -\mathrm{ord}_c(\rho_S)\ge 1$ may exceed $-\mathrm{ord}_{c_v}(\rho_v)$ for the unique place $v\in S-S_\chi$ such that $c = c_{v,m,\chi}$. For example, there may be finite places $v, w\in S-S_\chi$ over the same rational prime $p$ for which $F_v\simeq F_w$ and compatibly $\rho_v = \rho_w$. This matter will be revisited in §7.1.3.

Proof. By definition, $\rho_S(c) = \prod_{v\in S}\rho_v(c_v)$, where $c_v$ is the quasi-character of $F^\times_v$ obtained from $c$. The functions $\rho_v\in\Omega(F^\times_v)$ are tabulated explicitly on each connected component in [CF, Ch. XV, pp. 316-322]. Inspection shows that on the connected components of ramified quasi-characters for non-Archimedean $v$ the function $\rho_v$ is entire and non-vanishing (related to local root numbers of ramified characters), while in all other cases a zero of any of these never cancels a pole of another (not even the real parts ever coincide). Thus, the set of poles of $\rho_S(\chi|\cdot|^s_{F,S})$ is exactly the union of the sets of poles of the meromorphic functions $\rho_v$ (composed with the analytic covering map $\Omega(J_{F,S})\to\Omega(F^\times_v)$) for $v\in S-S_\chi$, and the pole order of $\rho_S$ at such a pole agrees with that of the corresponding $\rho_v$ for a uniquely determined $v$ (depending on the pole under consideration). Since we have parameterized the connected component of $\chi$ in $\Omega(J_{F,S})$ via $\chi|\cdot|^s_{F,S}$, for such a point to be a pole of $\rho_v$ with $v\in S-S_\chi$ we note that its restriction to $F^\times_v$ is $\chi_v|\cdot|^s_v$, so the possibilities for such $s$ are exactly read off from Tate's formulas for the $\rho_v$'s in all cases (Archimedean $v$ on each connected component of $\Omega(F_v)$, and non-Archimedean $v$ on the connected component of unramified quasi-characters in $\Omega(F_v)$). This yields exactly the list of points (in effect, the values for $s$) as claimed.

$\square$

The following, is the main Theorem of this section. We will be subsequently explain the connection with Sarnak's Theorem on the uniform distribution of long horocycles (see [Sarnak, §0,Thm.1]), a connection that will accompany us all the way through this Chapter until we find and describe the periodic orbits associated to the non-Archimedean places of the number field $F$, and show they serve a similar role as the periodic orbits of the horocycle flow from [Sarnak]. The higher rank version of the methods being presented in this work will generalize [Sarnak, §0,Thm.1], eventually rendering the analogy discussed at the end of this Chapter, sharper.

We let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. For a prime number $p$, we denote by $S_p$ the subset of those finite places $v$ of $F$ contained in $S$ such that the residue characteristic of the non-Archimedean local field $F_v$ is $p$.

We denote by $\Pi$ the set of all prime numbers, and by $\Pi(S)\subset\Pi$ the subset of the prime residue characteristics of the non-Archimedean local fields $F_v$ for each $v\in S_f := \Sigma_{F,f}\cap S$.

Theorem 7.1.2.3 (On Asymptotic Expansions as $|g|_{F,S}\to 0^+$). *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places. Let $\chi\in\widehat{J_{F,S}}$ be a continuous character. We have, for every real*

## PDF page 318

**318** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

number $A > 0$:

$$
\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)(g) = \sum_{v\in S_\infty}\sum_{m\in\mathbf{N}_{>0},m<A}\sum_{1\le k\le m_S(f,c_{v,m,\chi})}\frac{(-1)^{k-1}a_{k-1}(f,c_{v,m,\chi})}{(k-1)!}\bar{\chi}(g)|g|^{m+it_v}_{F,S}(\log|g|_{F,S})^{k-1} \tag{7.1.2.3}
$$

$$
+ \sum_{p\in\Pi(S)}\sum_{v\in S_p}\sum_{m\in\mathbf{Z}}\sum_{1\le k\le m_S(f,c_{v,m,\chi})}\frac{(-1)^{k-1}a_{k-1}(f,c_{v,m,\chi})}{(k-1)!}\bar{\chi}(g)|g|^{-\frac{2\pi i m}{\log(q_v)}+it_v}_{F,S}(\log|g|_{F,S})^{k-1}
$$

$$
+ O_A(|g|^A_{F,S})
$$

*as $|g|_{F,S}\to 0^+$, where the series converges uniformly on the compact subsets of $J_{F,S}$, the implied constant depends only on the restriction of $Z_S(f,\cdot)$ to the relative vertical line $\sigma(c) = -A$, and where each $c_{v,m,\chi}$ is a pole of the meromorphic function $\rho_S$ from (3.3.1.3) (these poles are made explicit in Lemma 7.1.2.2).*

Before we take up the proof, we make an extended Remark to provide broader perspective of the meaning of the result.

Remark 7.1.2.4 (On the poles of the non-Archimedean Euler factors of induced $L$-functions). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\chi\in\widehat{J_{F,S}}$ be a continuous character, and $v$ a finite place of $F$ contained in $S$ at which $\chi$ is unramified.

We assume $S$ is so large so as to arrange $\mathrm{Pic}(\mathcal{O}_{F,S}) = 1$, so that we can think $\chi$ as a continuous character of $C_F$ by composition of the inverse isomorphism of Hausdorff locally compact abelian groups $C_{F,S}\to C_F$, with the quotient $C_{F,S}\to J_{F,S}$. Upon doing this, we can refer to the meromorphic function $(1-\chi(\pi_v)|\pi_v|^s)^{-1}$ as the non-Archimedean local factor of the Hecke $L$-function $L(s,\chi)$ without ambiguity.

The real numbers $t_v$ are obtained as follows. We choose a logarithm $\log\chi(\pi_v)$ of $\chi(\pi_v)$, where $v$ is a finite place of $F$ contained in $S$ at which $\chi$ is unramified, and $\pi_v$ is a local uniformizer for the local field $F_v$.

If the choice of branch of the logarithm is the principal one translated vertically upwards by $i\pi$, then $t_v$ is obtained as $\frac{\log\chi(\pi_v)}{\log(q_v)}$ where $q_v$ is $N(\mathfrak{p}_v) = |\pi_v|^{-1}_v$, with $\mathfrak{p}_v\subset\mathcal{O}_F$ the unique prime ideal of $\mathcal{O}_F$ associated to the finite place $v$.

The poles of the non-Archimedean local factor $(1-\chi(\pi_v)q_v^{-s})^{-1}$ of the Hecke $L$-function $L(s,\chi)$ are a torsor under $\mathbf{Z}/\frac{2\pi i}{\log(q_v)}$, and hence the general such pole is obtained by vertical translation under $\mathbf{Z}/\frac{2\pi i}{\log(q_v)}$, of the point $\chi|\cdot|^{-it_v}_{F,S}\in\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$.

We now choose an algebraic closure $\overline{\mathbf{Q}}$ of $\mathbf{Q}$. We note that if $S_p$ is “saturated”, i.e. if the prime number $p$ is such that $S$ contains all the finite places of $F$ whose residue characteristic is $p$, then the collection of the points:

$$
\chi|\cdot|^{-\frac{2\pi i m}{\log(q_v)}+it_v}_F,\ v\in S_p,\ m\in\mathbf{Z}
$$

are the poles of the product of non-Archimedean local factors $\prod_{v\in S_p}(1-\chi(\pi_v)q_v^{-s})^{-1}$, which is in turn the Euler factor at the prime number $p$ of the $L$-function $L(s,\rho)$, where $\rho$ is the continuous finite dimensional complex representation of the Weil group $W_{\mathbf{Q}}$ (relative to the choice of algebraic closure $\overline{\mathbf{Q}}$ of $\mathbf{Q}$ we have made) obtained by inducing the inflation of the character $\chi$ to $W_{F'/F}$, with $F'$ the Galois closure of $F$.

This observation will be reprised in Chapter 8 (see the proof of Proposition 14.1.2.3).

We now look at Theorem 7.1.2.3 through the lens of Sarnak's paper on the uniform distribution of long horocycles (see [Sarnak, §0,Thm.1]).

We let $M$ be a Riemann surface, and $T^1M\to M$ its unit tangent bundle. We equip $M$ with its Poincaré metric, promoting it to a complete Riemannian manifold with constant negative curvature. We assume $M$ is non-compact, with finite volume.

For $r\ge 0$ the finite number of inequivalent cusps, there exist $r$ pairwise disjoint immersed submanifolds $P_k\subset T^1M$, $1\le k\le r$, whose union consists of all the periodic points of the horocyclic flow on $T^1M$.

## PDF page 319

**7.1. POLAR MULTIPLICITIES** · **319**

For each cusp $x_k$, $1 \le k \le r$, and for each real number $t > 0$, $\nu^{(k)}(t)$ is the probability measure on the closed orbit of period $t^{-1}$ of the horocyclic flow on $T^1M$ assigning uniform mass with respect to arc-length to such closed orbit.

$\nu^{(k)}(t)$ is constructed in [Sarnak, §2,(2.1)] as an element of the strong dual of $\mathcal{D}(T^1M)$, by means of the Uniformization Theorem. Let $\Gamma \subset \mathrm{PSL}_2(\mathbf{R})$ be a discrete subgroup acting properly discontinuously on the upper half-plane $\mathbf{H}$ equipped with the Poincaré metric, such that $M$ is isometric to $\Gamma\backslash \mathbf{H}$.

$\Gamma$ acts on $T^1\mathbf{H} \simeq \mathrm{PSL}_2(\mathbf{R})$ through tangent maps and we identify $T^1M$ isometrically to $\Gamma\backslash T^1\mathbf{H}$. Since $\Gamma$ acts on $\mathbf{H}$ and $T^1\mathbf{H}$ by isometries, the horocyclic flow on $T^1\mathbf{H}$ descends to the quotient $T^1M$, and in order to define $\nu^{(k)}(t)$ it is enough to do so for $k = 1$ on $T^1\mathbf{H}$ for then propagating the measure to the cusps other than the first, i.e. the one at $\infty \in \overline{\mathbf{H}}$, by push-forward along the $\Gamma$-action.

This is done in [Sarnak, §2,(2.1)] by integrating over a fundamental domain within the standard fundamental domain for the $\Gamma$-action on $T^1\mathbf{H}$, for the closed orbit of period $1/t$ on $T^1M$ of the horocyclic flow, the generic automorphic function $f$ on $T^1\mathbf{H}$.

The $J_{F,S}$-parametrized families of continuous functionals

$$
a_m(\cdot, \chi|\cdot|^{\frac{2\pi i m}{\log(q_v)}-it_v}_{F,S})\, \overline{\chi}(g)|g|^{-\frac{2\pi i m}{\log(q_v)}+it_v}_{F,S} (\log|g|_{F,S})^k
$$

are the direct analogs of the measures $\nu^{(k)}(t)$.

Throughout this Chapter, the Riemann surface $M$ is replaced by the $S$-adeles $\mathbf{A}_{F,S}$ for all large enough $S$, the automorphic function is replaced by the arbitrary $S$-local $\theta$-function $\Phi_{F,S}(f)$ for $f$ a Schwartz-Bruhat function on $\mathbf{A}_{F,S}$ (noting that the continuous functionals $a_m(\cdot, c)$ are $\mathcal{O}_{F,S}^{\times}$-invariant and hence are continuous on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$; see Definition 5.5.1.1 and Theorem 5.5.1.2 of the previous Chapter, discussing $S$-local eigendistributions; see also Theorem 7.2.1.4 in this Chapter).

The parameter $t$ in $\nu^{(k)}(t)$ is replaced by $\log|g|_{F,S}$.

Throughout [Sarnak, §2], Sarnak proves continuity on $\mathcal{D}(T^1M)$ of the Mellin transform of $\nu^{(k)}(t)$: continuity of $a_m(\cdot, c)$ and of formation of the $S$-idelic Mellin transform of the $S$-local $\theta$-functions $\Phi_{F,S}(\cdot)$, is what we have discussed throughout Chapter 3 and Chapter 4 of this work.

Sarnak then studies the measures $\nu^{(k)}(t)$ for all small enough $t > 0$ by means of their Mellin transform, relating them to certain functional families of Eisenstein series and recasting them as residue functionals of the meromorphic vector valued functions $E^{(k)}(s)$ introduced throughout [Sarnak, §2] (see [Sarnak, §2,(2.2),p.724]) which, when evaluated on the generic automorphic function, are seen to be related to classical Eisenstein series in [Sarnak, §2,Prop.2.6,p.726], which gives access to Selberg's work informing us on their singularities and asymptotic behavior, as well as vector-valued functional equations (see [Sarnak, §2,Thm.2.7,p.726], [Sarnak, §2,Thm.2.11,p.729], and the family of functional equations in [Sarnak, §2,Thm.2.16,p.731], as well as the section on poles and residues in [Sarnak, §2.17]). We further refer the reader to [Iwaniec, Ch.6,§6.3,6.4] and [Kubota, Ch.IV,§4.4]. We further refer the reader to Zagier's [Zagier, §1].

This is what we have also done concerning the functionals

$$
a_m(\cdot, c)
$$

for $c \in \Omega(J_{F,S})$ and $m \in \mathbf{N}$, by analyzing the functional properties of the $S$-local $\theta$-functions $\Phi_{F,S}(f)$ (the $\mathrm{GL}_1$-analogs of the Eisenstein series arising in Sarnak's paper) through their $S$-idelic Mellin transforms $Z_S(f, c)$, from which $a_m(f, c)$ are obtained as coefficients of principal parts.

Following the dictionary being outlined above, Theorem 7.1.2.3 is then analogous to the main Theorem in Sarnak's paper, namely [Sarnak, §0,Thm.1], relating the measures $\nu^{(k)}(t)$ to the canonical Riemannian measure $\mu$ on $T^1M$, and to residue functionals $\mu^{(k)}_m$ (obtained in [Sarnak, §2] in a similar manner as our

## PDF page 320

**320** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

$S$-local eigendistributions $a_m(\cdot, c)$), for all small enough $t > 0$, by the asymptotic expansion:

$$
\nu^{(k)}(t) = \frac{\mu}{2\pi V} + \sum_{1 \le m \le N} t^{1-s_m} \mu^{(k)}_m + o(t^{1/2}) \tag{7.1.2.4}
$$

as $t \to 0^+$, for $V$ the volume of $M$.

The meaning of the asymptotic expansion in (7.1.2.4) is that for each $f \in \mathcal{D}(T^1M)$, the evaluation on the element $f$ of all the functionals featuring in each side of (7.1.2.4) obeys the asymptotic relation:

$$
\langle \nu^{(k)}(t), f \rangle_{\mathcal{D}(T^1M),\mathcal{D}(T^1M)'} = \langle \frac{\mu}{2\pi V}, f \rangle_{\mathcal{D}(T^1M),\mathcal{D}(T^1M)'} + \sum_{1 \le m \le N} t^{1-s_m} \langle \mu^{(k)}_m, f \rangle_{\mathcal{D}(T^1M),\mathcal{D}(T^1M)'} + o(t^{1/2}) \tag{7.1.2.5}
$$

where the writing $\langle \mathcal{D}(T^1M), \mathcal{D}(T^1M)' \rangle$ refers to the duality of $\mathcal{D}(T^1M)$, the Hausdorff locally convex topological $\mathbf{C}$-vector space of test functions on $T^1M$, with its continuous dual. The $o(t^{1/2})$ (7.1.2.4) therefore refers to the rate of convergence to zero with respect to the topology of simple convergence on $\mathcal{D}(T^1M)$, i.e. the $\sigma(\mathcal{D}(T^1M)', \mathcal{D}(T^1M))$-topology.

Here the monomial functions $t^{1-s_m}$ play the same role as $\overline{\chi}(g)|g|^{-\frac{2\pi i m}{\log(q_v)}+it_v}_{F,S} (\log|g|_{F,S})^k$ in (7.1.2.3) of Theorem 7.1.2.3, and the asymptotic expansion for $\Phi_{F,S}(f)$ obtained in Theorem 7.1.2.3 is also as $|g|_{F,S} \to 0^+$, as is the case in [Sarnak, §0,Thm.1].

The measures $\mu^{(k)}_m$ in Sarnak's work are supported on the periodic loci $P_k$, and the geometric meaning of [Sarnak, §0,Thm.1] from (7.1.2.4) is that long horocycles (i.e. the periodic orbits contained within the immersed cylinders $P_k$, as their period $1/t$ tends to $+\infty$) tend to distribute themselves uniformly over $T^1M$ with respect to $\mu$ (obtained upon endowing $\Gamma$ with the counting measure and $T^1\mathbf{H}$ with the push-forward of the normalized Haar measure $\frac{\mathrm{d}x\,\mathrm{d}y\,\mathrm{d}\theta}{y^2}$ on $\mathrm{PSL}_2(\mathbf{R})$ by uniformization).

The uniform distribution of long horocycles bears on neighboring questions of arithmetic significance. As is often the case for continuous-time uniform distribution results, a discrete analog of Sarnak's Theorem exists. We refer the reader to [AtChe], where the authors describe a Poincaré section to the horocyclic flow and establish discrete-time versions of [Sarnak, §0,Thm.1] (see [AtChe, Thm.1.3]) where the horocyclic flow is discretized into the discrete flow generated by a self-map constructed by Boca-Cobeli-Zaharescu in [BCZ], in analogy with C. Series' work on a Poincaré section of the geodesic flow on the unit tangent bundle of the modular surface, as opposed to the horocyclic flow, discretized into the discrete flow generated by the Gauss' map (see the map $T$ on [Series, §2,p.76] and [Series, §2,Thm.C], which is ergodic with respect to the Gauss' measure $A \mapsto \frac{1}{\log(2)} \int_A \frac{\mathrm{d}x}{1+x}$ on $(0, 1)$, in analogy with [AtChe, Thm.1.2]) with applications to continued fractions.

It is possible to look at the asymptotic expansion from Theorem 7.1.2.3 too through the lens of ergodic theory (using Dirichlet's $S$-Unit Theorem and the lattice point-counting techniques underlying the proof of Theorem 2.4.2.1).

What we are most interested in, however, is the question of whether an analog of the periodic orbits and periodic loci $P_k$ in [Sarnak, §2] exists in the context of our Theorem 7.1.2.3 too.

By the end of this Chapter, this question will be answered in the affirmative, exhibiting orbital quotient stacks arising as topological quotient stacks of certain closed loci within $\mathbf{A}_{F,S}$ which are responsible for the existence of poles of the $S$-idelic Zeta functions $Z_S(f, c)$, and which are in correspondence with divisors on the Riemann surface $\Omega(J_{F,S})$ under $L_S$ from (5.1.1.2).

This leads to the finding of periodic orbits and fixed loci that realize the structures predicted by C. Deninger in his expectations on the existence of a functional approach to the problem of a Trace-Formula theoretic interpretation to Weil's Explicit Formulas.

They will indeed be underlying indirectly the trace calculation which is the main subject of study of this work.

## PDF page 321

**7.1. POLAR MULTIPLICITIES** · **321**

At the end of this Chapter, we will be describing the periodic orbits alluded to above, and we will be explaining how they indeed serve the same purpose of the periodic loci $P_k$ within $T^1M$ in [Sarnak]: in a precise sense they serve, similarly as the $P_k$'s do, as the supports of the continuous functionals $a_m(\cdot, \chi|\cdot|^{\frac{2\pi i m}{\log(q_v)}-it_v}_{F,S})$, whenever $v$ is a non-Archimedean place contained in $S$.

We will now prove Theorem 7.1.2.3. The proof mirrors to some meaningful extent the proof of [Sarnak, §0,Thm.1], and rests on the $S$-local functional equation of (3.3.1.3) from Lemma 3.3.1.1, which plays the same role as the vector-valued functional equations of [Sarnak, §2,Thm.2.7,p.726] and [Sarnak, §2,Thm.2.16,p.731], as well as Mellin inversion and the Asymptotic Residue Theorem (see Theorem B.3.2.1 and Theorem B.2.1.7).

The main difference between Theorem 7.1.2.3 and [Sarnak, §0,Thm.1] is that countably many poles are involved in the statement and in (7.1.2.3), and hence applying the Asymptotic Residue Theorem requires knowledge of the existence of horizontal segments on which partial Euler products are kept under control. This knowledge is provided to us by either Lemma 7.1.1.1, or, resting on the Kronecker-Weyl Theorem (see Theorem B.5.2.1), by Proposition B.5.3.3.

We now prove Theorem 7.1.2.3.

*Proof of Theorem 7.1.2.3.* We first choose $A \in (-1, 0)$.

We define the meromorphic function on the complex $s$-plane:

$$
\Phi(s) := Z_S(f, \chi|\cdot|^s_{F,S}) \prod_{v \in S_f} (1 - q_v^{-s-it_v}) \prod_{v \in S_\infty} (s - s_v)^{m_v}
$$

for $q_v := N(\mathfrak{p}_v)$ with $\mathfrak{p}_v$ the unique prime ideal of $\mathcal{O}_F$, corresponding to $v \in S_f$, and for $s_v$ the unique pole, if any, of the Archimedean local factor $L_v(\chi_v|\cdot|^s_v)$ at $v$, located on the vertical line $i\mathbf{R}$, where $m_v \in \{0, 1\}$ accordingly (for example, if $\chi = 1$, then $\prod_{v \in S_\infty}(s-s_v)^{m_v} = s^{r_1+r_2}$. Recall that $s = 0$ is a pole of $Z_S(f, |\cdot|^s_{F,S})$ of order $r_1+r_2$, since the $\Gamma$-function has a simple pole at $s = 0$, and each such pole of the $r_1+r_2$ Archimedean local $L$-functions contributes one order of pole to the quasi-character $|\cdot|^{s=0}_{F,S} = 1 \in \Omega(J_{F,S})(1)$).

We further define the meromorphic function on the complex $s$-plane:

$$
\phi(s) := \prod_{v \in S_f} (1 - q_v^{-s-it_v})^{-1} \prod_{v \in S_\infty} (s - s_v)^{-m_v}.
$$

The meromorphic function $Z_S(f, \chi|\cdot|^s_{F,S})$ on the complex $s$-plane is the product:

$$
Z_S(f, \chi|\cdot|^s_{F,S}) = \Phi(s)\phi(s).
$$

The function $\Phi(s)$ has only removable singularities over $\mathbf{C}_{(-1/2,1/2)}$, and decays, uniformly over $\mathbf{C}_{(-1/2,1/2)}$, faster than any positive power of $|s|^{-1}$ as $|s| \to +\infty$ from within the vertical strip $\mathbf{C}_{(-1/2,1/2)}$. (Explicitly, recall $|\Gamma(\sigma + it)| = O(e^{-(\pi/2)|t|}|t|^{1/2})$ for $|\sigma| \le 1/2$ as $|t| \to +\infty$.)

The function $\phi(s)$ is meromorphic over $\mathbf{C}_{(-1/2,1/2)}$ and has slow growth near its poles, in the sense of Definition B.3.1.1, because $\prod_{v \in S_\infty}(s - s_v)^{-m_v}$ does, being a rational function, and $\prod_{v \in S_f} (1 - q_v^{-s-it_v})^{-1}$ also does, by Lemma 7.1.1.1 applied to the choice $I = (-1/2, 1/2)$.$^1$

Lemma 7.1.2.2 provides the location of the poles of $Z_S(f, |\cdot|^s_{F,S})$ over $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$ holomorphically parametrized by $\chi|\cdot|^s_{F,S}$ (for example, for $\chi = 1$, they are all contained within the subset:

$$
\left\{ |\cdot|^s_{F,S},\, s \in -\mathbf{N} \cup \bigcup_{\{q \in N(\mathfrak{p}_v): v \in S_f\}} \frac{2\pi i\,\mathbf{Z}}{\log(q)} \right\}
$$

of the connected component $\Omega(J_{F,S})(1)$).

---

$^1$check if Definition B.3.1.1 is actually applicable since no control on growth of $|T_k|$'s in Lemma 7.1.1.1, or if it needs to be adjusted while retaining Asymptotic Residue Theorem

## PDF page 322

**322** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

By the Asymptotic Residue Theorem (see Theorem B.3.2.1), applied to $\Phi(s) := \Phi_0(s)$ and $f(s)$ in loc.cit, chosen to be $\phi(s)$, (7.1.2.3) follows, upon performing the following calculation for $t > 0$:

$$
\mathrm{Res}_{s=a} \left( \frac{t^{-s}}{(s-a)^m} \right) = \frac{(-1)^{m-1}}{(m-1)!} t^a (\log(t))^{m-1}
$$

and choosing a continuous homomorphic section $\tau$ to the $S$-idelic norm, so as to rewrite $Z_S(f, \chi|\cdot|^s_{F,S})$ over $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$ as the Mellin transform $M(\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)\circ\tau)(s + ix_0)$, for $x_0 \in \mathbf{R}$ the unique real number such that $\chi(\tau(t)) = t^{ix_0}$ as smooth functions on $\mathbf{R}_{>0}$, of the smooth function of $t \in \mathbf{R}_{>0}$ given by $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)(\tau(t))$.

The convergence of the series in (7.1.2.3) is uniform on the compact subsets of $\mathbf{R}_{>0}$ because the asymptotic vanishing of the line integrals arising in the Asymptotic Residue Theorem, of $\Phi(s)\phi(s)$ evaluated on the horizontal segments $\mathrm{Im}(s) = T_k$ intersected with $\mathbf{C}_{(-1/2,1/2)}$, $\{T_k\}_{k \in \mathbf{Z}}$ being the sequence provided by Lemma 7.1.1.1, is uniform with respect to $t \in \mathbf{R}_{>0}$, since $t^{-s}$ is bounded for $\mathrm{Re}(s) \in (-1/2, 1/2)$, and as $t$ is constrained to vary over a compact subset of $\mathbf{R}_{>0}$.

To obtain the general case of (7.1.2.3), i.e. for any $A > 0$, it suffices to modify the function $\Phi(s)$ by multiplying by $\prod_{v \in S_\infty}(s - s_{v,m})^{m_S(f,\chi|\cdot|^{s_{v,m}}_{F,S})}$, and multiplying $\phi(s)$ by the reciprocal, where $s_{v,m}$ is the unique pole of the Archimedean local factor $L_v(\chi_v|\cdot|^s_v)$ contained within the interior of the vertical strip $\mathbf{C}_{[-m-1/2,-m+1/2]}$, for the finitely many integers $m \in [0, A] \cap \mathbf{N}$.

The new $\Phi(s)$ and $\phi(s)$ again satisfy the assumptions of the Asymptotic Residue Theorem (see Theorem B.3.2.1), and more terms of the first series in (7.1.2.3) (a finite sum, in fact) occur, the error term becoming $O_A(|g|^A_{F,S})$ for the new $A > 0$.

The implied constant is indeed dependent only on $Z_S(f,\chi|\cdot|^s_{F,S})$ restricted to the vertical line $\mathrm{Re}(s) = -A$ within $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$, holomorphically parametrized as $\{\chi|\cdot|^s_{F,S},\, s \in \mathbf{C}\}$, because the error term is provided by $t^{-(-A)}$ multiplied by the $L^1$-norm of $Z_S(f,\chi|\cdot|^s_{F,S})$ over $\mathrm{Re}(s) = -A$ with respect to the Lebesgue measure on such vertical line.

$\square$

The fact that the sums in (7.1.2.3) converge, and the fact that the functionals $a_m(\cdot, c)$ on $\mathcal{S}(\mathbf{A}_{F,S})$ (and indeed, as is to be discussed shortly, on $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$, see Theorem 7.2.1.4), is a first indication that the continuous functionals $a_m(\cdot, c)$ may serve as the coefficient functionals of a Schauder basis on a quotient of $\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}_{F,S}^{\times}, \mathcal{S}(\mathbf{A}_{F,S}))$.

Theorem 7.1.2.3 serves as a first source of motivation for the search for such bases.

It is indeed possible to use Theorem 2.4.2.1 and Proposition 2.3.1.4 to obtain the stronger result that for all $g \in J_{F,S}$ such that $|g|_{F,S} < 1$, the right side of (7.1.2.3) converges uniformly with respect to $f \in \mathcal{S}(\mathbf{A}_{F,S})$ varying over a fixed bounded subset $\mathcal{B}$, in which case the implied constant in $O_A(|g|^A_{F,S})$ depends on $\mathcal{B}$ and not on the specific $f \in \mathcal{B}$.

The asymptotic expansion therefore reads

$$
\Phi_{F,S,\chi|_{J^1_{F,S}}}(\cdot)(g) = \sum_{v \in S_\infty} \sum_{m \in \mathbf{N}_{>0},\, m < A} \sum_{1 \le k \le m_S(\cdot,c_{v,m,\chi})} \frac{(-1)^{k-1} a_{k-1}(\cdot, c_{v,m,\chi})}{(k-1)!} \overline{\chi}(g)|g|^{m+it_v}_{F,S} (\log|g|_{F,S})^{k-1} + \sum_{p \in \Pi(S)} \sum_{v \in S_p} \sum_{m \in \mathbf{Z}} \sum_{1 \le k \le m_S(\cdot,c_{v,m,\chi})} \frac{(-1)^{k-1} a_{k-1}(\cdot, c_{v,m,\chi})}{(k-1)!} \overline{\chi}(g)|g|^{-\frac{2\pi i m}{\log(q_v)}+it_v}_{F,S} (\log|g|_{F,S})^{k-1} + O_{A,\mathcal{B}}(|g|^A_{F,S})
$$

the mode of convergence of the infinite sums being pointwise as $g \in J_{F,S}$ satisfies $|g|_{F,S} < 1$, and uniform over the fixed bounded subset $\mathcal{B} \subset \mathcal{S}(\mathbf{A}_{F,S})$. Recall that $\Pi(S)$ denotes the finite set of prime numbers $p$ such that there exists a finite place $v$ in $S$ whose residue characteristic is $p$.

## PDF page 323

**7.1. POLAR MULTIPLICITIES** · **323**

The notation $O_{A,\mathcal{B}}(|g|^A_{F,S})$ means that the function of $g \in J_{F,S}$ defined as the difference of $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)(g)$ and the finite and infinite sums indexed by the places in $S$, is, in absolute value, bounded above by $C_{\mathcal{B},A}|g|^A_{F,S}$ for all $g \in J_{F,S}$ with $|g|_{F,S} < 1$ and uniformly with respect to $f$ varying over the fixed bounded subset $\mathcal{B} \subset \mathcal{S}(\mathbf{A}_{F,S})$.

This uniform form of Theorem 7.1.2.3 is closer to Sarnak's [Sarnak, §0,Thm.1], insofar as it highlights the functional nature of the result. In other words, it concerns the vector-valued Mellin anti-transform of $Z_S(\cdot, c)$, the $S$-idelic zeta function as a vector valued meromorphic function, i.e. we think $Z_S(\cdot, c)$ as a meromorphic function over $\Omega(J_{F,S})$ valued in $\mathcal{S}(\mathbf{A}_{F,S})'_\beta$ (i.e. valued in tempered distributions on $\mathbf{A}_{F,S}$).

The coefficients $a_m(\cdot, c)$ are thus obtained as the vector-valued Laurent coefficients provided by the formulas in Grothendieck's Theorem C.5.3.2, as contour integrals in the sense of Pettis (see (C.5.3.3)). Namely, upon fixing a holomorphic parametrization $\{\chi|\cdot|^s_{F,S}\}$ as in §3.1.1 for the connected component of $\chi$ in $\Omega(J_{F,S})$, for every integer $k \ge 1$ the Laurent coefficient operator $a_k(\cdot, c)$ satisfies

$$
a_{k-1}(\cdot, c) = \frac{1}{2\pi i} \int_\Gamma \frac{Z_S(\cdot, \chi|\cdot|^s_{F,S})}{(s - s_c)^k} \mathrm{d}s
$$

as continuous operators on $\mathcal{S}(\mathbf{A}_{F,S})$, for $s_c$ corresponding to $c$ under the chosen parametrization for any continuously differentiable simple closed curve $\Gamma \subset \mathbf{C}$ enclosing $s_c$.

**7.1.3. Polar Multiplicities.** The following Theorem discusses the multiplicities of the poles of the local Euler factors of the Hecke $L$-function $L(c)$, across the Riemann surface $\Omega(C_F)$.

We refer to quasi-characters of the form

$$
c = \chi_0|\cdot|^s_F
$$

for some $s \in \mathbf{C}$ and for $\chi_0$ of finite order, as quasi-characters of Galois type. If $s \in i\mathbf{R}$, we say $\chi_0|\cdot|^{it}_F$ is a character of Galois type.

*Remark 7.1.3.1.* Let $F$ be a number field, and fix $S_0$ a finite set of finite places of $F$, $\chi$ a continuous character of $C_F$, and $S_\chi$ the finite set of finite places of $F$ at which $\chi$ is ramified.

Let $\varepsilon_p$ denote the arbitrary zero of the holomorphic function on the complex $s$-plane:

$$
\prod_{v|p,\, v \in S_0-(S_0 \cap S_\chi)} (1 - q_v^{-s-it_v})
$$

where $q_v := N(\mathfrak{p}_v)$ is the norm of the prime ideal $\mathfrak{p}_v \subset \mathcal{O}_F$ corresponding to $v$. Since $v \mid p$, $q_v$ is a power of $p$. In particular, $\varepsilon_p$ is always of the form:

$$
\frac{2\pi i k}{\log(q)} - it_v
$$

for $q$ a power of $p$ occurring as $q_v$ for some $v \mid p$ in $S_0$, $k \in \mathbf{Z}$, and $t_v \in \mathbf{R}$ a unique real number such that $t_v \in [0, 2\pi/\log(q))$, and $\chi_v = |\cdot|^{it_v}_v$ as continuous unitary characters of $F_v^\times$.

The highest possible multiplicity of a zero of $\prod_{v|p,\, v \in S_0-(S_0 \cap S_\chi)}(1 - q_v^{-s-it_v})$ is $[F : \mathbf{Q}]$, the degree of the number field over the field of the rational numbers.

This multiplicity is attained if $p$ splits completely in $F$, all finite places $v$ of $F$ over $p$ are contained in $S_0$, $\chi$ is unramified at each such $v$, and $\chi_v(\pi_v) = 1$ for each $v \mid p$, in which case

$$
\prod_{v|p,\, v \in S_0} (1 - q_v^{-s-it_v}) = (1 - p^{-s})^{[F:\mathbf{Q}]}. \tag{7.1.3.1}
$$

For any continuous character $\chi \in \widehat{C_F}$, there exist infinitely many primes $p$ such that $p$ splits completely in $F$ and such that for each $v \mid p$, $\chi$ is unramified at $v$.

## PDF page 324

**324** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

By Chebotarev, the density of the set of prime numbers $p$ such that $p$ splits completely in $F$, is positive. For $\chi$ of the form $\chi_0|\cdot|^{ix}_F$, for some $x \in \mathbf{R}$, with $\chi_0$ of finite order (i.e. for $\chi$ of Galois type), there exist infinitely many prime numbers such that (7.1.3.1) holds for all large enough $S_0$.

We begin to note that the only pole that reciprocal non-Archimedean Euler factors of Hecke $L$-functions are allowed to have in common, is the "origin" of the connected component of $\Omega(C_F)$ parametrized by $\chi|\cdot|^s_F$, at least when $\chi$ is of finite order. Similarly, this remains the case if $\chi$ is of Galois type, i.e. of the form $|\cdot|^{ix_0}_F \chi_0$ for $\chi_0$ of finite order.

This phenomenon is specific to number fields.

We further refer the reader to §14.2, for the differences with the case of global function fields of positive characteristic, where the analog of Theorem 7.1.3.2 below does not hold.

**Theorem 7.1.3.2 (On Polar Multiplicities).** *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.*

*Let $\chi \in \widehat{C_F}$ be a continuous character, unramified outside $S$. Denote by $\chi$ also the unique continuous character of $J_{F,S}$ obtained from the restriction of $\chi$ to $C_{F,S}$, by $\widehat{\mathcal{O}}_{\Sigma_F-S}^{\times}$-invariance.*

*The polar multiplicities of $\rho_S$ on the connected component of $\chi$ in $\Omega(J_{F,S})$ from Lemma 7.1.2.2 satisfy:*

(1) *For $v_1, v_2 \in S$ two finite places with distinct residue characteristics at which $\chi$ is unramified, the local Euler factors $L(\chi_{v_1}|\cdot|^s_{v_1})$ and $L(\chi_{v_2}|\cdot|^s_{v_2})$ of the Hecke $L$-function have at most one pole $s$ in common.*

(2) *For $v$ Archimedean, $m_S(c_{v,0,\chi}) \le |S|$, $m_S(c_{v,m,\chi}) \le r_1+r_2$ if $m$ is a negative even integer, $m_S(c_{v,m,\chi}) \le r_2$ if $m$ is a negative odd integer. (In particular, $m_S(c_{v,m,\chi}) \le [F : \mathbf{Q}]$ for $m < 0$ and Archimedean $v$.)*

(3) *Let $S_0 = S_f - S_\chi$ be the set of finite places in $S$ at which $\chi$ is unramified. If $v \in S_0$ then $m_S(c_{v,m,\chi}) \le |S|$ for all $m$, and as we vary across all such points $c = c_{v,m,\chi} \in \Omega(J_{F,S})(\chi)$ we have $m_S(c) \le [F : \mathbf{Q}]$ with at most $r_1+r_2+|S_0|(|S_0|-1)/2$ exceptions.*

(a) *If $\chi = \chi_0|\cdot|^{ix}_F$ for $x \in \mathbf{R}$ and $\chi_0$ of finite order (i.e., $\chi$ is of Galois type) then the only pole with order exceeding $[F : \mathbf{Q}]$ is $s = -ix$.*

(b) *If $\chi = \chi_0|\cdot|^{s_0}_F$ for $s_0 \in \mathbf{C}$ and $\chi_0$ algebraic then assuming Schanuel's Conjecture the only points in $\Omega(J_{F,S})(\chi)$ where $\rho_S$ can have a pole order exceeding $[F : \mathbf{Q}]$ are the imaginary axis points on the horizontal lines of Archimedean poles and at $s = -\mathrm{Im}(s_0)i$. Unconditionally for such $\chi$, the only point on $\Omega(J_{F,S})(\chi)$ where the pole order can exceed $2[F : \mathbf{Q}]$ is $s = -\mathrm{Im}(s_0)i$.*

*Proof.* (1): If $s$ is a common pole then $\chi_{v_1}(\pi_{v_1})q_{v_1}^{-s} = 1 = \chi_{v_2}(\pi_{v_2})q_{v_2}^{-s}$, so $q_{v_1}^s = \chi_1(\pi_{v_1})$ and $q_{v_2}^s = \chi_2(\pi_{v_2})$ for uniformizers $\pi_{v_k}$ at $v_k$. The condition $q_{v_k}^s = \chi_k(\pi_{v_k})$ determines $s$ up to adding an element of $(2\pi i/\log(q_{v_k}))\mathbf{Z}$. Since $\log(q_{v_k})$ is a positive integer multiple of $\log(p_k)$, so the $\log(q_{v_k})$'s are $\mathbf{Q}$-linearly independent, the two equations $q_{v_k}^s = \chi_{v_k}(\pi_{v_k})$ determine $s$ uniquely (if it exists at all).

(2) Since $\rho_S$ is a product of $|S|$ meromorphic functions whose poles are all simple, it has pole-order at most $|S|$ at any of its poles. In particular $m_S(c_{v,0,\chi}) \le |S|$. The non-Archimedean factors $\rho_v$ have all poles on the imaginary axis in $\Omega(J_{F,S})(\chi)$ (since if $q_v^s = \chi_v(\pi_v) \in U(1)$ then $\mathrm{Re}(s) = 0$), whereas the Archimedean factors $\rho_v$ have poles in the half-plane to the left of that axis.

Consider an Archimedean $v \in S$. If $m$ is a negative even integer then $c_{v,m,\chi}$ has polar multiplicity at most multiplicity the number of Archimedean local factors of $\rho_S$, which is the number $r_1+r_2$ of Archimedean places of $F$. For $m$ odd, $c_{v,m,\chi}$ can only occur as a pole of $\rho_v$ for complex $v$, so its multiplicity as a pole of $\rho_S$ is bounded above by the number $r_2$ of complex places of $F$.

(3). Suppose for some $c_{v,m,\chi}$ with non-Archimedean $v \in S_0 = S_f - S_\chi$, the pole-order of $\rho_S$ exceeds $[F : \mathbf{Q}]$. Since there are at most $[F : \mathbf{Q}]$ places of $F$ with the same residue characteristic $p$ as $v$, for such excess pole order to occur it must also be a pole of $\rho_w$ for some Archimedean $w$ or some non-Archimedean $w$ with residue characteristic different from $p$. If there is a common pole with $\rho_w$ for an Archimedean $w$ then the pole is the rightmost of the Archimedean poles in $\Omega(J_{F,S})(\chi)$. There are at most $r_1+r_2$ horizontal lines on which

## PDF page 325

**7.1. POLAR MULTIPLICITIES** · **325**

the Archimedean local factors have their poles (the number of such distinct lines depends on the infinity-type of $\chi$). Each such line has only its rightmost polar point on the imaginary axis, so setting aside those points (which have meaning independently of $v$), we aim to show at most $|S_0|(|S_0|-1)/2$ such points $c_{v,m,\chi}$ can arise.

There are at most $|S_0|(|S_0|-1)/2$ pairs of places $v, w$ in $S_0$ with distinct residue characteristics, so it suffices to show that for any such pair there is at most one common pole for $\rho_v$ and $\rho_w$. The relation of $\rho_v$ to $L(\chi_v|\cdot|^s_v)$ reduces this "at most one" assertion to (1).

(3.a): We may and do reparameterize the connected component by a pure-imaginary translation so the unitary base point is $\chi = \chi_0$ (i.e., $x = 0$). Suppose $\rho_S$ has pole-order exceeding $[F : \mathbf{Q}]$, so by (2) it occurs as a pole of $\rho_v$ and $\rho_w$ for some non-Archimedean $v$ and some place $w \ne v$ that either is Archimedean or is non-Archimedean with a residue characteristic distinct from $v$. In the case of Archimedean $w$, the pole would have to be at $s = 0$ (as desired) since this is the only pole of an Archimedean local factor which occurs on the imaginary axis (where the non-Archimedean local factors have their poles): the infinity type for finite-order $\chi_0$ puts all Archimedean poles on the same horizontal line.

Thus, we can assume $v, w$ are as in (1), in which case the common pole $s$ satisfies $q_v^s = \chi_0(\pi_v)$ and $q_w^s = \chi_0(\pi_w)$. These character values are roots of unity, so for a sufficiently divisible integer $N > 0$ we have $q_v^{Ns} = 1 = q_w^{Ns}$, forcing $Ns = 0$ (and so $s = 0$, as desired) since $v$ and $w$ have distinct residue characteristics.

(3.b): We may and do reparameterize the connected component by a pure-imaginary translation so the unitary base point is $\chi = \chi_0|\cdot|^{s_0}_F$ with $s_0 \in \mathbf{R}$. If there is a point $c$ at which $\rho_S$ has pole-order exceeding $[F : \mathbf{Q}]$, then as in the argument for (3.a) it occurs as a pole of $\rho_v$ and $\rho_w$ for some non-Archimedean $v$ and some place $w \ne v$ that either is Archimedean or is non-Archimedean with a residue characteristic distinct from $v$. We'll use Schanuel's Conjecture to rule out the possibility of such $v$ and $w$ both non-Archimedean, so then such a common pole would have to be one of the points where the imaginary axis meets the finitely many lines of Archimedean poles.

The condition on $v$ and $w$ implies $q_v^{-s-s_0} \chi_0(\pi_v) = 1 = q_w^{-s-s_0} \chi_0(\pi_w)$ with $s \in i\mathbf{R}$. Since $s_0 \in \mathbf{R}$, if $s \ne 0$ then $\{1, s+s_0\}$ is $\mathbf{Q}$-linearly independent. Since $\log(q_v)$ and $\log(q_w)$ are $\mathbf{Q}$-linearly independent, the Four Exponentials Theorem (a consequence of Schanuel's Conjecture) would imply that one of the numbers $q_v$, $q_w$, $q_v^{s+s_0} = \chi_0(\pi_v)$, or $q_w^{s+s_0} = \chi_0(\pi_w)$ are transcendental. But $\chi_0(\pi_v)$ and $\chi_0(\pi_w)$ are algebraic since $\chi_0$ is an algebraic Hecke character, so this is a contradiction. Thus, necessarily $s = 0$.

Suppose instead there is a pole $c \in \Omega(J_{F,S})(\chi)$ for $\rho_S$ at which the pole-order exceeds $2[F : \mathbf{Q}]$. If this isn't the unique Archimedean pole on the imaginary axis, we can get an unconditional contradiction via the Six Exponentials Theorem (which is unconditional): there would have to be three non-Archimedean places $v, v', v''$ with pairwise distinct residue characteristics such that $q_v^{s+s_0} = \chi_0(\pi_v)$, $q_{v'}^{s+s_0} = \chi_0(\pi_{v'})$, and $q_{v''}^{s+s_0} = \chi_0(\pi_{v''})$ with $s \in i\mathbf{R}$. If $s \ne 0$ then once again $\{1, s+s_0\}$ is $\mathbf{Q}$-linearly independent, as are $\{\log(q_v), \log(q_{v'}), \log(q_{v''})\}$, so now by the Six Exponentials Theorem at least one among $q_v$, $q_{v'}$, $q_{v''}$, $q_v^{s+s_0}$, $q_{v'}^{s+s_0}$, $q_{v''}^{s+s_0}$ is transcendental.

This is again a contradiction, so necessarily $s = 0$.

$\square$

From Theorem 7.1.3.2 and Theorem 7.1.2.3, we deduce the following:

Corollary 7.1.3.3. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing the unique Archimedean place. Let $\chi \in \widehat{J_{F,S}}$, and $f \in \mathcal{S}(\mathbf{A}_{F,S})$. There exists a real number $C > 0$ depending on $S$, $\chi$ and $f$, such that:*

$$
|\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)(g)| \le C_{S,\chi,f} |\log|g|_{F,S}|^{|S|-1} + O_{S,\chi,f}(|\log|g|_{F,S}|^{m-1}) \tag{7.1.3.2}
$$

*for some integer $m < |S|$, and for all $g \in \mathrm{GL}_1(\mathbf{A}_{F,S})$ as $|g|_{F,S} \to 0^+$, where the implied constant in (7.1.3.2) depends on $S$, $\chi$ and $f$, and on the poles of the meromorphic function $\rho_S$ from (3.3.1.3) contained within $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$.*

## PDF page 326

**326** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

*The integer $m \ge 0$ equals the highest order of pole of $Z_S(f,\chi|\cdot|^s_{F,S})$ that is strictly less than the highest order of pole of $Z_S(f,\chi|\cdot|^s_{F,S})$.*

Proof. From Theorem 7.1.2.3 we may choose $A > 0$, and $m = 0$ in (7.1.2.3), calling:

$$
C := \sup_{v\in S}\max_{1\le m\le |S|}\left|\frac{(-1)^{m-1}a_{m-1}(f,\chi|\cdot|^{s_0}_{F,S})}{(m-1)!}\right|
$$

where $s_0$ is the pole of highest order of $Z_S(f,\chi|\cdot|^s_{F,S})$.

The estimate in (7.1.3.2) follows from (7.1.2.3) upon calling $m_0\in\mathbf N$ the smallest integer such that

$$
m_S(f,c)\le m_0
$$

for every pole $c$ of $Z_S(f,c)$ of order less than the order of pole of $\chi|\cdot|^{s_0}_{F,S}$, which, in turn, satisfies $m_0\le |S|$.

$\square$

We refer the reader to Theorem 2.4.2.1, where a version of the estimate from (7.1.3.2), with implied constants that are uniform on bounded subsets, is discussed.

We further refer the reader to [Co, §VII,(6),p.30], where this type of estimates is alluded to, and a lattice-point argument in a similar vein as the proof of Theorem 2.4.2.1 is suggested.

**7.1.4. Spectral bi-orthogonal sequences.** Using Theorem 6.3.2.1, we can now describe the orthogonal of $\mathrm{H}_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))$ within $A\mathcal S(\mathbf C)$ for any $\omega\in \widehat{C^1_F}$.

We denote by $\mathscr{O}(\mathbf C)$ the $\mathbf C$-vector space of all holomorphic functions on the complex $s$-plane, equipped with the Hausdorff locally convex topology of uniform convergence on compact subsets, promoting it to a nuclear Fréchet space.

Situation 7.1.4.1. We choose a continuous homomorphic section $\tau$ to the idelic norm.

We recall that the Mellin transform $Z : \mathcal S_0(\mathbf A_F)\to A\mathcal S(\mathbf C)$ defined as $Z(f,\chi|\cdot|^s_F)$, for $\chi$ varying over a choice of representative continuous characters of $C_F$ for the continuous characters of the compact Hausdorff abelian closed subgroup $C^1_F\subset C_F$, factors through the continuous linear map:

$$
Z : \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))\to A\mathcal S(\mathbf C) \tag{7.1.4.1}
$$

sending $\phi\in \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ to $Z(\phi,s) := \int_{\mathbf R_{>0}}t^{s+ix_0}\phi(\tau(t))\,\frac{\mathrm{d}t}{t}$, i.e. $Z(\phi,s) = Z(f,\chi|\cdot|^s_F)$ for $\phi = \Phi_{F,\chi|_{C^1_F}}(f)$, and $x_0\in\mathbf R$ is the unique real number such that $\chi(\tau(t)) = t^{ix_0}$ as smooth functions of $t\in\mathbf R_{>0}$.

Theorem 7.1.4.2 (Spectral bi-orthogonal sequences). *Let $F$ be a number field, $\chi\in \widehat{C_F}$ a continuous character. We adopt the notation and choices from Situation 7.1.4.1.*

(1) *The orthogonal $Z_\chi$ of the ideal $(s+ix_0)^{\delta_\chi}(1-s-ix_0)^{\delta_\chi}L(s,\chi)\,\mathscr{O}(\mathbf C)\subset\mathscr{O}(\mathbf C)$ with respect to the topology of uniform convergence on compact subsets of the complex $s$-plane, with $\delta_\chi = 1$ if $\chi|_{C^1_F} = 1$, and $\delta_\chi = 0$ otherwise, is linearly and topologically isomorphic to the locally convex product:*

$$
\prod_{\rho:L(\rho,\chi)=0}J_\rho \tag{7.1.4.2}
$$

*where $J_\rho$ is the finite dimensional $\mathbf C$-vector space:*

$$
J_\rho := \bigoplus_{0\le m\le N(\rho)-1}\mathbf C\,\delta^{(m)}_\rho \tag{7.1.4.3}
$$

*where $N(\rho)$ is the multiplicity of $\rho$ as a zero of $L(s,\chi)$, and $\delta^{(m)}_\rho\in\mathscr{O}(\mathbf C)'_\beta$ is the continuous functional:*

$$
\delta^{(m)}_\rho(\phi) := (\partial^m_s\phi)(\rho). \tag{7.1.4.4}
$$

(2) *The continuous linear inclusion operator $A\mathcal S(\mathbf C)\to\mathscr{O}(\mathbf C)$ induces a continuous linear map:*

$$
U : Z_\chi\to \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))^\perp \tag{7.1.4.5}
$$

## PDF page 327

**7.1. POLAR MULTIPLICITIES** · **327**

*where the orthogonal is formed with respect to the duality pairing $\langle\cdot,\cdot\rangle := \langle\cdot\circ L,\cdot\rangle_{ZH,A\mathcal S(\mathbf C)}$, where $ZH$ denotes the image in $A\mathcal S(\mathbf C)$ under the operator $Z$ from (7.1.4.1) of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$. The continuous linear operator $U$ from (7.1.4.5) is injective with dense image, and for every zero of $L(s,\chi)$ and every integer $0\le m\le N(\rho)-1$, we have:*

$$
U(\delta^{(m)}_\rho)(\phi) = \frac{1}{2\pi i}\int_{\mathbf R_{>0}}\left(\int^{+i\infty}_{-i\infty}t^{-s}\phi(s)\,\mathrm{d}s\right)t^{\rho+ix_0}(\log(t))^m\,\frac{\mathrm{d}t}{t}. \tag{7.1.4.6}
$$

(3) *Any enumeration of the set of continuous functionals $\{U(\delta^{(m)}_\rho)\}$, indexed by the pairs $(\rho,m)$ as $\rho$ varies over the zeros of $L(s,\chi)$ and, for each $\rho$, $m$ varies over the integers $0\le m\le N(\rho)-1$, admits a bi-orthogonal sequence in*

$$
\mathscr{H}_F(\chi|_{C^1_F}) := \mathcal S_\mathrm{E}(C_F)(\chi|_{C^1_F})/\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}.\mathcal S_0(\mathbf A_F)) \tag{7.1.4.7}
$$

*In particular, it is topologically free.*

(4) Let:

$$
H_\chi := \left\{\frac{1}{m!}U(\delta^{(m)}_\rho)\right\}_{(\rho,m)} \subset \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))^\perp \tag{7.1.4.8}
$$

*be the set of continuous functionals from (7.1.4.6) of Theorem 7.1.4.2, where $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))^\perp$ is endowed with the strong topology on the continuous dual of the quotient of $\mathcal S(C_F)(\chi|_{C^1_F})$ by $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.*

Then $H_\chi$ is equicontinuous and bounded.

Proof. (1) : By [Bar, Thm.2], we have, for every $s\in\mathbf C$ and upon defining

$$
\Lambda(s,\chi) := \left(\frac{1}{2}(s+ix_0)(s-1-ix_0)\right)^{\delta_\chi}L(s,\chi)
$$

where $\delta_\chi = 0$ if $\chi|_{C^1_F}$ is non-trivial, and $\delta_\chi = 1$ if $\chi|_{C^1_F} = 1$:

$$
\Lambda(s,\chi) = \Lambda(0,\chi)\prod'_{\rho\in\mathbf C:L(\rho,\chi)=0}\left(1-\frac{s}{\rho}\right) \tag{7.1.4.9}
$$

where the convergence of the product on the right side ($\prod'$ meaning that the factors are indexed by the pairs of conjugate zeros, counted with multiplicity, whose imaginary part has absolute value $\le T$, for $T\in\mathbf R_{>0}$, and the product is the limit of the resulting finite products as $T\to +\infty$) is uniform on the compact subsets of the complex $s$-plane (note that in [Bar, Thm.2] the exponent $\delta_\chi$ vanishes if and only if $\chi$ is the principal character: any unitary Hecke character $\chi$ such that $\chi|_{C^1_F} = 1$ is of the form $\chi = |\cdot|^{ix_0}_F$, and hence $\chi|\cdot|^{-ix_0}_F$ is trivial. We are using [Bar, Thm.2] upon replacing $\chi$ with $\chi|\cdot|^{-ix_0}_F$).

The quotient $\mathbf C$-linear space:

$$
\mathscr{O}(\mathbf C)/\Lambda(s,\chi)\,\mathscr{O}(\mathbf C) \tag{7.1.4.10}
$$

is Hausdorff, since $\Lambda(s,\chi)\,\mathscr{O}(\mathbf C)$ is closed in $\mathscr{O}(\mathbf C)$, and it is complete, since $\mathscr{O}(\mathbf C)$ is a Fréchet space, and Hausdorff quotients of Fréchet spaces are complete by [Scha, Ch.I,§6,6.3,p.31].

Its continuous dual is linearly and topologically isomorphic to $Z_\chi$ by [NB, Thm.8.12.1(a)] and [NB, Thm.8.12.2(b)].

We define:

$$
K_\rho := \mathbf C[s]/((1-s/\rho)^{N(\rho)}(1-s/\bar\rho)^{N(\rho)}) \tag{7.1.4.11}
$$

equipped with the Euclidean topology.

## PDF page 328

**328** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

$K_\rho$ is linearly and topologically isomorphic to $\mathscr{O}(\mathbf C)/((1-s/\rho)^{N(\rho)}(1-s/\bar\rho)^{N(\rho)})\,\mathscr{O}(\mathbf C)$. Indeed, calling $I_\rho$ the ideal of holomorphic functions on the complex $s$-plane generated by $((1-s/\rho)^{N(\rho)}(1-s/\bar\rho)^{N(\rho)})$, we have:

$$
I_\rho = (((1-s/\rho)^{N(\rho)}(1-s/\bar\rho)^{N(\rho)})\mathbf C[s])\otimes_{\mathbf C[s]}\mathscr{O}(\mathbf C)
$$

since $\mathscr{O}(\mathbf C)$ is $\mathbf C[s]$-flat as an algebra over $\mathbf C[s]$ (in fact, faithfully flat). This gives injectivity of $K_\rho\to\mathscr{O}(\mathbf C)/I_\rho$.

Since $\mathbf C[s]$ is dense in $\mathscr{O}(\mathbf C)$ by [Cnw-b, Ch.VIII,Cor.1.15,p.200], then $K_\rho$ is dense in $\mathscr{O}(\mathbf C)/I_\rho$, being the quotient maps $\mathbf C[s]\to K_\rho$ and $\mathscr{O}(\mathbf C)\to\mathscr{O}(\mathbf C)/I_\rho$ open. Since $K_\rho$ is finite dimensional, it carries the subspace topology inherited from $\mathscr{O}(\mathbf C)/I_\rho$, which is the Euclidean topology, being $K_\rho$ finite dimensional. Being $K_\rho$ complete, the map $K_\rho\to\mathscr{O}(\mathbf C)/I_\rho$ is surjective.

As a $\mathbf C$-vector space, the quotient $\mathscr{O}(\mathbf C)/\Lambda(s,\chi)\,\mathscr{O}(\mathbf C)$ is linearly isomorphic to the countable product of the $K_\rho$, i.e. to $\prod_{\rho\in\mathbf C:L(\rho,\chi)=0}K_\rho$.

To see this, we note that since $\mathbf C$ is Stein, then upon denoting by $\mathscr{J}\subset\mathscr{O}$ the ideal sheaf globally generated by $\Lambda(s,\chi)$, we have

$$
\check{\mathrm{H}}(\mathbf C,\mathscr{O}/\mathscr{J}) = \mathrm{H}^1(\mathbf C,\mathscr{O}/\mathscr{J}) = 0
$$

and hence upon choosing a locally finite countable open cover $\{B_m\}_{m\ge 0}$ of the complex $s$-plane by open balls each of which contains at most one of the zeros $\rho$ of $L(s,\chi)$, then, upon denoting by $B_{\underline{k}}$ the intersection $\bigcap_{m\in \underline{k}}B_m$ for $\underline{k}$ varying over all non-empty finite subsets of the nonnegative integer, we deduce that $\mathrm{H}^0(B_{\underline{k}},\mathscr{J})$ is trivial if $\underline{k}$ contains at least two elements, and it is either trivial or $K_\rho$ if $\underline{k}$ contains one element exactly. This computes

$$
\mathscr{O}(\mathbf C)/\Lambda(s,\chi)\,\mathscr{O}(\mathbf C) = \check{\mathrm{H}}^0(\mathbf C,\mathscr{O}/\mathscr{J})
$$

to be $\prod_{\rho:L(\rho,\chi)=0}K_\rho$. The quotient topology $\mathscr{O}(\mathbf C)/\Lambda(s,\chi)\,\mathscr{O}(\mathbf C)$ is the product topology, since any compact subset $K\subset\mathbf C$ is contained in the union of at most finitely many of the $B_m$, and hence the linear bijection $\mathscr{O}(\mathbf C)/\Lambda(s,\chi)\,\mathscr{O}(\mathbf C)\to\prod_{\rho:L(\rho,\chi)=0}K_\rho$ is continuous. Being source and target Fréchet spaces, it is a linear topological isomorphism by [NB, Thm.14.4.5(b)].

To compute the orthogonal of $\Lambda(s,\chi)\,\mathscr{O}(\mathbf C)$ it is therefore enough to compute the continuous dual of $\prod_{\rho\in\mathbf C:L(\rho,\chi)=0}\mathbf C[s]/(s-\rho)^{N(\rho)}$ with respect to the product topology: by [Tre, Part II,Ch.22,Thm.22.1(b)], this is exactly the locally convex direct sum of the finite dimensional $\mathbf C$-vector spaces:

$$
H_\rho := \bigoplus_{0\le m\le N(\rho)-1}\mathbf C\,D^m_\rho
$$

where $D^m_\rho$ is the composition of the formal $m$th derivative on polynomials in $\mathbf C[s]$ followed by the evaluation-at-$\rho$ of the resulting polynomial function of $s\in\mathbf C$.

Each such functional $D^m_\rho$ is the image of $\delta^{(m)}_\rho$ under the linear isomorphism $Z_\chi = (\Lambda(s,\chi)\,\mathscr{O}(\mathbf C))^\perp\to (\prod_{\rho\in\mathbf C:L(\rho,\chi)=0}\mathbf C[s]/(s-\rho)^{N(\rho)})'$, which provides the desired description of $Z_\chi$ as a $\mathbf C$-vector space.

The subspace topology on $(\Lambda(s,\chi)\,\mathscr{O}(\mathbf C))^\perp$ inherited from the strong topology on $\mathscr{O}(\mathbf C)'_\beta$ promotes the continuous linear bijection $(\Lambda(s,\chi)\,\mathscr{O}(\mathbf C))^\perp\to (\prod_{\rho\in\mathbf C:L(\rho,\chi)=0}\mathbf C[s]/(s-\rho)^{N(\rho)})'_\beta$ to a linear topological isomorphism.

(2) : Since every element $\phi\in A\mathcal S(\mathbf C)$ is the Mellin transform of some Schwartz-Bruhat function $f\in\mathcal S(\mathbf R_{>0})$ with exponential decay (i.e. such that $f$ decays more rapidly than any positive power of $e^{-|\log(t)|}$ as $|\log(t)|\to +\infty$, see Definition B.2.1.1), and we have, by Fourier Inversion:

$$
f(t) = \frac{1}{2\pi i}\int^{+i\infty}_{-i\infty}t^{-s}\phi(s)\,\mathrm{d}s
$$

## PDF page 329

**7.1. POLAR MULTIPLICITIES** · **329**

then we compute:

$$
\delta^{(m)}_\rho(\phi) = (\partial^m_s\phi)(\rho) = \left(\partial^m_s\int_{\mathbf R_{>0}}f(t)t^s\,\frac{\mathrm{d}t}{t}\right)|_{s=\rho} = \left(\int_{\mathbf R_{>0}}f(t)t^s(\log(t))^m\,\frac{\mathrm{d}t}{t}\right)|_{s=\rho} = \frac{1}{2\pi i}\int_{\mathbf R_{>0}}\left(\int^{+i\infty}_{-i\infty}t^{-s}\phi(s)\,\mathrm{d}s\right)t^\rho(\log(t))^m\,\frac{\mathrm{d}t}{t}
$$

and hence (7.1.4.6) holds. Denseness of the range of $U$ follows from the observation that, by Theorem 6.3.2.1(1), the functionals $U(\delta^{(m)}_\rho)$ separate the points of $A\mathcal S(\mathbf C)/\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

(3) : We consider, for $\rho$ a zero of $\Lambda(s,\chi)$, of multiplicity $N(\rho)$, and for $m$ an integer such that $0\le m\le N(\rho)-1$, the meromorphic function on the complex $s$-plane:

$$
\phi_{\rho,m}(s) := \frac{1}{(s-\rho)^{N(\rho)-m}}\Lambda(s,\chi). \tag{7.1.4.12}
$$

Since $0\le m\le N(\rho)-1$, then $\phi_{\rho,m}$ has only removable singularities. We let $\widetilde{\phi}_{\rho,m}$ be the unique holomorphic extension of $\phi_{\rho,m}$ to the complex $s$-plane, and rename it as $\phi_{\rho,m}$.

Since $\rho$ can be located within the vertical strip $\mathbf C_{[0,1]}$ only, we may fix an arbitrary real number $\varepsilon > 0$ and an integer $N\ge 0$, and consider the two line integrals, for $s\in\mathbf C_{(0,1)}$:

$$
\frac{1}{2\pi i}\int^{-\varepsilon+i\infty}_{-\varepsilon-i\infty}\frac{z^N\phi_{\rho,m}(z)}{z-s}\,\mathrm{d}z,\quad \frac{1}{2\pi i}\int^{\varepsilon+i\infty}_{\varepsilon-i\infty}\frac{z^N\phi_{\rho,m}(z)}{z-s}\,\mathrm{d}z. \tag{7.1.4.13}
$$

Since $\phi_{\rho,m}$ is entire, by the Asymptotic Residue Theorem (see Theorem B.3.2.1), which applies since $z^N(z-\rho)^{m-N(\rho)}/(z-s)$ is meromorphic and with slow growth near its poles (see Definition B.3.1.1), and $\Lambda(s,\chi)$ decays faster than any positive power of $|s|^{-1}$ uniformly over the vertical strips of bounded width of the complex $s$-plane, we obtain:

$$
|s^N\phi_{\rho,m}(s)|\le \frac{1}{2\pi}\int^{-\varepsilon+i\infty}_{-\varepsilon-i\infty}\left|\frac{z^N\phi_{\rho,m}(z)}{z-s}\right||\mathrm{d}z| + \frac{1}{2\pi}\int^{\varepsilon+i\infty}_{\varepsilon-i\infty}\left|\frac{z^N\phi_{\rho,m}(z)}{z-s}\right||\mathrm{d}z| \tag{7.1.4.14}
$$

$$
= \frac{1}{2\pi}\int^{+\infty}_{-\infty}\frac{|-\varepsilon+iy|^N|\phi_{\rho,m}(-\varepsilon+iy)|}{|-\varepsilon+iy-s|}\,\mathrm{d}y + \frac{1}{2\pi}\int^{+\infty}_{-\infty}\frac{|\varepsilon+iy|^N|\phi_{\rho,m}(\varepsilon+iy)|}{|\varepsilon+iy-s|}\,\mathrm{d}y \tag{7.1.4.15}
$$

$$
= \frac{1}{2\pi}\int^{+\infty}_{-\infty}\frac{|-\varepsilon+iy|^N|\Lambda(-\varepsilon+iy,\chi)|}{|-\varepsilon+iy-s||-\varepsilon+iy-\rho|^{N(\rho)-m}}\,\mathrm{d}y \tag{7.1.4.16}
$$

$$
+ \frac{1}{2\pi}\int^{+\infty}_{-\infty}\frac{|\varepsilon+iy|^N|\Lambda(\varepsilon+iy,\chi)|}{|\varepsilon+iy-s||\varepsilon+iy-\rho|^{N(\rho)-m}}\,\mathrm{d}y \tag{7.1.4.17}
$$

and since both $s$ and $\rho$ are within $\mathbf C_{[0,1]}$, and $\Lambda(s,\chi)$ decays faster than any positive power of $|s|^{-1}$ uniformly over the vertical strip $\mathbf C_{[-\varepsilon,1+\varepsilon]}$, and hence in particular on the vertical lines $\mathrm{Re}(s) = -\varepsilon$ and $\mathrm{Re}(s) = 1+\varepsilon$, both integrals in (7.1.4.17) converge and their value is bounded above by a positive real number that depends on $N\ge 0$ but not on $s$ (since $\varepsilon > 0$ and $s$ is constrained to vary over $\mathbf C_{[0,1]}$).

The same argument shows that the holomorphic derivatives of $\phi_{\rho,m}$ of any order also decay faster than any positive power of $|s|^{-1}$ as $|s|\to +\infty$ uniformly over the vertical strips of bounded width of the complex $s$-plane.

In particular, $\phi_{\rho,m}$ is an element of $A\mathcal S(\mathbf C)$ for every $(\rho,m)$, with $\rho$ a zero of $L(s,\chi)$, and $m$ an integer such that $0\le m\le N(\rho)-1$.

## PDF page 330

**330** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

They satisfy the following vanishing conditions:

$$
U(\delta^m_\rho)(\phi_{(\rho',m')}) = 0 \tag{7.1.4.18}
$$

if $\rho'\ne\rho$ and $m'$ is an integer such that $0\le m'\le N(\rho')-1$, or if $\rho' = \rho$ and $m'$ is an integer such that $0\le m\le m'-1$, and

$$
U(\delta^m_\rho)(\phi_{(\rho',m')})\ne 0 \tag{7.1.4.19}
$$

if $\rho' = \rho$ and $m'\le m\le N(\rho)-1$.

We know from (1) and (2) that the functionals $\{U(\delta^{(m)}_\rho)\}_{(\rho,m)}$ are linear topological generators of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))^\perp$.

Indeed, the continuous linear injection $A\mathcal S(\mathbf C)\to\mathscr{O}(\mathbf C)$ has dense range, because both $A\mathcal S(\mathbf C)$ and $\mathscr{O}(\mathbf C)$ are reflexive, and hence [NB, Thm.8.10.6(e)] applies to its adjoint.

Let $\{c_{(\rho,m)}\}_{(\rho,m)}$ and $\{c'_{(\rho,m)}\}_{(\rho,m)}$ be two countable nets of complex numbers such that the following two series converge in $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))^\perp$ with respect to the topology of uniform convergence on bounded subsets, with same sum:

$$
\sum_{(\rho',m')}c_{(\rho',m')}U(\delta^{(m')}_{\rho'}) = \sum_{(\rho',m')}c'_{(\rho',m')}U(\delta^{(m')}_{\rho'}). \tag{7.1.4.20}
$$

Since the convergence is with respect to the strong topology, evaluation at $\phi_{\rho,m}$ is a continuous functional on $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))^\perp$ equipped with this topology, and we may therefore evaluate each series in (7.1.4.20) term by term, to obtain the finite sums:

$$
\sum_{(\rho',m'):\rho'=\rho,m\le m'\le N(\rho)-1}c_{(\rho',m')}U(\delta^{(m')}_{\rho'}) = \sum_{(\rho',m'):\rho'=\rho,m\le m'\le N(\rho)-1}c'_{(\rho',m')}U(\delta^{(m')}_{\rho'})
$$

and since the $U(\delta^{(m')}_{\rho'})$ are $\mathbf C$-linearly independent, we obtain $c_{(\rho,m)} = c'_{(\rho,m)}$ for all pairs $(\rho,m)$.

This implies that for any enumeration of the pairs $(\rho,m)$, the resulting sequence of functionals $\{U(\delta^{(m)}_\rho)\}$ is topologically free within $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))^\perp$ (since it admits a bi-orthogonal sequence, which can, in light of the foregoing, be constructed by replacing each $\phi_{(\rho,m)}$ with a finite linear combination of the finitely many elements $\phi_{(\rho,m')}$ as $m'$ varies over the integers $0\le m'\le N(\rho)-1$; see [Jar, Part II,Ch.14,§14.1,Prop.1,p.290]).

(4) : Let $\phi\in\mathcal S_\mathrm{E}(C_F)(\chi|_{C^1_F})$ be an arbitrary element. Since $\phi$ has exponential decay (see Definition D.3.3.1), its Mellin transform:

$$
\Phi(s) := \int_{C_F}\phi(g)\chi(g)|g|^s_F\,\mathrm{d}\overline{\mu}(g)
$$

is entire and Schwartz uniformly over each vertical strip of bounded width of the complex $s$-plane. In particular, the set of values of $\Phi$ over the vertical strip $\mathbf C_{(-\varepsilon,1+\varepsilon)}$, for any fixed real number $\varepsilon > 0$, is bounded with respect to the Euclidean topology.

We have, by the Asymptotic Residue Theorem (see Theorem B.3.2.1):

$$
-\frac{k!}{2\pi i}\int^{-\varepsilon+i\infty}_{-\varepsilon-i\infty}\frac{\Phi(z)}{(z-s)^{k+1}}\,\mathrm{d}z + \frac{k!}{2\pi i}\int^{\varepsilon+i\infty}_{\varepsilon-i\infty}\frac{\Phi(z)}{(z-s)^{k+1}}\,\mathrm{d}z = \Phi^{(k)}(s) \tag{7.1.4.21}
$$

for every $s\in\mathbf C_{[0,1]}$ and every $\varepsilon > 0$. From (7.1.4.21) we obtain the estimate:

$$
|\Phi^{(k)}(s)|\le \frac{k!}{2\pi\varepsilon^{k+1}}\left\{\int^{-\varepsilon+i\infty}_{-\varepsilon-i\infty}|\Phi(z)|\,|\mathrm{d}z| + \int^{\varepsilon+i\infty}_{\varepsilon-i\infty}|\Phi(z)|\,|\mathrm{d}z|\right\} \tag{7.1.4.22}
$$

which implies that, for all $s\in\mathbf C_{[0,1]}$, we have, upon choosing $\varepsilon = 1$:

$$
\left|\frac{\Phi^{(k)}(s)}{k!}\right|\le \frac{1}{2\pi}\max\{\|\Phi\|_{L^1(-1+i\mathbf R,\mathrm{d}x)},\|\Phi\|_{L^1(2+i\mathbf R,\mathrm{d}x)}\}.
$$

## PDF page 331

**7.1. POLAR MULTIPLICITIES** · **331**

This implies that the subset $H_\chi\subset\mathcal S_\mathrm{E}(C_F)(\chi|_{C^1_F})'_\beta$ is simply bounded, hence bounded by [Scha, Ch.III,§3,Corollary,p.82], since $\mathcal S_\mathrm{E}(C_F)(\chi|_{C^1_F})'_\beta$ is complete.

By [Scha, Ch.III,§4,Thm.4.2,p.83], since $\mathcal S_\mathrm{E}(C_F)(\chi|_{C^1_F})$ is barrelled, being a Fréchet space, it is equicontinuous.

$\square$

The following extension of Theorem 7.1.4.2 incorporates the inversion of finitely many Euler factors of the Hecke $L$-function.

Theorem 7.1.4.3 (Global Orbital bi-orthogonal sequences). *Let $F$ be a number field, $\chi\in \widehat{C_F}$ a unitary character. Let $S_\chi$ be the finite set of finite places of $F$ at which $\chi$ is ramified. Let $S_0$ be a finite set of finite places of $F$.*

(1) *The orthogonal $Z_{S_0,\chi}$ of the ideal*

$$
\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)(s+it_0)^{\delta_\chi}(1-s-it_0)^{\delta_\chi}L(s,\chi)\,\mathscr{O}(\mathbf C)\subset\mathscr{O}(\mathbf C)
$$

*with respect to the topology of uniform convergence on compact subsets of the complex $s$-plane, with $\delta_\chi = 1$ if $\chi|_{C^1_F} = 1$, and $\delta_\chi = 0$ otherwise, is linearly and topologically isomorphic to the locally convex product:*

$$
\prod_{p:(p,S_0)\ne 1}J_{S_0,p}\times\prod_{\rho:L(\rho,\chi)=0}J_\rho \tag{7.1.4.23}
$$

*where $J_\rho$ is the finite dimensional $\mathbf C$-vector space from (7.1.4.3), where $(p,S_0)\ne 1$ denotes the condition on the prime number $p$, of some $v\in S_0$ existing such that $v\mid p$, and $J_p$ is the finite dimensional $\mathbf C$-vector space:*

$$
J_{S_0,p} := \bigoplus_{0\le m\le N(\varepsilon_p)-1}\delta^{(m)}_{\varepsilon_p} \tag{7.1.4.24}
$$

*where $\varepsilon_p$ varies over the zeros of $\prod_{v\mid p,v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)$, $N(\varepsilon_p)$ is the zero-multiplicity of $\varepsilon_p$, and $\delta^{(m)}_{\varepsilon_p}\in\mathscr{O}(\mathbf C)'_\beta$ is the continuous functional:*

$$
\delta^{(m)}_{\varepsilon_p}(\phi) := (\partial^m_s\phi)(\varepsilon_p). \tag{7.1.4.25}
$$

(2) *The continuous linear operator $A\mathcal S(\mathbf C)\to\mathscr{O}(\mathbf C)$ induces a continuous linear map:*

$$
U : Z_{S_0,\chi}\to (\mathrm{PV}_{S_0}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)))^\perp \tag{7.1.4.26}
$$

*where the orthogonal is formed with respect to the duality pairing $\langle\cdot,\cdot\rangle := \langle\cdot\circ L,\cdot\rangle_{ZH,A\mathcal S(\mathbf C)}$, where $ZH$ denotes the image in $A\mathcal S(\mathbf C)$ under $Z$ of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.*

*The continuous linear operator $U$ from (7.1.4.26) is injective with dense image, and for every zero $z$ of either $L(s,\chi)$ or $\prod_{v\mid p,v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)$, and every integer $0\le m\le N(z)-1$, we have:*

$$
U(\delta^{(m)}_z)(\phi) = \frac{1}{2\pi i}\int_{\mathbf R_{>0}}\left(\int^{+i\infty}_{-i\infty}t^{-s}\phi(s)\,\mathrm{d}s\right)t^z(\log(t))^m\,\frac{\mathrm{d}t}{t}. \tag{7.1.4.27}
$$

(3) *Any enumeration of the countable subset $\{U(\delta^{(m)}_z)\}_{(z,m)}$ in $(\mathrm{PV}_{S_0}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)))^\perp$ equipped with strong topology of the quotient topology on the quotient of $\mathcal S(C_F)(\chi|_{C^1_F})$ by $\mathrm{PV}_{S_0}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$ as $z$ varies over the zeros of $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q^{-s-it_v}_v)L(s,\chi)$, and, for each such $z$, $m$ is an integer satisfying $0\le m\le N(z)-1$, admits a bi-orthogonal sequence in*

$$
\mathscr{E}_{F,S_0}(\chi|_{C^1_F}) := \mathcal S_\mathrm{E}(C_F)(\chi|_{C^1_F})/\mathrm{PV}_{S_0}\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F)). \tag{7.1.4.28}
$$

*In particular, it is a topologically free set.*

## PDF page 332

**332** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

PROOF. The argument for both (1) and (2) is formally analogous to that for (1) and (2) from Theorem 7.1.4.2, with only one additional input: the non-vanishing of $L(s,\chi)$ on the vertical lines $\mathrm{Re}(s)=0,1$, which is required to ensure that no zero of $L(s,\chi)$ is also a zero of $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q_v^{-s-it_v})$. This property of $L(s,\chi)$ is logically equivalent to the Prime Number Theorem (in its general form for Hecke $L$-functions) and is proved in [CF, Ch.VIII,Thm.2].

(3) : The argument is closely analogous to that for (3) from Theorem 7.1.4.2, upon replacing $L(s,\chi)$ with $\prod_{v\in S_0-(S_0\cap S_\chi)}(1-q_v^{-s-it_v})L(s,\chi)$, and upon constructing additional functions $\phi_{\varepsilon_p,m}$ for $\varepsilon_p$ varying among the zeros of $\prod_{v\in S_0-(S_0\cap S_\chi),v\mid p}(1-q_v^{-s-it_v})$ for each rational prime $p$ in a manner similar to that of $\phi_{\rho,m}$ from (7.1.4.12), to test any topological linear dependence relation among the functionals $U(\delta^{(m)}_z)$ and deduce its triviality. By [Jar, Part II,Ch.14,§14.1,Prop.1,p.289], any enumeration of the countable set $\{U(\delta^{(m)}_z)\}$ is topologically free. $\square$

**7.2. Poles of the $S$-idelic Zeta functions**

Let $X$ be a Riemann surface, $D\subset X$ a divisor. The following is a short exact sequence of sheaves of $\mathscr{O}_X$-modules, the sheaf of holomorphic functions on $X$:

$$
0\to\mathscr{O}_X(-D)\to\mathscr{O}_X\to\mathscr{O}_D\to 0 \tag{7.2.0.1}
$$

and if $X$ is Stein, then $\mathrm{H}^m(X,\mathscr F)=0$ for all integers $m>0$ and for any coherent analytic sheaf of $\mathscr{O}_X$-modules $\mathscr F$, which leads to the exact sequence of global sections:

$$
0\to\mathscr{O}_X(-D)\to\mathscr{O}_X\to\mathscr{O}_D\to 0.
$$

Twisting by $\mathscr{O}_X(D)$, we further obtain the short exact sequence of sheaves of $\mathscr{O}_X$-modules:

$$
0\to\mathscr{O}_X\to\mathscr{O}_X(D)\to\mathscr P_{X,D}\to 0 \tag{7.2.0.2}
$$

where $\mathscr P_{X,D}$ is the sheaf of principal parts.

The $\mathbf C$-linear spaces of global sections involved can be topologized so as to render the above short exact sequences strict exact. We refer to (7.2.0.1) and to (7.2.0.2) as the *divisor exact sequence* and the *principal parts exact sequence*, respectively.

We refer the reader to work of Grosse-Erdman on topologizing spaces of meromorphic functions, focusing on the Hausdorff locally convex topologies on spaces of meromorphic functions, and comparing the topology induced by combining the topology of uniform convergence on compact subsets for holomorphic functions, with the product topology on Euclidean lines generated by principal parts, termed Mittag-Leffler topology, with other Hausdorff locally convex topologies on spaces of meromorphic functions on complex domains: the standard topology inherited from the topology of uniform convergence on compact subsets for holomorphic functions on complex domains (an inductive topology by nature), and the Holdgründ topology, a projective topology obtained by writing spaces of meromorphic functions on complex domains as projective limits of spaces of holomorphic functions up to rational functions obtained as principal parts.

We refer the reader to [GE, §3.2], as well as to [Jor-a, §3], for vector-valued analogs, and particularly to [Jor-a, Thm.3.6].

**7.2.1. Principal parts.** Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

We recall from Theorem 3.3.1.1 that the $S$-local Mellin transform operator:

$$
Z_S:\mathcal S(\mathbf A_{F,S})\to\mathscr M(\Omega(J_{F,S}))
$$

## PDF page 333

**7.2. POLES OF THE $S$-IDELIC ZETA FUNCTIONS** · **333**

from (5.1.1.2), factors through $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, and for any Schwartz-Bruhat function $f\in\mathcal S(\mathbf A_{F,S})$, the meromorphic function $Z_S(f,c)$ of $c\in\Omega(J_{F,S})$ satisfies the functional equation:

$$
Z_S(f,c)=\rho_S(c)Z_S(\widehat f,\widehat c) \tag{7.2.1.1}
$$

for which we refer the reader to (3.3.1.2).

Recall that $\mathscr M(\Omega(J_{F,S}))$ denotes the $\mathbf C$-linear space of meromorphic functions on the Riemann surface $\Omega(J_{F,S})$ with poles located within the subset $\mathcal{U}_S$ of $\Omega(J_{F,S})$ of the poles of $\rho_S(c)$ from (3.3.1.3).

Recall that $\widehat f$ is the $S$-adelic Fourier transform, which we defined using the standard additive character of $\mathbf A_{F,S}$, and that $\rho_S(c)$ is the meromorphic function on $\Omega(J_{F,S})$ defined in (3.3.1.3) as:

$$
\rho_S(c):=\prod_{v\in S}\rho_v(c_v) \tag{7.2.1.2}
$$

where $\rho_v$ is the meromorphic function on $\Omega(F_v^\times)$ defined in [CF, Ch.XV,§2.5] for each $v\in S$.

We further recall that $Z_S(f,c)$ is holomorphic over the relative half-surface $\Omega(J_{F,S})_{>0}$, as is $Z(\widehat f,c)$, and so the functional equation (7.2.1.1) extends $Z_S(f,c)$ to a meromorphic function over $\Omega(J_{F,S})$ whose only poles are located at the poles of $\rho_S(c)$ (possibly with lower order of pole).

The location and order of the poles of $\rho_S(c)$ was described in Lemma 7.1.2.2 and Theorem 7.1.3.2.

We established, using input from the theory of almost periodic functions and the Asymptotic Residue Theorem (see Theorem B.3.2.1), that for any $f\in\mathcal S(\mathbf A_{F,S})$, the continuous function $\Phi_{F,S,\omega}(f)$ on $J_{F,S}$ satisfies the following asymptotic expansion.

For any continuous character $\chi\in\widehat{J_{F,S}}$, we have, for any real number $A>0$ and upon denoting by $S_\chi$ the subset of $S$ of those places in $S$ at which $\chi$ is ramified:

$$
\Phi_{F,S,\chi\mid_{J^1_{F,S}}}(f)(g)=\sum_{v\in S_\infty}\sum_{m\in\mathbf N_{>0},m<A}\sum_{1\le k\le m_S(f,c_{v,m,\chi})}\frac{(-1)^{k-1}a_{k-1}(f,c_{v,m,\chi})}{(k-1)!}\overline\chi(g)\lvert g\rvert_{F,S}^{m+it_v}(\log\lvert g\rvert_{F,S})^{k-1} \tag{7.2.1.3}
$$

$$
+\sum_{p\in\Pi(S)}\sum_{v\in S_p}\sum_{m\in\mathbf Z}\sum_{1\le k\le m_S(f,c_{v,m,\chi})}\frac{(-1)^{k-1}a_{k-1}(f,c_{v,m,\chi})}{(k-1)!}\overline\chi(g)\lvert g\rvert_{F,S}^{-\frac{2\pi im}{\log(q_v)}+it_v}(\log\lvert g\rvert_{F,S})^{k-1} \tag{7.2.1.4}
$$

$$
+O(\lvert g\rvert_{F,S}^A) \tag{7.2.1.5}
$$

as $\lvert g\rvert_{F,S}\to 0^+$, where $q_v$ is the norm of the prime ideal $\mathfrak p_v$ corresponding to the finite place $v$ of $F$, the series converges uniformly on the compact subsets of $J_{F,S}$, the implied constant depends only on the restriction of the meromorphic function $Z_S(f,c)$ on the vertical line $\chi\lvert\cdot\rvert_{F,S}^{-A+i\mathbf R}$ within $\Omega(J_{F,S})(\omega)$, and where $c_{v,m,\chi}$ is a pole of $\rho_S(c)$, as described in Lemma 7.1.2.2 according to the chosen parametrization of $\Omega(J_{F,S})(\omega)$.

In this subsection we reprise the study of the Mellin transform of $\Phi_{F,S,\chi\mid_{J^1_{F,S}}}(f)$, by discussing continuity properties of the coefficients $a_k(f,c)$ for all integers $k\ge 0$, as $c$ varies over all the poles of $\rho_S(c)$, and as $f$ varies over all Schwartz-Bruhat functions in $\mathcal S(\mathbf A_{F,S})$.

They will turn out to be $S$-local eigendistributions (see Definition 5.5.1.1, and Theorem 5.5.1.2 for their classification), which is the content of Theorem 7.2.1.1 below.

In the last subsection, we will use the eigendistributions $a_k(\cdot,c)$ to describe the orthogonals within the strong dual $\mathrm H_{0,\mathrm{cont}}(\chi\mid_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))'_\beta$ of certain closed subspaces of $\mathrm H_{0,\mathrm{cont}}(\chi\mid_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$, and the functionals $\{a_k(\cdot,c)\}$ will provide Schauder bases for such orthogonals, equipped with the strong topology on the continuous dual of the quotient of $\mathrm H_{0,\mathrm{cont}}(\chi\mid_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ by the such closed subspace (we refer the reader to Lemma 4.2.1.3 on strong adjoints to quotient maps).

THEOREM 7.2.1.1 (Coefficients of Principal Parts). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $m\ge 0$ be an integer.*

## PDF page 334

**334** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

*(1) Formation of $a_m(f,c)$ is continuous with respect to $f\in\mathcal S(\mathbf A_{F,S})$.*

*(2) The tempered distribution $a_m(\cdot,c)\in\mathcal S(\mathbf A_{F,S})'_\beta$ factors through $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, through its $\omega$-isotype for $\omega=c\mid_{J^1_{F,S}}$. It is an $S$-local eigendistribution of weight $c\in\Omega(J_{F,S})$.*

*(3) If $a_m(\cdot,c)$ is nonzero, then $c\in\mathcal{U}_S$ and $m\le m_S(f,c)$ for all $f\in\mathcal S(\mathbf A_{F,S})$.*

*(4) Let $\omega\in\widehat{J^1_{F,S}}$ be a continuous character. Let $\mathcal{U}\subset\mathcal{U}_S$ be a subset, $m:\mathcal{U}_S\to\mathbf N$ a function supported on $\mathcal{U}$. Let $\mathcal{U}(\omega)$, respectively $\mathcal{U}_S(\omega)$, denote the intersections with the connected component $\Omega(J_{F,S})(\omega)$. The linear subspace:*

$$
H_m(\omega,\mathcal S(\mathbf A_{F,S}))\subset\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})) \tag{7.2.1.6}
$$

*linearly generated by those elements $\Phi_{F,S,\omega}(f)$ such that $Z_S(f,c)$ has poles with order of pole $m_S(f,c)\le m(c)$, is closed, and the orthogonal $H_m(\omega,\mathcal S(\mathbf A_{F,S}))^\perp$ with respect to the duality*

$$
\langle\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})),\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))'_\beta\rangle
$$

*is linearly and topologically generated by the $S$-local eigendistributions:*

$$
\{a_k(\cdot,c):c\in\mathcal{U}_S(\omega),k>m(c)\}. \tag{7.2.1.7}
$$

PROOF. (1) : By the $S$-local functional equation (see (3.3.1.2) from Theorem 3.3.1.1), we have:

$$
Z_S(f,c)=\rho_S(c)Z_S(\widehat f,\widehat c)
$$

for all $f\in\mathcal S(\mathbf A_{F,S})$, and formation of both sides is continuous with respect to the Schwartz-Bruhat topology on $\mathcal S(\mathbf A_{F,S})$ by Lemma 5.1.3.1 for each fixed $c$, and also upon endowing the linear space $\mathscr M(\Omega(J_{F,S}))$ with the topology of uniform convergence on the compact subsets of $\Omega(J_{F,S})-\mathcal{U}_S$.

We now choose a holomorphic parametrization $\chi\lvert\cdot\rvert_{F,S}^s$, $s\in\mathbf C$, for $\Omega(J_{F,S})$, i.e. a set of base points, equivalently representatives, $\chi\in\widehat{J_{F,S}}$ for the continuous characters $\omega\in\widehat{J^1_{F,S}}$, which parametrize the connected components of $\Omega(J_{F,S})$.

Let $c_0\in\mathcal{U}_S$ be a point, and we parametrize it as $c_0=\chi_0\lvert\cdot\rvert_{F,S}^{s_0}$ for a unique base point $\chi_0$ and a unique point $s_0\in\mathbf C$.

Formation of $a_m(f,c)$ is therefore continuous with respect to the Schwartz-Bruhat topology on $\mathcal S(\mathbf A_{F,S})$, since we may write, by Cauchy's Integral Formula:

$$
a_m(f,c_0)=\frac{1}{2\pi i}\int_\Gamma\frac{(s-s_0)^mZ_S(f,\chi\lvert\cdot\rvert_{F,S}^s)}{s-s_0}\,\mathrm{d}s \tag{7.2.1.8}
$$

for any closed rectifiable curve $\Gamma\subset\mathbf C$ containing $s_0$ within the unique bounded domain of $\mathbf C$ whose boundary is $\Gamma$, and formation of the integral in the right side of (7.2.1.8) is continuous.

(2) : Since $a_m(f,c_0)$, in light of (7.2.1.8), depends on $f$ only through $Z_S(f,c)$ as a meromorphic function of $c\in\Omega(J_{F,S})$, then by Lemma 5.1.2.2, then $a_m(\cdot,c_0)$ annihilates the kernel of $\Phi_{F,S,\omega_0}$, for $\omega_0=c_0\mid_{J^1_{F,S}}=\chi_0\mid_{J^1_{F,S}}$. Since this holds for all $c_0\in\mathcal{U}_S$, we deduce that $a_m(\cdot,c)$ factors through $\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$, and in fact through its quotient $\mathrm H_{0,\mathrm{cont}}(c\mid_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$. $c$-homogeneity of $a_m(\cdot,c)$ follows from $c$-homogeneity of $Z_S(\cdot,c)$, which is given by (5.1.3.2) from Lemma 5.1.3.1, and from (7.2.1.8). $a_m(f,c)$ is therefore an $S$-local eigendistribution of weight $c$.

(3) : If $a_m(\cdot,c_0)$ is nonzero, then there exists $f\in\mathcal S(\mathbf A_{F,S})$ such that $a_m(f,c_0)\ne 0$, which means that $c_0$ is a pole of $Z_S(f,c)$, and the polar multiplicity $m_S(f,c_0)$ of $c_0$ is at least $m$. It follows that we have $c_0\in\mathcal{U}_S$, and $m\le m_S(f,c_0)$, this latter inequality holding for all $f\in\mathcal S(\mathbf A_{F,S})$.

(4) : By design of $a_m(\cdot,c)$, for each $\omega\in\widehat{J^1_{F,S}}$, $H_m(\omega,\mathcal S(\mathbf A_{F,S}))$ is the intersection:

$$
H_m(\omega,\mathcal S(\mathbf A_{F,S}))=\bigcap_{(c,k):c\in\mathcal{U}_S,k>m(c)}\ker(a_k(\cdot,c)) \tag{7.2.1.9}
$$

## PDF page 335

**7.2. POLES OF THE $S$-IDELIC ZETA FUNCTIONS** · **335**

and hence by (1), $H_m(\omega,\mathcal S(\mathbf A_{F,S}))$ is closed, and the eigendistributions $\{a_k(\cdot,c)\}$ as $(c,k)$ varies over the set of pairs $I:=\{(c,k):c\in\mathcal{U},1\le k\le m(c)\}$ generate $H_m(\omega,\mathcal S(\mathbf A_{F,S}))^\perp$ within $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))'_\beta$ linearly and topologically. Indeed, $H_m(\omega,\mathcal S(\mathbf A_{F,S}))^\perp$ is closed in $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))'$ with respect to the $\sigma(\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))',\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S})))$-topology by [NB, Thm.8.9.2(d)], and hence it is closed with respect to the strong topology on $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))'$, since the strong topology is finer than the topology of simple convergence.

It is therefore enough to show that $\{a_k(\cdot,c)\}_{(c,k)\in I}$, linearly and topologically generates $H_m(\omega,\mathcal S(\mathbf A_{F,S}))^\perp$ with respect to the topology of simple convergence. By (7.2.1.9), this follows from [NB, Thm.8.9.2(a)]. $\square$

REMARK 7.2.1.2. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\omega\in\widehat{J^1_{F,S}}$ be a continuous character.

The short algebraically-exact sequence:

$$
0\to H_{m_{S_0}}(\omega,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))\xrightarrow{\prod_{(c,k)}a_k(\cdot,c)}\prod_{(c,k)}\mathbf C
$$

as $(c,k)$ ranges over the countable set of pairs:

$$
\{(c,k):c\in\mathcal{U}_{S_0},1\le k\le m_{S_0}(c)\}
$$

is turned by the $S$-local Mellin transform $L_S$ into the short algebraically-exact sequence:

$$
0\to\mathscr{O}_{\Omega(J_{F,S})}(\mathcal{U}_S-\mathcal{U}_{S_0})\to\mathscr{O}_{\Omega(J_{F,S})}(\mathcal{U}_S)\to\mathscr P_{\Omega(J_{F,S}),\mathcal{U}_S-\mathcal{U}_{S_0}}
$$

up to identifying the $m_{S_0}(c)$-dimensional linear space generated by the principal part of $Z_S(f,c)$ at $c\in\mathcal{U}_{S_0}$ with $\prod_{1\le k\le m_{S_0}(c)}\mathbf C$, the principal part operator being turned, by such identification, into $\prod_{1\le k\le m_{S_0}}a_k(\cdot,c)$.

REMARK 7.2.1.3. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We may choose $S_0=S$ in Theorem 7.3.1.2. In this case, the closed subspace $H_{m_S}(\omega,\mathcal S(\mathbf A_{F,S}))$ is, for each continuous character $\omega\in\widehat{J^1_{F,S}}$, the closure of the linear image under $\Phi_{F,S,\omega}$ of the closed subspace:

$$
\mathcal S_{00}(\mathbf A_{F,S})\subset\mathcal S(\mathbf A_{F,S}) \tag{7.2.1.10}
$$

which agrees with the closure of the linear subspace of those Schwartz-Bruhat functions in $\mathcal S(\mathbf A_{F,S})$ that vanish over the union $\bigcup_{v\in S}H_v$, for $H_v\subset\mathbf A_{F,S}$ the closed subspace defined by the equation $x_v=0$, and vanish with their real, holomorphic and anti-holomorphic directional derivatives of arbitrary order along $F_v\subset\mathbf A_{F,S}$ at each $H_v$ for $v$ ranging over all the Archimedean places.

We further note that $\Phi_{F,S,\omega}$ maps $\mathcal S_{00}(\mathbf A_{F,S})$ onto a closed subspace of $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$ which is linearly and topologically isomorphic to $\mathcal S_\mathrm{E}(J_{F,S})(\omega)$, the $\omega$-isotype of the Hausdorff locally convex topological $\mathbf C$-vector space of exponentially decaying Schwartz-Bruhat functions on the modulated group $J_{F,S}$, compatibly with the continuous left-translation actions of $J_{F,S}$.

This is a consequence of Proposition 5.3.4.4.

The next Theorem describes the structure of the tempered distributions $a_m(\cdot,c)$ more closely. Recall that the set $\mathcal{U}_S$ of the poles of $\rho_S(c)$, counted with multiplicity, is the union of the sets:

$$
\mathcal{U}_{S,v}:=\psi_v^{-1}(\mathcal{U}_v) \tag{7.2.1.11}
$$

for $\mathcal{U}_v\subset\Omega(F_v^\times)$ the set of the poles of the meromorphic function $\rho_v(c_v)$ on the Riemann surface $\Omega(F_v^\times)$ of local quasi-characters, counted with multiplicity, in light of the definition of $\rho_S(c)$ from (7.2.1.2).

Recall that each Riemann surface $\Omega(J_{F,S})$ admits holomorphic submersions

$$
\psi_v:\Omega(J_{F,S})\to\Omega(F_v^\times)
$$

## PDF page 336

**336** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

to the Riemann surfaces of local quasi-characters for each $v\in S$, defined by restricting a quasi-character $c\in\Omega(J_{F,S})$ to $F_v^\times$ along the closed injective homomorphism of Hausdorff locally compact abelian groups $F_v^\times\subset J_{F,S}$ induced by the insertion homomorphism $F_v^\times\subset\mathrm{GL}_1(\mathbf A_{F,S})$ into the $v$-indexed “coordinate”.

We recall that for such $S$, the $S$-local Hecke $L$-function $L_S(c)$ is defined for $c\in\Omega(J_{F,S})_{>0}$ by the assignment:

$$
L_S(c):=\prod_{v\in S}L_v(\psi_v(c))=\prod_{v\in S}L_v(c_v)
$$

where $L_v(c_v):=Z_v(f_v,c_v)$, for $f_v\in\mathcal S(F_v)$ the basic Schwartz-Bruhat functions on the local fields $F_v$, for each $v\in S$, defined in [CF, Ch.XV,§2.5] (see also [RV, Ch.7,§7.1(iii),pp.249-259]).

$L_S(c)$ is explicitly computed in [CF, Ch.XV,§2.5] (see also [RV, Ch.7,§7.1(iii),pp.249-259]) and it is seen to be meromorphic on $\Omega(J_{F,S})$, with poles located exactly at the points of $\mathcal{U}_S$, counted with multiplicity.

For $c\in\Omega(J_{F,S})_{>0}$, we let $\widehat L_S(c)$ be defined as

$$
\widehat L_S(c):=\prod_{v\in S}Z_v(\widehat f_v,\psi_v(\widehat c))=\prod_{v\in S}Z_v(\widehat f_v,\widehat c_v). \tag{7.2.1.12}
$$

The meromorphic function $1/\widehat L_S(c)$ has only removable singularities over $\Omega(J_{F,S})$, and the meromorphic function $\rho_S(c)$, which is defined as $L_S(c)/\widehat L_S(c)$, and computed explicitly in [CF, Ch.XV,§2.5] (see also [RV, Ch.7,§7.1(iii),pp.249-259]), therefore extends to a meromorphic function on $\Omega(J_{F,S})$, with poles located at exactly the points of $\mathcal{U}_S$, i.e. at the poles of $L_S(c)$, counted with multiplicity.

We further refer the reader to Theorem 3.3.1.1.

The following Theorem provides formulas for the functionals $a_k(\cdot,c)$.

Before we state it and prove it, we recall the following. For $F$ a number field, $S$ a finite set of places of $F$ containing all the Archimedean places, we fix a continuous character $\chi\in\widehat{J_{F,S}}$ for each parameter $\omega\in\widehat{J^1_{F,S}}$, i.e. such that $\chi\mid_{J^1_{F,S}}=\omega$, and use it as a base point for the connected component $\Omega(J_{F,S})(\omega)$, to parametrize the connected component by the global holomorphic chart $\chi\lvert\cdot\rvert_{F,S}^s$.

For $\phi$ a meromorphic function on $\Omega(J_{F,S})$, we can therefore consider the holomorphic derivative:

$$
\partial_s^k\phi(\chi\lvert\cdot\rvert_{F,S}^s)
$$

for each integer $k\ge 0$. If we change the choice of $\chi$ for each $\omega\in\widehat{J^1_{F,S}}$, then the holomorphic parametrization of $\Omega(J_{F,S})$ changes into a new one, $\chi'\lvert\cdot\rvert_{F,S}^z$, under a bi-holomorphism, which is given, explicitly, by the formula $z=-it_0+s$, where $t_0\in\mathbf R$ is the unique real number such that $\chi'=\lvert\cdot\rvert_{F,S}^{it_0}$.

In particular, we have:

$$
\partial_z^k(\phi(\chi'\lvert\cdot\rvert_{F,S}^z))=\partial_z^k(\phi(\chi\lvert\cdot\rvert_{F,S}^{z+it_0}))=(\partial_s^k\phi)(\chi\lvert\cdot\rvert_{F,S}^{z+it_0})=(\partial_s^k\phi)(\chi\lvert\cdot\rvert_{F,S}^s)
$$

and hence the holomorphic derivative of order $k$ is independent of the choice of global holomorphic parametrization $\chi\lvert\cdot\rvert_{F,S}^s$ of $\Omega(J_{F,S})$. We will be denoting it by $\partial^k$.

THEOREM 7.2.1.4 (Coefficients of Principal Parts Formula). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $v_1,\dots,v_N$ be the places of $F$ contained in $S$ such that $c\in\mathcal{U}_{S,v_1}\cap\dots\cap\mathcal{U}_{S,v_N}$. Let $m:=m_S(c)$ be the multiplicity of $c$ in $\mathcal{U}_S$.*

*Then $m=N$. Moreover:*

*(1) The image $\Delta'(c)$ in $\mathcal S(\mathbf A_{F,S})'_\beta$ from (3.4.3.14) of the $S$-local eigendistribution $\Delta_{F,S}(c)$ from Theorem 5.5.1.2, satisfies:*

$$
a_m(\cdot,c)=\widehat\Delta'(\widehat c)\prod_{v\in\{v_1,\dots,v_m\}}\mathrm{Res}_{c'_v=\psi_v(c)}L_v(c'_v)\prod_{v\in S-\{v_1,\dots,v_m\}}L_v(\psi_v(c)) \tag{7.2.1.13}
$$

## PDF page 337

**7.2. POLES OF THE $S$-IDELIC ZETA FUNCTIONS** · **337**

*where $L_v(c_v)$ is the local factor at $v$ of the Hecke $L$-function $L(c)$, and $\widehat\Delta'(c)$ is the $S$-adelic Fourier transform of the eigendistribution $\Delta'(\widehat c)$, i.e. $\widehat\Delta'(f)(\widehat c)=\Delta'(\widehat f)(\widehat c)$.*

*In particular, $a_m(\cdot,c)$ is an $S$-local eigendistribution of weight $c$.*

*(2) For any integer $0\le k\le m-1$, we have:*

$$
a_k(f,c)=\sum_{j=0}^{m-k}a_{m-j}(\rho_S(c'),c)\frac{\partial^{m-k-j}Z_S(\widehat f,\widehat{c'})|_{c'=c}}{(m-k-j)!} \tag{7.2.1.14}
$$

*where $a_{m-j}(\rho_S(c'),c)$ is the principal part of order $m-j$ of the meromorphic function $\rho_S(c')$ from (3.3.1.3) at $c=c'$, i.e. the coefficient of $(s-s_0)^{-m+j}$ of the Laurent series expansion of $\rho_S(\chi_0\lvert\cdot\rvert_{F,S}^s)$ at $s=s_0$, for $\{\chi_0\lvert\cdot\rvert_{F,S}^s,s\in\mathbf C\}$ a choice of holomorphic parametrization of $\Omega(J_{F,S})(c\mid_{J^1_{F,S}})$, and for $c$ being parametrized by $s=s_0$.*

We recall that the residues of the local $L$-functions $Z_v(f_v,c_v)$ for $f_v\in\mathcal S(F_v)$ are described in Lemma 3.3.2.1, for $v$ Archimedean, and Lemma 3.3.2.2, for $v$ non-Archimedean.

PROOF. (1) : By (3.4.3.13) from Theorem 3.4.3.3, we have the identity, as meromorphic functions over $\Omega(F_v^\times)$ for each place $v\in S$:

$$
\widehat\Delta'_v(\widehat c_v)(f)=\frac{Z_v(\widehat f,\widehat c)}{\widehat L_v(c)} \tag{7.2.1.15}
$$

for every $f\in\mathcal S(F_v)$. By design of $\Delta'$ (see (3.4.3.11) from Theorem 3.4.3.3), we deduce the identity as $S$-local eigendistributions of weight $c$:

$$
\widehat\Delta'(\widehat c)=\frac{Z_S(\mathcal F_S(\cdot),\widehat c)}{\widehat L_S(c)}. \tag{7.2.1.16}
$$

From the $S$-local functional equation (see (3.3.1.2) from Theorem 3.3.1.1), we have, upon choosing a holomorphic parametrization $\chi\lvert\cdot\rvert_{F,S}^s$, where $\{\chi\}\subset\widehat{J_{F,S}}$ is a set of representatives for the continuous characters of $J^1_{F,S}$, serving as base-points for each connected components of $\Omega(J_{F,S})$:

$$
Z_S(f,\chi\lvert\cdot\rvert_{F,S}^s)=\rho_S(\chi\lvert\cdot\rvert_{F,S}^s)Z_S(\widehat f,\overline{\chi}\lvert\cdot\rvert_{F,S}^{1-s})=\epsilon_S(\chi\lvert\cdot\rvert_{F,S}^s)\frac{L_S(\chi\lvert\cdot\rvert_{F,S}^s)}{\widehat L_S(\chi\lvert\cdot\rvert_{F,S}^s)}Z_S(\widehat f,\overline{\chi}\lvert\cdot\rvert_{F,S}^{1-s}) \tag{7.2.1.17}
$$

for any Schwartz-Bruhat function $f\in\mathcal S(\mathbf A_{F,S})$.

The identity of meromorphic functions over $\mathbf C$ from (7.2.1.17) therefore reads:

$$
Z_S(f,\chi\lvert\cdot\rvert_{F,S}^s)=L_S(\chi\lvert\cdot\rvert_{F,S}^s)\widehat\Delta'(\overline{\chi}\lvert\cdot\rvert_{F,S}^{1-s})(f) \tag{7.2.1.18}
$$

for each $f\in\mathcal S(\mathbf A_{F,S})$, the identity in (7.2.1.18) being in the sense of meromorphic functions on the complex $s$-plane, using Theorem 3.4.3.3 on $\Delta'$ (and hence its Fourier transform) being a holomorphic vector valued function valued in $\mathcal S(\mathbf A_{F,S})'_\beta$.

Let $c\in\bigcap_{1\le k\le N}\mathcal{U}_{S,v_k}$ be as in the statement of the Theorem. We parametrize $c$ as $\chi_0\lvert\cdot\rvert_{F,S}^{s_0}$ according to the chosen holomorphic parametrization of $\Omega(J_{F,S})$.

We therefore have, for each $f\in\mathcal S(\mathbf A_{F,S})$:

$$
a_m(f,c)=\lim_{s\to s_0}(s-s_0)^mZ_S(f,\chi_0\lvert\cdot\rvert_{F,S}^s)=\left\{\lim_{s\to s_0}(s-s_0)^mL_S(\chi_0\lvert\cdot\rvert_{F,S}^s)\right\}\lim_{s\to s_0}\left\{\widehat\Delta'(\overline{\chi_0}\lvert\cdot\rvert_{F,S}^{1-s})(f)\right\}. \tag{7.2.1.19}
$$

By Theorem 7.2.1.18, $\Delta'$, and hence its Fourier transform, is an $\mathcal S(\mathbf A_{F,S})'_\beta$-valued holomorphic function over $\Omega(J_{F,S})$, and hence we have:

$$
\lim_{s\to s_0}\left\{\widehat\Delta'(\overline{\chi_0}\lvert\cdot\rvert_{F,S}^{1-s})(f)\right\}=\widehat\Delta'(\overline{\chi_0}\lvert\cdot\rvert_{F,S}^{1-s_0})(f)=\widehat\Delta'(\widehat c)(f). \tag{7.2.1.20}
$$

## PDF page 338

**338** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

We are reduced to computing the complex limit:

$$
\lim_{s\to s_0}(s-s_0)^mL_S(\chi_0\lvert\cdot\rvert_{F,S}^s). \tag{7.2.1.21}
$$

Assume first that we have $m>N$. Since $c\in\bigcap_{1\le k\le N}\mathcal{U}_{S,v_k}$, then $\psi_v(c)$ is a pole of $L_v(c_v)$ for $v\in\{v_1,\dots,v_N\}$ only, and hence the limit in (7.2.1.21) is zero. We may therefore assume $m\le N$, and, up to relabelling, assume that $\psi_v(c)$ is a pole of $L_v(c_v)$ exactly for $v\in\{v_1,\dots,v_m\}$, since, by Lemma 3.3.2.1 and Lemma 3.3.2.2, $L_v(c_v)$ only has at most a simple pole over $\Omega(F_v^\times)$.

We deduce the identity:

$$
\lim_{s\to s_0}\prod_{v\in\{v_1,\dots,v_m\}}(s-s_0)L_v(\psi_v(\chi_0\lvert\cdot\rvert_{F,S}^s))\prod_{v\in\{v_{m+1},\dots,v_N\}}L_v(\psi_v(\chi_0\lvert\cdot\rvert_{F,S}^s)) \tag{7.2.1.22}
$$

$$
=\prod_{1\le k\le m}\mathrm{Res}_{c'_{v_k}=\psi_{v_k}(c)}L_{v_k}(\psi_{v_k}(c')\prod_{m+1\le k\le N}L_{v_k}(\psi_{v_k}(c)). \tag{7.2.1.23}
$$

From (7.2.1.22), we deduce that (7.2.1.13) holds, for each Schwartz-Bruhat function $f\in\mathcal S(\mathbf A_{F,S})$, and since both sides in (7.2.1.13) are continuous functionals on $\mathcal S(\mathbf A_{F,S})$, it holds in the sense of tempered distributions on $\mathbf A_{F,S}$, homogeneous of weight $c$.

(2) : We parametrize $c\in\bigcap_{1\le k\le N}\mathcal{U}_{S,v_k}$ as $\chi_0\lvert\cdot\rvert_{F,S}^{s_0}$. By (7.2.1.19), we have:

$$
\lim_{s\to s_0}\partial_s^{m-k}(s-s_0)^mZ_S(f,\chi_0\lvert\cdot\rvert_{F,S}^s)=\lim_{s\to s_0}\partial_s^{m-k}\left\{(s-s_0)^m\rho_S(\chi_0\lvert\cdot\rvert_{F,S}^s)Z_S(\widehat f,\overline{\chi_0}\lvert\cdot\rvert_{F,S}^{1-s})\right\} \tag{7.2.1.24}
$$

$$
=\lim_{s\to s_0}\sum_{j=0}^{m-k}\binom{m-k}{j}\partial_s^j\left\{(s-s_0)^m\rho_S(\chi_0\lvert\cdot\rvert_{F,S}^s)\right\}\partial_s^{m-k-j}Z_S(\widehat f,\overline{\chi_0}\lvert\cdot\rvert_{F,S}^{1-s}) \tag{7.2.1.25}
$$

$$
=\sum_{j=0}^{m-k}\binom{m-k}{j}j!\,a_{m-j}(\rho_S(\chi_0\lvert\cdot\rvert_{F,S}^s),s_0)\,\partial_s^{m-k-j}Z_S(\widehat f,\overline{\chi_0}\lvert\cdot\rvert_{F,S}^{1-s})|_{s=s_0} \tag{7.2.1.26}
$$

where $a_{m-j}(\rho_S(\chi_0\lvert\cdot\rvert_{F,S}^s),s_0)$ is the principal part of order $m-j$ at $s=s_0$, of the meromorphic function $\rho_S(\chi_0\lvert\cdot\rvert_{F,S}^s)$, i.e. the coefficient of $(s-s_0)^{-m+j}$ in the Laurent series expansion of $\rho_S(\chi_0\lvert\cdot\rvert_{F,S}^s)$ around $s=s_0$.

The last sum in (7.2.1.26) reads:

$$
a_k(f,\chi_0\lvert\cdot\rvert_{F,S}^{s_0})=\sum_{j=0}^{m-k}a_{m-j}(\rho_S(\chi_0\lvert\cdot\rvert_{F,S}^s),s_0)\frac{\partial_s^{m-k-j}Z_S(\widehat f,\overline{\chi_0}\lvert\cdot\rvert_{F,S}^{1-s})|_{s=s_0}}{(m-k-j)!} \tag{7.2.1.27}
$$

and formation of both sides of (7.2.1.27) is $\mathbf C$-linear with respect to $f$.

We deduce that (7.2.1.14) holds. $\square$

**7.2.2. Local poles and global zeros.** The following Proposition provides a first dictionary between the poles of the $S$-idelic Zeta functions and the zeros of the global idelic Zeta functions, using the transition operators:

$$
\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S(\mathbf A_F)).
$$

Following (7.2.1.11), we denote by

$$
\mathcal{U}_{S_0}\subset\mathcal{U}_S
$$

the subset of the set of poles $\mathcal{U}_S$ of $\rho_S(c)$ on $\Omega(J_{F,S})$ given by

$$
\mathcal{U}_{S_0}:=\bigcup_{v\in S_0}\psi_v^{-1}(\mathcal{U}_v)=\bigcup_{v\in S_0}\mathcal{U}_{S,v} \tag{7.2.2.1}
$$

## PDF page 339

**7.2. POLES OF THE $S$-IDELIC ZETA FUNCTIONS** · **339**

each point being counted with multiplicity, defined, for $c\in\mathcal{U}_{S_0}$, as the sum of the orders of poles of $\rho_v$ at $\psi_v(c)$ as $v$ ranges over $S_0$. Since, by Lemma 3.3.2.1 and Lemma 3.3.2.2, each such order is $1$, the multiplicity of $c$ in $\mathcal{U}_{S_0}$ is the number of places $v\in S_0$ such that $\psi_v(c)$ is a pole of $\rho_v$ over $\Omega(F_v^\times)$.

We define the function:

$$
m_{S_0}:\mathcal{U}_{S_0}\to\mathbf N \tag{7.2.2.2}
$$

to be the function assigning to $c\in\mathcal{U}_{S_0}$ its multiplicity in $\mathcal{U}_{S_0}$ as defined in the foregoing.

PROPOSITION 7.2.2.1. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$. Let $S_0\subset S$ be a non-empty subset of finite places.*

*Then for any continuous character $\chi\in\widehat{C_F}$ unramified outside $S_0$ (and hence outside $S$), and for $\chi_S$ the unique continuous character of $J_{F,S}$ obtained by descending to $J_{F,S}$ the restriction of $\chi$ to $C_{F,S}\subset C_F$, by $\widehat{\mathcal O}_{\Sigma_F-S}^\times$-invariance, given the transition operator:*

$$
\bar\pi_S:\mathrm H_{0,\mathrm{cont}}(\chi_S\mid_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\chi\mid_{C^1_F},\mathcal S(\mathbf A_F))
$$

*induced by the transition operators $\bar\pi_{S,S'}$ from (5.2.3.1) of Theorem 5.2.3.1, the following conditions on $f\in\mathcal S(\mathbf A_{F,S})$ are equivalent:*

*(1) $a_k(f,c)=0$ for all $c\in\mathcal{U}_{S_0}\cap\Omega(J_{F,S})(\chi_S\mid_{J^1_{F,S}})$ and all integers $m_S(c)-m_{S_0}(c)+1\le k\le m_S(c)$.*

*(2) $Z(\pi_S(f),c)=Z(\overline{\pi}_S(\Phi_{F,S}(f)),c)$ has a zero at $c$ of order $m_{S_0}(c)$, for all $c\in\psi_{F,S}^{-1}(\mathcal{U}_{S_0})\cap\Omega(C_F)(\chi\mid_{C^1_F})$, with the sole exception of $c=1$, in which case its order is $m_{S_0}(c)-1$ if and only if $c=1$ is a pole of at least one of the Euler factors at $v\in S_0$ of the Hecke $L$-function.*

*(3) $f\in \mathrm{PV}_{S,S_0}\mathrm H_{0,\mathrm{cont}}(\chi_S\mid_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$.*

*(4) $\pi_S(f)\in \mathrm{PV}_{S_0}\mathrm H_{0,\mathrm{cont}}(\chi\mid_{C^1_F},\mathcal S(\mathbf A_F))$.*

PROOF. (1) implies (2) : By Theorem 7.2.1.4(2), $Z_S(\widehat f,\widehat{c'})$ has a zero of order $m_{S_0}(c)$ at $c'=c\in\mathcal{U}_{S_0}$. It follows that, since $\chi$ is unramified outside $S$, we have:

$$
Z_S(\widehat f,\widehat{c'})\widehat L_S(c')=Z(\widehat{\pi_S(f)},\widehat{c'})=Z(\pi_S(f),c')
$$

where we used the global functional equation from (3.2.2.2) of Theorem 3.2.2.1.

It follows that $Z(\pi_S(f),c')$ has a zero of order $m_{S_0}(c)$ at $c'=c$, unless $L_S(c')$ has a pole at $c'=c$, in which case such pole can only be simple and occurs at $c'=1$. This proves (2).

(2) implies (4) : By (2), upon fixing a holomorphic parametrization $\chi\lvert\cdot\rvert_F^s$ for the Riemann surface $\Omega(C_F)$, the meromorphic function:

$$
\phi(s):=\prod_{v\in S_0}\frac{1}{1-\chi(\mathfrak p_v)N(\mathfrak p_v)^{-s}}Z(\pi_S(f),\chi\lvert\cdot\rvert_F^s)
$$

has only removable singularities, and it is an element of $A\mathcal{S}(\mathbf C)$ (a consequence of the Asymptotic Residue Theorem, Theorem B.3.2.1, applied to the vertical lines bounding any vertical strip of bounded width containing the line $\chi\lvert\cdot\rvert_F^{i\mathbf R}$ in its interior, from which we deduce that not only $\phi$ but also its holomorphic derivatives decay faster than any positive power of $\lvert s\rvert^{-1}$ as $\lvert s\rvert\to+\infty$ uniformly over any such strip).

It follows from Theorem 6.3.2.1 that $\phi$ is in the range of $L$, and hence $\pi_S(f)$ is in the image of $\mathrm{PV}_{S_0}$ on $\mathrm H_{0,\mathrm{cont}}(\chi\mid_{C^1_F},\mathcal S(\mathbf A_F))$.

(4) implies (3) : By (4), $\pi_S(f)$ is in the range of $\mathrm{PV}_{S_0}$ on $\mathrm H_{0,\mathrm{cont}}(\chi\mid_{C^1_F},\mathcal S(\mathbf A_F))$.

By Lemma 5.3.1.5, $f$ is in the range of $\mathrm{PV}_{S,S_0}$ on $\mathrm H_{0,\mathrm{cont}}(\chi_S\mid_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$.

(3) implies (1) : By Theorem 7.2.1.1(4), if $Z_S(f,c')$ has a pole of order $k>m_S(c)-m_{S_0}(c)$ at $c'=c$, then $f$ cannot be in the range of $\mathrm{PV}_{S,S_0}$, since all elements of $\mathcal S(\mathbf A_{F,S})$ in the range of $\mathrm{PV}_{S,S_0}$ have $S$-idelic Mellin transforms with poles of order at most $m_S(c)-m_{S_0}(c)$. $\square$

## PDF page 340

**340** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

Corollary 7.2.2.2. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$. Let $S_0\subset S$ be a non-empty subset of finite places.*

*Then for any continuous character $\chi\in\widehat{C_F}$ unramified outside $S_0$ (and hence outside $S$), and for $\chi_S$ the unique continuous character of $J_{F,S}$ obtained by descending to $J_{F,S}$ the restriction of $\chi$ to $C_{F,S}\subset C_F$, by $\widehat{\mathcal O}^\times_{\Sigma_F-S}$-invariance, given the transition operator:*

$$\overline{\pi}_S:\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}},\mathcal S_0(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$$

*induced by the transition operators $\overline{\pi}_{S,S'}$ from (5.2.3.1) of Theorem 5.2.3.1, with:*

$$\mathcal S_0(\mathbf A_{F,S})=\ker(\delta_0)\cap\ker(\widehat{\delta_0})\subset\mathcal S(\mathbf A_{F,S}) \tag{7.2.2.3}$$

*then the following conditions on $f\in\mathcal S_0(\mathbf A_{F,S})$ are equivalent:*

(1) *$a_k(f,c)=0$ for all $c\in \mathcal{U}_{S_0}\cap\Omega(J_{F,S})(\chi_S|_{J^1_{F,S}})$ and all integers $m_S(c)-m_{S_0}(c)+1\le k\le m_S(c)$, with the sole possible exception of $c=1$, in which case $a_k(f,c)=0$ for all integers $m_S(c)-m_{S_0}(c)\le k\le m_S(c)-1$.*

(2) *$Z(\pi_S(f),c)=Z(\overline{\pi}_S(\Phi_{F,S}(f)),c)$ has a zero at $c$ of order $m_{S_0}(c)$, for all $c\in\psi^{-1}_{F,S}(\mathcal{U}_{S_0})\cap\Omega(C_F)(\chi|_{C^1_F})$.*

(3) $f\in \mathrm{PV}_{S,S_0}\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}},\mathcal S_0(\mathbf A_{F,S}))$.

(4) $\pi_S(f)\in \mathrm{PV}_{S_0}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F},\mathcal S_0(\mathbf A_F))$.

Proof. This is a direct consequence of Proposition 7.2.2.1, noting that the linear conditions $\delta_0(f)=\widehat{\delta_0}(f)=0$ resolve one order of pole at $c=1$ in (1), and increase the multiplicity of the zero at $c=1$ in (2) of the Proposition. $\square$

**7.3. Paley-Wiener Levels and Schauder Bases of Principal Parts**

We now discuss an $S$-local analog of the Theorem 7.1.4.2, describing certain $S$-local divisor exact sequences encoding the poles of the $S$-idelic Zeta functions, and describing orthogonals by means of Schauder bases comprised of $S$-local eigendistributions.

We will also be analyzing principal parts at the poles of the Archimedean local Euler factors, and relate them to point evaluation functionals on global idelic Zeta functions supported at the trivial zeros.

**7.3.1. Orbital Schauder Bases.** The following Theorem describes the orthogonals of the closed subspaces $\mathrm{PV}_{S,S_0}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ as $S_0\subset S$ is a fixed subset of finite places.

Situation 7.3.1.1 (Saturated sets of places). Let $F$ be a number field, $S$ be a finite set of places of $F$ containing all the Archimedean places. Let $S_0$ be an arbitrary finite set of places of $F$.

(1) We will term $S_0$ saturated if and only if for every prime number $p$, if a place $v$ of $F$ whose residue characteristic is $p$ is contained in $S_0$, then all places of $F$ whose residue characteristic is $p$ are also contained in $S_0$.

(2) Let $p$ be a prime number such that at least one place of $F$ whose residue characteristic is $p$, is contained in $S$. Assume $S$ is saturated.

(3) We choose, as in Situation 4.4.2.3 applied to the $\mathbf R_{>0}$-moduated group $G=J_{F,S}$ with $|\cdot|_G=|\cdot|_{F,S}$, a set of representatives $\widetilde{J^1_{F,S}}$ of the continuous characters of the compact Hausdorff abelian group $J^1_{F,S}$, equivalently a holomorphic parametrization for $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$ of the form

$$
\chi|\cdot|^s_{F,S},\quad s\in\mathbf C
$$

for $\chi\in\widetilde{J^1_{F,S}}$.

We begin by constructing bi-orthogonal sets to the sets of continuous functionals given by the coefficients of the principal parts of the $S$-idelic Zeta functions (see Definition 7.1.2.1 for the definition of the functionals $a_m(\cdot,c)$, as $c\in\Omega(J_{F,S})$).

## PDF page 341

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **341**

Theorem 7.3.1.2 (Orbital bi-orthogonal sets). *Let $F$ be a number field, $S$ a saturated finite set of places containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$.*

*Let $S_0\subset S$ be a non-empty subset containing all the Archimedean places.*

*Assume the notation and choices in Situation 7.3.1.1 are in force.*

Let $\chi\in\widetilde{J^1_{F,S}}$ be a continuous character.

Then:

(1) *The closed subspace $\mathrm{PV}_{S,S_0}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ is the intersection of $\ker(a_k(\cdot,c))$ as $c$ ranges over $\mathcal{U}_S$, and as $k$ ranges over the integers $m_S(c)-m_{S_0}(c)<k\le m_S(c)$.*

(2) The orthogonal

$$\mathrm{PV}_{S,S_0}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))^\perp\subset\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))'_\beta \tag{7.3.1.1}$$

*with respect to the duality $\langle\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})),\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))'\rangle$ is linearly and topologically generated by the eigendistributions $\{a_k(\cdot,c)\}$ as $c$ ranges over the points in $\mathcal{U}_S$ and, for each $c\in \mathcal{U}_S$, $k$ ranges over the integers $m_S(c)-m_{S_0}(c)<k\le m_S(c)$. The set $\{a_k(\cdot,c)\}$ admits a bi-orthogonal set in*

$$
\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))/\mathrm{PV}_{S,S_0}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})).
$$

*In particular, it is topologically free.*

Proof. (1) follows from Theorem 7.2.1.1(4) applied to $\mathcal{U}=\mathcal{U}_{S_0}$, to $m:=m_S-m_{S_0}$.

(2) : By (1) and Theorem 7.2.1.1(4), the set of $S$-local eigendistributions $\{a_k(\cdot,c)\}$ as $c$ ranges over the points in $\mathcal{U}_S$ and, for each $c\in \mathcal{U}_S$, $k$ ranges over the integers $m_S(c)-m_{S_0}(c)<k\le m_S(c)$ linearly and topologically generates the orthogonal of $\mathrm{PV}_{S,S_0}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ with respect to the duality $\langle\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})),\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))'_\beta\rangle$.

We let $\omega\in\widehat{J^1_{F,S}}$ be a continuous character, and we denote by $I_{S_0,\omega}$ the countable set of pairs:

$$I_{S_0,\omega}:=\{(c,k)\in(\mathcal{U}_S\cap\Omega(J_{F,S})(\omega))\times\mathbf N:m_{S_0}(c)<k\le m_S(c)\}$$

and let $\{C_{(c,k)}\}_{(c,k)\in I_{S_0,\omega}}$ and $\{C'_{(c,k)}\}_{(c,k)\in I_{S_0,\omega}}$ be two sets of complex numbers such that for any finite subset $J\subset I_{S_0,\omega}$, the assignments $J\mapsto\sum_{(c,k)\in J}C_{(c,k)}a_k(\cdot,c)$, respectively $J\mapsto\sum_{(c,k)\in J}C'_{(c,k)}a_k(\cdot,c)$, is a convergent net in $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))'_\beta$.

We denote by $\sum_{(c,k)\in I_{S_0,\omega}}C_{(c,k)}a_k(\cdot,c)$, respectively $\sum_{(c,k)\in I_{S_0,\omega}}C'_{(c,k)}a_k(\cdot,c)$, their respective limits.

Assume we have, as elements of $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))'_\beta$:

$$\sum_{(c,k)\in I_{S_0,\omega}}C_{(c,k)}a_k(\cdot,c)=\sum_{(c,k)\in I_{S_0,\omega}}C'_{(c,k)}a_k(\cdot,c). \tag{7.3.1.2}$$

We select a single pair $(c_0,m_0)\in I_{S_0,\omega}$, and let $f\in\mathcal S(\mathbf A_{F,S})$ be a Schwartz-Bruhat function such that $Z_S(f,c)$ has a pole at $c=c_0$ of order $m_0>m_{S_0}(c_0)$, and is holomorphic over $\Omega(J_{F,S})-\{c_0\}$.

By continuity of both sides of (7.3.1.2), and the mode of convergence of the sums in (7.3.1.2) being uniform on bounded subsets, we deduce that the nets of complex numbers $J\mapsto\sum_{(c,k)\in J}C_{(c,k)}a_k(f,c)$, respectively $J\mapsto\sum_{(c,k)\in J}C'_{(c,k)}a_k(f,c)$, both converge, and their limits are $\langle\sum_{(c,k)\in I_{S_0,\omega}}C_{(c,k)}a_k(\cdot,c),f\rangle$, respectively $\langle\sum_{(c,k)\in I_{S_0,\omega}}C'_{(c,k)}a_k(\cdot,c),f\rangle$.

Since $a_k(f,c)=0$ if either $c\ne c_0$ or if $k>m_0$, we deduce that the identity:

$$\sum_{m_{S_0}(c_0)<k\le m_0}C_{(c_0,k)}a_k(f,c_0)=\sum_{m_{S_0}(c_0)<k\le m_0}C'_{(c_0,k)}a_k(f,c_0) \tag{7.3.1.3}$$

## PDF page 342

**342** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

Upon repeating the reasoning with $f$ replaced by a Schwartz-Bruhat function $f'\in\mathcal S(\mathbf A_{F,S})$ such that $Z_S(f',c)$ has only one pole at $c_0$ of order $m_0-1$, we further obtain the identity:

$$\sum_{m_{S_0}(c_0)<k\le m_0-1}C_{(c_0,k)}a_k(f',c_0)=\sum_{m_{S_0}(c_0)<k\le m_0-1}C'_{(c_0,k)}a_k(f',c_0) \tag{7.3.1.4}$$

and upon iterating the reasoning $m_0$ times, we obtain a non-degenerate system of $m_0$ linear equations relating the $C_{(c_0,k)}$ to the $C'_{(c_0,k)}$, deducing the identities $C_{(c_0,k)}=C'_{(c_0,k)}$.

Since we selected $(c_0,m_0)\in I_{S_0,\omega}$ arbitrarily, we deduce the identities $C_{(c,k)}=C'_{(c,k)}$ for all $(c,k)\in I_{S_0,\omega}$.

By [Jar, Part II,Ch.14,§14.1,Prop.1.p.289], this implies that the countable set $\{a_k(\cdot,c)\}_{(c,k)\in I_{S_0,\omega}}$, and hence, for any countable subset $I\subset I_{S_0,\omega}$, the resulting countable subset $\{a_k(\cdot,c)\}_{(c,k)\in I}$, is topologically free.

We are reduced to showing that for any choice $(c_0,m_0)\in I_{S_0,\omega}$, there exists $f\in\mathcal S(\mathbf A_{F,S})$ such that $Z_S(f,c)$ is holomorphic over $\Omega(J_{F,S})-\{c_0\}$, and the order of pole of $Z_S(f,c)$ at $c=c_0$ is exactly $m_0$.

We choose a holomorphic parametrization $\chi|\cdot|^s_{F,S}$ for the Riemann surface $\Omega(J_{F,S})$, i.e. we choose a continuous character $\chi\in\widehat{J_{F,S}}$ for each $\omega\in\widehat{J^1_{F,S}}$, and parametrize the connected component $\Omega(J_{F,S})(\omega)$ as $\chi|\cdot|^s_{F,S}$, with $s\in\mathbf C$ a global holomorphic coordinate.

The point $c_0\in\Omega(J_{F,S})$ is therefore parametrized as $\chi_0|\cdot|^{s_0}_{F,S}$, for a unique $\chi_0$, the base point with respect to the chosen holomorphic parametrization of $\Omega(J_{F,S})$, of the connected component of $\Omega(J_{F,S})$ containing $c_0$.

We let $\varphi\in\mathcal D(\mathbf R_{>0})$ such that the entire function:

$$\psi(s):=\int_{\mathbf R_{>0}}t^{s+ix_0}\varphi(t)\frac{\mathrm{d}t}{t}$$

satisfies $\psi(s_0)\ne 0$, for $x_0\in\mathbf R$ the unique real number such that $\chi_0(t)=t^{ix_0}$ as smooth functions on $t\in\mathbf R_{>0}$.

We let $S_{c_0}:=\{v_1,\dots,v_{m_S(c_0)}\}\subset S$ be the subset of those places such that $c_0\in \mathcal{U}_{S,v_1}\cap\dots\cap \mathcal{U}_{S,v_{m_S(c_0)}}$, i.e. such that $\psi_{v_i}(c_0)$ is a pole of the local factor $L_{v_i}(c_{v_i})$ at $v_i$ of the Hecke $L$-function $L(c)$.

There therefore exists a unique integer $N_{v_i}\in\mathbf N$ such that $c_0=\chi|\cdot|^{\frac{2\pi iN_{v_i}}{\log(q_{v_i})}-it_{v_i}}_{F,S}$.

Recall that we have $m_0>m_{S_0}(c_0)$.

The function:

$$u(s):=\prod_{1\le i\le m_0:v_i\in S_{c_0}}\left\{\frac{1}{s-\frac{2\pi iN_{v_i}}{\log(q_{v_i})}-it_{v_i}}(1-q^{-s-it_{v_i}}_{v_i})\right\}\psi(s)$$

has only removable singularities and we rename as $u$ its unique holomorphic extension to the complex $s$-plane.

The entire function $u(s)$ has simple zeros at all the points $\{\chi|\cdot|^{\frac{2\pi im}{\log(q_{v_i})}-it_{v_i}}_F\}_{m\in\mathbf Z}$ for all $1\le i\le m_0$, where, recall, $v_i$ is a non-Archimedean place contained in $S_0$ such that $\psi_{v_i}(c_0)$ is a pole of local-at-$v_i$ $L$-functions, with the exception of the unique point $\psi^{-1}_{F,S}(c_0)$, which does not feature among such zeros.

The inverse Mellin transform $\phi$ of $u$ is a Schwartz-Bruhat function on $\mathbf R_{>0}$ with exponential decay. By Lemma 5.3.4.3, there exists a Schwartz-Bruhat function $f_0\in\mathcal S_{00}(\mathbf A_{F,S})$ such that $\Phi_{F,S,1}(f_0)=\phi$.

We deduce that the function $f_1:=\chi^{-1}\cdot f_0$, also a Schwartz-Bruhat function on $\mathbf A_{F,S}$ and an element of $\mathcal S_{00}(\mathbf A_{F,S})$ by Lemma 5.3.4.2(3), satisfies $\Phi_{F,S,\omega}(f_1)=\phi$.

Note that since $f_1\in\mathcal S_{00}(\mathbf A_{F,S})$, $f_1$ is in the range of Weil's Principal Value operator $\mathrm{PV}_{S,S_0}$, which is a linear topological embedding with closed range (see Lemma 5.3.1.5).

The Schwartz-Bruhat function $f:=\mathrm{PV}^{-1}_{S,S_0}(f_1)$ satisfies the desired properties: $Z_S(f,c)$ has, over the connected component $\Omega(J_{F,S})(\omega)$, exactly one pole, $c_0$, with order of pole exactly $m_0$, and it is holomorphic away from $c_0$. $\square$

We now start the study of the Fréchet spaces

$$
\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))
$$

## PDF page 343

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **343**

through the study of certain subquotients which we will now introduce.

Definition 7.3.1.3 ($p$-primary Orbital Quotients). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

Assume the notation and choices in Situation 7.3.1.1 are in force.

We denote by:

$$\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}}):=\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))/\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})) \tag{7.3.1.5}$$

endowed with the quotient topology.

We refer to $\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})$ as the $p$-primary Orbital Quotient.

We now return to the multiplicity function $m_{S_0}$ defined in (7.2.2.2) and associated to a subset $S_0\subset S$.

Recall that for $\mathcal{U}_{S_0}$ the subset defined as the union $\bigcup_{v\in S_0}\mathcal{U}_{S,v}$ (see (7.2.2.1)), where $\mathcal{U}_{S,v}:=\psi^{-1}_v(\mathcal{U}_v)$, with $\psi_v:\Omega(J_{F,S})\to\Omega(F^\times_v)$ the quotient surjective local analytic isomorphism defined by restriction of a continuous quasi-character $c$ to $F^\times_v\subset J_{F,S}$, and where $\mathcal{U}_v$ is the set of poles (each simple) over $\Omega(F^\times_v)$ of the meromorphic function $\rho_v(c)$ from [CF, Ch.XV,§2.5,p.322] (i.e. the correcting meromorphic factor from the local-at-$v$ functional equation; see Proposition 3.3.1.5), $m_{S_0}$ counts the cumulative multiplicity of $c\in \mathcal{U}_{S_0}$ as a member of each $\psi^{-1}_v(\mathcal{U}_v)$, each counted with multipicity $1$.

Definition 7.3.1.4 (Primary Multiplicity Functions). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$.

Assume the notation and choices in Situation 7.3.1.1 are in force.

We define the multiplicity function:

$$N_{S_p}:\mathcal{U}_{S_p}\to\mathbf N \tag{7.3.1.6}$$

to be $N_{S_p}:=m_{S_p}$, the integer-valued function assigning to $c\in \mathcal{U}_{S_p}$ the value:

$$N_{S_p}(c):=\sum_{v\in S_p}\mathrm{ord}_{c'=\psi_v(c)}\rho_v(c'). \tag{7.3.1.7}$$

We refer to $N_{S_p}$ as the $p$-primary multiplicity function.

The following Theorem provides absolute Schauder bases for the Fréchet spaces $\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})$, and unconditional bases for its strong dual.

We will be using the following Lemma:

Lemma 7.3.1.5. *Let $E_1,E_2$ be nuclear Fréchet spaces, $H_k\subset E_k$ closed subspaces for $k=1,2$. Assume:*

(i) *there exists a continuous injective linear operator $A:E_1\to E_2$ such that $A^{-1}(H_2)=H_1$.*

(ii) *The induced continuous injective linear operator $A_0:E_1/H_1\to E_2/H_2$ is surjective.*

(iii) *There exists a sequence $\{x_m\}_{m\ge 0}\subset E_2$ whose image in $E_2/H_2$ is an absolute Schauder basis.*

(iv) *For any continuous seminorm $q$ on $E_2/H_2$, there exists a real-valued nonnegative function $F_q:\mathbf N\to\mathbf R_{\ge 0}$ such that:*

$$q(\pi_2(x_m))\ll_q F_q(m) \tag{7.3.1.8}$$

as $m\to+\infty$.

Then:

(1) *For any choice of sequence $\{y_m\}_{m\ge 0}\subset E_1$ such that $A(y_m)=x_m$ for each integer $m\ge 0$, the image sequence $\{\pi_1(y_m)\}_{m\ge 0}$, with $\pi_1:E_1\to E_1/H_1$ the quotient map, is an absolute Schauder basis for $E_1/H_1$. Its bi-orthogonal sequence in $(E_1/H_1)'_\beta$ is an unconditional Schauder basis.*

## PDF page 344

**344** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

(2) *The sequence $\{\pi_1(y_m)\}_{m\ge 0}\subset E_1/H_1$ satisfies the following condition: for any continuous seminorm $q$ on $E_1/H_1$, there exists a real-valued nonnegative function $F_q:\mathbf N\to\mathbf R_{\ge 0}$ such that:*

$$q(\pi_1(y_m))\ll_q F_{q\circ A^{-1}_0}(m) \tag{7.3.1.9}$$

as $m\to+\infty$.

Proof. We note that by Lemma 4.1.2.4, the bi-orthogonal sequence to $\{\pi_2(x_m)\}_{m\ge 0}\subset E_2/H_2$ is an unconditional Schauder basis. The Lemma applies since $E_2$, and hence $E_2/H_2$, being $H_2\subset E_2$ is a Fréchet space, hence complete and barrelled, nuclear by [Scha, Ch.III,§7,Thm.7.4,p.103].

(1) : By (i) and [NB, Thm.14.4.5(b)], $A_0$ is a linear topological isomorphism. The convergence condition from [Jar, Part II,Ch.14,§14.7,p.314] defining absolute Schauder bases is preserved under linear topological isomorphisms, which also preserve topological bases in both directions, and hence Schauder bases, by [Jar, Part II,Ch.14,§14.2,Thm.5,p.293].

(2) : We let $q$ be a continuous seminorm on $E_1/H_1$. Then $q\circ A^{-1}_0$ is a continuous seminorm on $E_2/H_2$ since $A_0$ is a linear topological isomorphism. The estimate in (7.3.1.9) folows from (iv). By Lemma 4.1.2.4, the bi-orthogonal sequence to $\{\pi_1(y_m)\}_{m\ge 0}$ is an unconditional Schauder basis in $(E_1/H_1)'_\beta$. $\square$

We first recall the description of the poles of $\rho_S(c)$ from Lemma 7.1.2.2, in accordance with the holomorphic parametrization $\{\chi|\cdot|^s_{F,S}\}$ of $\Omega(J_{F,S})$ chosen in Situation 7.3.1.1.

For each $\chi\in\widetilde{J^1_{F,S}}$ and for each $v\in S_p$, there exists a unique real number $t_v\in\mathbf R$ contained within $[0,2\pi/\log(q_v))$, for $q_v:=|\pi_v|^{-1}_v$ with $\pi_v\in F^\times_v$ a choice of local uniformizer, such that:

$$\chi|\cdot|^{-it_v}_F\in(\pi^{\mathbf Z}_v)^\perp\subset\widehat{J_{F,S}} \tag{7.3.1.10}$$

and for each $c\in \mathcal{U}_{S_p}$, we let $S_{p,c}\subset S_p$ be the subset $\{v_1,\dots,v_{N_p(c)}\}\subset S_p$ of those finite places $v\in S_p$ such that $c\in \mathcal{U}_{S,v}=\psi^{-1}_v(\mathcal{U}_v)$.

For each $v\in S_{p,c}$, there therefore exists a unique integer $m_{c,v}\in\mathbf Z$ such that:

$$c=\chi|\cdot|^{\frac{2\pi im_{c,v}}{\log(q_v)}-it_v}_{F,S}. \tag{7.3.1.11}$$

Note that for $v,w\in S_{p,c}$, the two real numbers $t_v$ and $t_w$ are related by a unique translation by an element of the discrete subgroup $\frac{2\pi\mathbf Z}{\log(p)}\subset\mathbf R$.

Theorem 7.3.1.6 (Orbital Schauder Bases - I). *Let $F$ be a number field, $S$ a saturated finite set of places containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal O_{F,S})=1$.*

*Assume the notation and choices in Situation 7.3.1.1 are in force.*

*We denote by $N_p$ is the number of finite places of $F$ whose residue characteristic is $p$.*

Let $\chi\in\widetilde{J^1_{F,S}}$ be a continuous character.

We define the two subsets:

$$P_{S,S_p}(\chi|_{J^1_{F,S}}):=\{a_k(\cdot,c):m_S(c)-N_p(c)<k\le m_S(c)\}\subset\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))'_\beta \tag{7.3.1.12}$$

and:

$$E_{S,S_p}(\chi|_{J^1_{F,S}}):=\{\widehat\delta^{(k)}_c:0\le k\le N_p(c)-1\}\subset\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))'_\beta \tag{7.3.1.13}$$

*where $\widehat\delta^{(k)}_c$ is the continuous functional obtained as the composition of the Fourier transform*

$$
\mathcal F_S:\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\overline{\chi}|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))
$$

*followed by the Mellin transform $L_S$, and by the $k$th derivative of the point-evaluation functional at $\widehat c\in\Omega(J_{F,S})$, i.e. $\widehat\delta^{(k)}_c$ is uniquely determined by the assignment, on the arbitrary $f\in\mathcal S(\mathbf A_{F,S})$:*

$$\widehat\delta^{(k)}_c(f):=\partial^k_s Z_S(\widehat f,\overline{\chi}|\cdot|^{1-s}_{F,S})|_{s=s_c} \tag{7.3.1.14}$$

## PDF page 345

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **345**

*with $s_c=\frac{2\pi im_{c,v}}{\log(q_v)}-it_v$ for a, equivalently any, choice of $v\in S_p$ such that $c\in \mathcal{U}_{S,v}$.*

*Then the sets in (7.3.1.12), respectively (7.3.1.13), satisfy the following properties:*

(1) *$P_{S,S_p}(\chi|_{J^1_{F,S}})$ and $E_{S,S_p}(\chi|_{J^1_{F,S}})$ are contained within the range of the continuous linear inclusion*

$$
\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})'_\beta\to\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))'_\beta.
$$

(2) *Any enumeration of either countable set $P_{S,S_p}(\chi|_{J^1_{F,S}})$ and $E_{S,S_p}(\chi|_{J^1_{F,S}})$ is an unconditional Schauder basis for*

$$(\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))/\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})))'_\beta \tag{7.3.1.15}$$

equipped with the strong topology.

(3) Their bi-orthogonal sets:

$$P^\vee_{S,S_p}(\chi|_{J^1_{F,S}}),E^\vee_{S,S_p}(\chi|_{J^1_{F,S}})\subset \mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}}) \tag{7.3.1.16}$$

*equipped with the induced enumeration, are absolute Schauder bases.*

(4) *The elements $\psi_{(c,k)}$ of the set $E^\vee_{S,S_p}(\chi|_{J^1_{F,S}})$ further satisfy the following property. For any continuous seminorm $q$ on $\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})$, and for each $v\in S_p$, upon parametrizing the points of $\mathcal{U}_{S_p,v}=\psi^{-1}_v(\mathcal{U}_v)$ as:*

$$c=\chi|\cdot|^{\frac{2\pi im_{c,v}}{\log(q_v)}-it_v}_{F,S},\;m_{c,v}\in\mathbf Z$$

*there exists a polynomial $P\in\mathbf C[X]$ depending on $v$ and such that, as $c$ varies over $\mathcal{U}_{S_p,v}$ as a function of $m_{c,v}$, we have:*

$$q(\psi_{(c,k)})\ll_{q,v}P(m_{c,v}) \tag{7.3.1.17}$$

*uniformly with respect to $0\le k\le N_p(c)-1$, as $|m_{c,v}|\to+\infty$, where the implied constant depends on the chosen enumeration.*

(5) *For every $f\in\mathcal S(\mathbf A_{F,S})$, and for each pair $(c,k)$ as $c$ varies over $\mathcal{U}_{S_p,v}$, then the sequence of complex numbers $\{\widehat\delta^{(k)}_c(\Phi_{F,S,\chi|_{J^1_{F,S}}}(f))\}_{m_{c,v}\in\mathbf Z}$ is of rapid decay, i.e. an element of $\mathcal S(\mathbf Z)$ as a function of $m_{c,v}\in\mathbf Z$.*

Proof. (1) : We first treat the case $E_{S,S_p}(\chi|_{J^1_{F,S}})$.

We choose a continuous homomorphic section $\tau$ to the $S$-idelic norm. We call $x_0\in\mathbf R$ the unique real number such that $\chi(\tau(t))=t^{ix_0}$ as smooth functions on $\mathbf R_{>0}$.

We define $I:=(0,+\infty)\subset\mathbf R$.

By Proposition 2.4.3.1, for every $f\in\mathcal S(\mathbf A_{F,S})$, we have that $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)$ is, as a smooth function on $J_{F,S}$, contained within $\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$. In particular, upon replacing $f$ with $\widehat f$, so is $\Phi_{F,S,\overline{\chi}|_{J^1_{F,S}}}(\widehat f)$.

We define $V_{S_p,\chi}\subset\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ the linear subspace linearly generated by the elements $|\cdot|_{F,S}\Phi_{F,S,\overline{\chi}|_{J^1_{F,S}}}(\widehat f)$, i.e. by the functions defined as the product of the continuous quasi-character $|\cdot|_{F,S}$ and $\Phi_{F,S,\overline{\chi}|_{J^1_{F,S}}}(\widehat f)$.

We endow $V_{S_p,\chi}$ with the quotient topology inherited from $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$.

We note that $V_{S_p,\chi}$ is sequentially dense within $\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ by Lemma D.3.6.1.

As discussed in Remark D.3.3.6, $\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ is stable under multiplication by continuous quasi-characters of $J_{F,S}$ of arbitrary exponent.

By Proposition 5.3.4.4 combined with surjectivity of $\Phi_{F,S,\overline{\chi}|_{J^1_{F,S}}}$ as a continuous linear map:

$$\Phi_{F,S,\overline{\chi}|_{J^1_{F,S}}}:\mathcal S_{00}(\mathbf A_{F,S})\to\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}}) \tag{7.3.1.18}$$

where we refer the reader to (5.3.4.1) from Definition 5.3.4.1 for the construction of the closed subspace $\mathcal S_{00}(\mathbf A_{F,S})\subset\mathcal S(\mathbf A_{F,S})$.

## PDF page 346

**346** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

The surjectivity assertion for (7.3.1.18) follows from the combination of Lemma 5.3.4.3 together with continuity and continuous invertibility of the multiplication operator on $\mathcal S_{00}(\mathbf A_{F,S})$ by a continuous quasi-character of arbitrary exponent, which holds by Lemma 5.3.4.2(3).

We refer the reader to the proof of Proposition 5.3.4.4 for a similar argument.

$\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ is, as a linear subspace of $\mathcal S_I(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, therefore contained within the linear image of $\mathrm H_{0,\mathrm{cont}}(\overline{\chi},\mathcal S(\mathbf A_{F,S}))$ into $\mathcal S_I(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, and hence so is $W:=|\cdot|^{-1}_{F,S}\cdot\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})\subset V_{S_p,\chi}$ by another application of Lemma 5.3.4.2(3) and Remark D.3.3.6.

Since the linear map $\mathrm H_{0,\mathrm{cont}}(\overline{\chi}|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))\to\mathcal S_I(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ is injective, we identify $W$ with its pre-image in $\mathrm H_{0,\mathrm{cont}}(\overline{\chi}|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ and rename such linear subspace of $\mathrm H_{0,\mathrm{cont}}(\overline{\chi}|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ as $W$.

We further denote by $\widehat W$ the pre-image of $W$ in $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ under the Fourier transform

$$
\mathcal F_S:\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\overline{\chi}|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))
$$

from (5.2.4.1) of Theorem 5.2.4.1, a linear topological isomorphism by Theorem 5.2.4.1.

We are not topologizing $W$ nor $\widehat W$.

The idea is to now use $\widehat W$ to produce within the subquotient:

$$(|\cdot|_{F,S}\mathcal F_S\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})))/(|\cdot|_{F,S}\mathcal F_S\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})))$$

a copy of $\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})/P_X\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, where $X$ denotes, following the notation of Situation 4.6.1.1 (see item (2)) from the previous subsection and from Theorem 4.6.1.5, the vector $X=(\pi_v,v\in S_p)$, for $\pi_v$ a choice of local uniformizer in $F^\times_v$ for each $v\in S_p$, and for any choice of ordering on the finitely many elements of $S_p$, and $P_X$ is the operator from (4.6.1.3) from Lemma 4.6.1.3.

Indeed, upon doing so, we will be deducing from Corollary 4.6.3.1 that the continuous linear map:

$$(|\cdot|_{F,S}\mathcal F_S\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})))/(|\cdot|_{F,S}\mathcal F_S\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})))\to\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})/P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}}) \tag{7.3.1.19}$$

is a linear topological isomorphism.

This entails showing that the intersection of $P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ with

$$
(|\cdot|_{F,S}\mathcal F_S\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})))
$$

is indeed the closed subspace

$$
(|\cdot|_{F,S}\mathcal F_S\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})))
$$

which amounts to using the Mellin transform $L_S$ from (5.1.1.2) and the very definition of Weil's Principal Value operators $\mathrm{PV}_{S,S_p}$ from (5.3.1.6) of Definition 5.3.1.4, which $L_S$ turns into a multiplication operator by a product of reciprocal Euler factors, and shows injectivity of (7.3.1.19).

Surjectivity is indeed given by the existence of a copy of $\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ within $(|\cdot|_{F,S}\mathcal F_S\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})))$, constructed using $\widehat W$, for then using the surjectivity assertion in Corollary 4.6.3.1 applied to the $\mathbf R_{>0}$-modulated group $G=J_{F,S}$ and to the continuous character $\overline{\chi}$ of $J_{F,S}$.

Since source and target of (7.3.1.19) are Fréchet spaces, the continuous linear bijection in (7.3.1.19) is therefore a linear topological isomorphism by [NB, Thm.14.4.5(a)].

Theorem 4.6.1.5 and Lemma 7.3.1.5 (which applies by nuclearity of the source, by the First Structure Theorem, Theorem 5.2.3.1(2), and the target, by Theorem D.3.3.7(1)) combined, then provide us with the desired absolute basis property for the set $E_{S,S_p}(\chi|_{J^1_{F,S}})$ from (7.3.1.13), and with the estimates from (7.3.1.17) (see (4.6.1.17)).

We note that indeed the continuous functionals comprising the set $E_{S,S_p}(\chi|_{J^1_{F,S}})$ in (7.3.1.13) are the images under the continuous adjoint of the quotient operator $\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})\to\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})/P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$,

## PDF page 347

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **347**

of the continuous functionals defined in (4.6.1.14), which were shown to be an unconditional Schauder basis in Theorem 4.6.1.5, with its dual basis being absolute. We further refer the reader to the general Lemma 4.1.2.4, which applies since $E=\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})$ is a nuclear Fréchet space, hence Montel, hence complete barrelled and reflexive.

We now complete the argument by discussing the details of the above steps.

We inspect the following diagram of linear operators:

(7.3.1.20)

```latex
\begin{tikzcd}
\mathrm{PV}_{S,S_p}(\widehat W) \arrow[r, "(1)"] \arrow[d, "(\mathrm{a})"'] & \widehat W \arrow[r, "(2)"] \arrow[d, "(\mathrm{b})"] & \widehat W/\mathrm{PV}_{S,S_p}(\widehat W) \arrow[d, "(\mathrm{c})"] \\
\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})) \arrow[r, "(3)"] \arrow[d, "(\mathrm{d})"'] & \mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})) \arrow[r, "(4)"] \arrow[d, "(\mathrm{e})"] & \mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}}) \arrow[d, "(\mathrm{f})"] \\
\mathcal F_S\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})) \arrow[r, "(5)"] \arrow[d, "(\mathrm{g})"'] & \mathcal F_S\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})) \arrow[r, "(6)"] \arrow[d, "(\mathrm{h})"] & \mathcal F_S\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}}) \arrow[d, "(\mathrm{i})"] \\
P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})\times P_X\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) \arrow[r, "(7)"] \arrow[d, "(\mathrm{j})"'] & \mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})\times\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) \arrow[r, "(8)"] \arrow[d, "(\mathrm{k})"] & \mathcal{S}_{X,\overline{\chi}}(J_{F,S}) \arrow[d, "(\mathrm{l})"] \\
P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}}) \arrow[r, "(9)"'] & \mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}}) \arrow[r, "(10)"'] & \mathcal{S}_{X,\overline{\chi}}(J_{F,S})
\end{tikzcd}
```

where:

$$\mathcal{S}_{X,\overline{\chi}}(J_{F,S}):=\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})/P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}}) \tag{7.3.1.21}$$

where the horizontal arrows are:

(1) is the inclusion linear operator induced by the inclusion of the closed subspace $\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ into $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$.

(2) is the quotient map resulting from the inclusion in (1).

(3) is the inclusion linear operator of the closed subspace $\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ into $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$.

(4) is the quotient map resulting from (3).

(5) is the inclusion linear operator of the closed subspace $\mathcal F_S\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ into

$$
\mathcal F_S\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))
$$

obtained upon applying the linear topological isomorphism $\mathcal F_S$ from (5.2.4.1), inherited from the $S$-adelic Fourier transform $\mathcal F_S$ on $\mathcal S(\mathbf A_{F,S})$, onto the continuous inclusion with closed range from (3).

(6) is the quotient map resulting from the inclusion with closed range from (5).

(7) is the product of the inclusions of the closed subspaces $P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, respectively $P_X\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$, into $\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, respectively $\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$.

(8) is the quotient induced by the inclusion with closed range from (7).

(9) is the inclusion of the closed subspace $P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ into $\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$.

(10) is the quotient map induced by the inclusion with closed range from (9).

and the vertical arrows are:

(a) is the inclusion induced by the inclusion of $\widehat W$ into $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$, which we constructed throughout the discussion preceding the diagram in (7.3.1.20), resting on Proposition 5.3.4.4 and Lemma 5.3.4.2(3).

## PDF page 348

**348** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

(b) is the inclusion of $\widehat W$ into $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$, which we constructed throughout the discussion preceding the diagram in (7.3.1.20), resting on Proposition 5.3.4.4 and Lemma 5.3.4.2(3).

(c) is the linear inclusion induced by the top leftmost square being cartesian as a diagram of $\mathbf C$-linear maps among $\mathbf C$-vector spaces. To see this, we proceed as follows: we let $\phi\in\widehat W$ be of the form:

$$\phi=\mathrm{PV}_{S,S_p}(\psi) \tag{7.3.1.22}$$

for some $\psi\in\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$. We compute:

$$Z_S(\mathcal F_S(\phi),\overline{\chi}|\cdot|^{1-s}_{F,S})=Z_S(\mathcal F_S(\mathrm{PV}_{S,S_p}(\psi)),\overline{\chi}|\cdot|^{1-s}_{F,S})=\prod_{v\in S_p}(1-\chi(\mathfrak p_v)q^{-s}_v)Z_S(\mathcal F_S(\psi),\overline{\chi}|\cdot|^{1-s}_{F,S}) \tag{7.3.1.23}$$

where we used the $S$-local functional equation from (3.3.1.2) of Theorem 3.3.1.1, and Weil's Identity from (3.4.1.6) of Theorem 3.4.1.1, to deduce the second of the two identities in (7.3.1.23).

We now use the assumption $\phi\in\widehat W$. We deduce that $|\cdot|_{F,S}\mathcal F_S(\phi)\in\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ (where the linear space $\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ is thought as a linear subspace of $\mathcal F_S\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$). In particular, $(1-\chi(\mathfrak p_v)q^{-s}_v)Z_S(\mathcal F_S(\psi),\overline{\chi}|\cdot|^{1-s}_{F,S})$ is entire, and since $Z_S(\mathcal F_S(\psi),\overline{\chi}|\cdot|^{1-s}_{F,S})$ can only have poles located over

$$
\widehat{\mathcal{U}}_S=\{\widehat c,c\in \mathcal{U}_S\}
$$

by Theorem 3.3.1.1(1), where $(1-\chi(\mathfrak p_v)q^{-s}_v)$ has no zeros for every $v\in S_p$, we deduce that $Z_S(\mathcal F_S(\psi),\overline{\chi}|\cdot|^{1-s}_{F,S})$ is itself entire.

It follows that we have $|\cdot|_{F,S}\mathcal F_S(\psi)\in\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ by Proposition 5.3.4.4, and hence $\psi\in\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ by Remark D.3.3.6 and Lemma 5.3.4.2(3) (as earlier in the argument, $\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ is identified with its linear copy within $|\cdot|_{F,S}\mathcal F_S\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$).

In particular, we have $\mathcal F_S(\psi)\in|\cdot|^{-1}_{F,S}\cdot\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ by another application of Remark D.3.3.6 combined with Lemma 5.3.4.2(3).

It follows that we have $\psi\in\widehat W$, and hence $\phi\in \mathrm{PV}_{S,S_p}(\widehat W)$, which was the assertion to be shown.

(d) is the Fourier transform $\mathcal F_S$, restricted to the closed subspace $\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$.

(e) is the Fourier transform $\mathcal F_S$.

(f) is induced by the Fourier transform $\mathcal F_S$ from (d) and (e).

(g) is the linear topological embedding induced by the linear topological embedding in (h): we need to show that the linear topological embedding in (h) (see below) indeed maps $\mathcal F_S\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ into $P_X\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})\times P_X\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$ and promotes the square within (7.3.1.20) whose edges are (5),(h),(g) and (7), to a cartesian diagram of $\mathbf C$-linear maps among $\mathbf C$-vector spaces.

To see this, we proceed as follows: by Theorem 5.4.1.1, (h) is a linear topological embedding with closed range.

Under Mellin transform (the operator $L_S$ from (5.1.1.2), therefore incorporating in its definition the vertical translation on the complex $s$-plane by $ix_0$, for $x_0\in\mathbf R$ the unique real number such that $\chi(\tau(t))=t^{ix_0}$, for $\tau$ the given choice of continuous homomorphic section to the $S$-idelic norm), it is isomorphic to the operator sending $\Phi_{F,S,\chi|_{J^1_{F,S}}}(f)$ to

$$(Z_S(\widehat f,\overline{\chi}|\cdot|^{1+s}_{F,S}),Z_S(f,\chi|\cdot|^s_{F,S})) \tag{7.3.1.24}$$

and if the pair in (7.3.1.24) is of the form:

$$\left(\prod_{v\in S}(1-\chi(\mathfrak p_v)q^{-s}_v)\phi(s),\prod_{v\in S}(1-\chi(\mathfrak p_v)q^{-s}_v)\psi(s)\right) \tag{7.3.1.25}$$

then $Z_S(f,\chi|\cdot|^s_{F,S})$ has no poles over $\mathcal{U}_{S_p}$ by the $S$-local functional equation of Theorem 3.3.1.1 (since all its poles are located at the poles of $\rho_S(\chi|\cdot|^s_{F,S})$, and multiplication by $\prod_{v\in S}(1-\chi(\mathfrak p_v)q^{-s}_v)$ removes exactly

## PDF page 349

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **349**

the poles located over $\mathcal{U}_{S_p}$, if any, by introducing zeros of $Z_S(\widehat{f}, \overline{\chi}|\cdot|^{1+s}_{F,S})$, and hence of $Z_S(\widehat{f}, \overline{\chi}|\cdot|^{1-s}_{F,S})$, that remove the singularities of $\rho_S(\chi|\cdot|^s_{F,S})$ located over $\mathcal{U}_{S_p}$. Here we are using the assumption $\prod_{v\in S}(1-\chi(\mathfrak p_v)q_v^{-s})\phi(s) = Z_S(\widehat{f}, \overline{\chi}|\cdot|^{1+s}_{F,S})$, where $\psi\in A\mathcal{S}(\mathbf C_{>0}))$.

By Theorem 7.3.1.2(2) applied to $S_0 = S_p$, we have

$$
\Phi_{F,S,\chi|_{J^1_{F,S}}}(f) \in \mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))
$$

which shows that the square within (7.3.1.20) whose edges are (5),(h),(g) and (7), is cartesian, as a diagram of $\mathbf C$-linear maps among $\mathbf C$-vector spaces, which is the assertion to be shown.

(h) is the inclusion of the closed space on the source, into the target, obtained as follows: by Theorem 5.4.1.1, upon choosing a continuous homomorphic section $\tau$ to the $S$-idelic norm, and calling $\omega := \chi|_{J^1_{F,S}}$, the operator $U_{S,\tau}(\Phi_{F,S,\omega}(f)) := (Z_S(f,c), Z_S(\widehat{f},\widehat{c}))$ is a linear topological embedding of $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$ into $A\mathcal{S}(\mathbf C_{>0})\times A\mathcal{S}(\mathbf C_{<1})$. The operator $U_{S,\tau}$ is isomorphic, under conjugation by the Mellin transform ($L_S$ from (5.1.1.2), i.e. incorporating the vertical translation by $ix_0$ on the complex $s$-plane, for $x_0\in\mathbf R$ the unique real number such that $\chi(\tau(t)) = t^{ix_0}$ as smooth functions of $t\in\mathbf R_{>0}$) to the operator sending $\Phi_{F,S,\omega}(f)$ to the pair of functions $(\Phi_{F,S,\omega}(f), |\cdot|_{F,S}J\Phi_{F,S,\omega}(\widehat{f}))$, for $J : \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) \to \mathcal S_{-I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ the inversion linear topological automorphism (see (5.4.2.6)). This is, by Theorem 5.4.2.2, itself a linear topological embedding.

Finally, the operator in (h) sends the element $\Phi_{F,S,\omega}(\widehat{f})$ to the pair $(|\cdot|_{F,S}\Phi_{F,S,\omega}(\widehat{f}), \Phi_{F,S,\omega}(f))$. We deduce from the foregoing that this assignment is itself a linear topological embedding.

(i) is an injective continuous linear operator. Injectivity follows from the diagram comprised by the arrows (g),(7),(5) and (h) being cartesian as a diagram of $\mathbf C$-linear maps among $\mathbf C$-vector spaces, which was shown in point (g) above.

(j) is the projection onto the first factor.

(k) is the projection onto the first factor.

(l) is a linear topological isomorphism, noting that the quotient map in (8) annihilates the second factor in the product $\mathcal S_{-1+I}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}}) \times \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$, because $0\notin I$, and so $P_X\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) = \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$ (because the zeros of $\prod_{v\in S_p}L_v(\chi_v|\cdot|^s_v)$ are all located on the vertical line $i\mathbf R$, and so the orthogonal of $P_X\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) \subset \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$ with respect to the duality

$$
\langle \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}), \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})'\rangle
$$

is trivial. It follows that $P_X\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$ is $\sigma(\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}), \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})')$-dense in $\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$. Since, by Theorem D.3.3.7(1), $\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$ is Montel, $P_X\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$ is strongly dense by [Jar, Part II,Ch.11,§11.5,Prop.1,p.230], and being a closed subspace by Lemma 4.6.1.3(1) applies to $G = J_{F,S}$, $|\cdot|_G = |\cdot|_{F,S}$, $S_0 = X$, we indeed have $P_X\mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}}) = \mathcal S_I(J_{F,S})(\chi|_{J^1_{F,S}})$.

In light of the foregoing, we know that the continuous linear map:

$$
\mathscr E_{S,S_p}(\chi|_{J^1_{F,S}}) \to \mathcal S_{X,\overline\chi}(J_{F,S}) \tag{7.3.1.26}
$$

is a continuous injective linear operator.

Since $\widehat{W}$ is mapped by it onto a copy of $\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ within $|\cdot|_{F,S}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$, such that the restriction to it agrees with the surjective (by Corollary 4.6.3.1) linear operator $\mathcal S_\mathrm{E}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}}) \to \mathcal S_{X,\overline{\chi}}(J_{F,S})$, we deduce that the composition of (c),(f),(i) and (l) is surjective, and hence so is (7.3.1.26). This finishes the proof of the Theorem in the case $E_{S,S_p}(\chi|_{J^1_{F,S}})$.

The case of $P_{S,S_p}(\chi|_{J^1_{F,S}})$, the set of coefficients of principal parts from (7.3.1.12), follows from the previous case by Theorem 7.2.1.4, which relates the functionals $\widehat{\delta}_c^{(k)}$ to the functionals $a_k(\cdot,c)$.

## PDF page 350

**350** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

Note that the correcting coefficients involved in passage from a set of functionals to the other do not preserve the growth and decay conditions asserted in part (4).

To see this, we compute them: from Theorem 7.2.1.4, they are either residues or special values of the local factors of the Hecke $L$-function corresponding to the finite or Archimedean places in $S$, or special values of the reciprocal Euler factors of the Hecke $L$-function corresponding to the finite or Archimedean places in $S$ (through $\widehat{L}_S(\widehat{c})$, defined in (7.2.1.12)). Since the logarithms of prime numbers are $\mathbf Q$-linearly independent, the special values of $1/L_v(\chi_v|\cdot|^s_v)$ at the points $s = \frac{2\pi im}{\log(q_w)} - it_w$, for $v\in S-S_p$ and $w\in S_p$, and for $t_w$ the unique real number $t_w\in [0, 2\pi/\log(q_w))$, with $q_w = N(\mathfrak p_w)$ for $\mathfrak p_w\subset\mathcal O_F$ the unique prime ideal corresponding to the finite place $w\in S$, such that $\chi|\cdot|^{\frac{2\pi im}{\log(q_w)}-it_w}_{F,S} \in \pi_v^{\mathbf Z}$, oscillate too much, since $q_w$ is a prime power coprime to the residue characteristic of the non-Archimedean local field $F_v$: a consequence of Proposition B.5.3.3. $\square$

**DEFINITION 7.3.1.7 (Orbital Schauder Bases - I).** Let $F$ be a number field, $S$ a saturated finite set of places of $F$ containing all the Archimedean places. Assume the notation and choices in Situation 7.3.1.1 are in force.

Let $\chi\in\widetilde{J_{F,S}^1}$ be a choice of continuous character from the chosen set of representatives $\widetilde{J_{F,S}^1}$ for $\widehat{J_{F,S}^1}$. Let $p$ be a prime number such that at least one finite place of $F$ whose residue characteristic is $p$, is contained in $S$.

We refer to the sets $P_{S,S_p}(\chi|_{J^1_{F,S}})$ and their bi-orthogonals $E_{S,S_p}(\chi|_{J^1_{F,S}})$ from Theorem 7.3.1.6, as the:

(1) *Polar Orbital Schauder System*, for $P_{S,S_p}(\chi|_{J^1_{F,S}})$ the set from (7.3.1.12) and $P^\vee_{S,S_p}(\chi|_{J^1_{F,S}})$ is its bi-orthogonal.

(2) *Orbital Fourier Schauder System* is $E_{S,S_p}(\chi|_{J^1_{F,S}})$ is the set from (7.3.1.13) and $E^\vee_{S,S_p}(\chi|_{J^1_{F,S}})$ is its bi-orthogonal.

In light of the topological properties of the Hausdorff locally convex topological $\mathbf C$-vector spaces $\mathrm H_{0,\mathrm{cont}}(F^\times, \mathcal S(\mathbf A_F))$, $\mathrm H_{0,\mathrm{cont}}(\mathcal O^{\times}_{F,S}, \mathcal S(\mathbf A_{F,S}))$ and their isotypes, we deduce the following result on the local and global Spectral and Orbital Schauder Bases.

Finer information on the Orbital Schauder bases will be shown in the first two subsections of the next section, where the main results of this Chapter are discussed.

**COROLLARY 7.3.1.8.** *Let $F$ be a number field, $S$ a finite set of places containing all the Archimedean places, $\chi\in\widehat{C_F}$ a continuous character, unramified outside $S$. Let $\chi_S$ be the unique continuous character of $J_{F,S}$ obtained as the descent of $\chi|_{C_{F,S}}$ by $\widehat{\mathcal O}^{\times}_{\Sigma_F-S}$-invariance.*

*Then the Orbital Schauder Systems from Theorem 7.3.1.2(3) are such that for any choice of enumeration, the resulting Schauder bases satisfy the following conditions:*

*(1) They are equicontinuous, shrinking and boundedly complete bases.*

*(2) Their dual bases are equicontinuous, shrinking and boundedly complete bases.*

*PROOF.* We observe that [Jar, Part II,Ch.14,§14.3,Cor.3,p.296] applies since, by Theorem 5.4.1.1 and by Theorem 6.2.1.1 (see also Corollary 6.2.1.2), $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))$, $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$, are barrelled by [NB, Thm.11.7.2], since they are Fréchet spaces. Their strong duals are Montel by Theorem 5.2.3.1(2). It follows that said bases and their duals are equicontinuous Schauder bases. Being $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))$, $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$ and their strong duals Montel by Theorem 5.2.3.1(2), they are reflexive, and by [Jar, Part II,Ch.14,§14.5,Thm.1(a)], all said bases are shrinking and boundedly complete. $\square$

**7.3.2. Paley-Wiener Levels.** We let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places. Let $\chi\in\widehat{J_{F,S}}$ be a continuous character.

In this subsection we construct a one-parameter family of closed subspaces of $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$, incorporating a support condition on the Fourier transform.

Their aim is to enable an approximation method to perform the final trace calculation of this work in Chapter 7.

## PDF page 351

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **351**

The one-parameter family of closed subspaces of $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$ we are about to construct, collects “most” of the continuous left-translation action of $J_{F,S}$, and it is where most of the trace will be “concentrated”. We will begin explaining this at the end of this Chapter, when we discuss the existence and role of the periodic orbits and fixed points that correspond to the Schauder bases of point-evaluation functionals we are in the process of identifying (see Theorem 7.3.1.6).

**DEFINITION 7.3.2.1 (Absolute Paley-Wiener spaces of level $X$).** Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_\chi$ be the finite set of finite places of $F$ at which $\chi$ is ramified. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Assume $S_\chi\subset S$ and $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.

Let $S_0$ be a saturated finite set of finite places of $F$ disjoint from $S$, and define $S' := S\cup S_0$.

Let $\chi_{S'}$ be the unique continuous character of $J_{F,S'}$ obtained by descending by $\widehat{\mathcal O}^{\times}_{F,\Sigma_F-S'}$-invariance the restriction of $\chi$ to $C_{F,S'}$.

Let $X > 0$ be a real number.

We define:

(1) The linear subspace:

$$
\mathcal S(\mathbf A_{F,S'})_X \subset \mathcal S(\mathbf A_{F,S'}) \tag{7.3.2.1}
$$

of those Schwartz-Bruhat functions over $\mathbf A_{F,S'}$ of the following form:

$$
\pi_{S,S'}(f) = f\otimes\bigotimes_{v\in S_0}1_{\mathcal O^\times_{F_v}} \tag{7.3.2.2}
$$

where $\pi_{S,S'}$ is the transition operator $\mathcal S(\mathbf A_{F,S}) \to \mathcal S(\mathbf A_{F,S'})$ from (2.1.4.2) of Proposition 2.1.4.1, and $f\in\mathcal S(\mathbf A_{F,S})$ is a Schwartz-Bruhat function on $\mathbf A_{F,S}$ whose Fourier transform is compactly supported, with support contained within the hypercube:

$$
Q_X := \prod_{v\in S}\{x_v\in F_v : |x_v|_v\in [-X,X]\} \subset \mathbf A_{F,S}. \tag{7.3.2.3}
$$

We further define

$$
\mathcal S_0(\mathbf A_{F,S'})_X \subset \mathcal S(\mathbf A_{F,S'})_X \tag{7.3.2.4}
$$

to be the codimension-2 subspace obtained by intersecting $\mathcal S(\mathbf A_{F,S'})_X$ with $\ker(\delta_0)$ and $\ker(\widehat{\delta}_0)$ within $\mathcal S(\mathbf A_{F,S'})$.

(2) Let $\rho_{S_0}$ be the Schwartz-Bruhat function on $\widehat{\prod}_{v\in S_0}(F_v,\mathcal O_{F_v})$:

$$
\rho_S := \bigotimes_{v\notin S_0}1_{\mathcal O_{F_v}} \in \mathcal S\left(\widehat{\prod}_{v\in S_0}(F_v,\mathcal O_{F_v})\right). \tag{7.3.2.5}
$$

We define the linear subspaces:

$$
\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \tag{7.3.2.6}
$$

and

$$
\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S_0(\mathbf A_{F,S'})) \subset \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S_0(\mathbf A_{F,S'})) \tag{7.3.2.7}
$$

to be the closure of the linear images under $\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}$ of $\mathcal S(\mathbf A_{F,S'})_X$, respectively of $\mathcal S_0(\mathbf A_{F,S'})_X$. We refer to $\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S_0(\mathbf A_{F,S'}))$, as the *absolute Paley-Wiener subspaces of level $X$* in $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$.

We abbreviate the terminology and refer to the absolute Paley-Wiener levels as the *absolute PW-levels*.

We begin by describing the functions $\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(f)$ on $J_{F,S'}$ as $f$ varies over $\mathcal S(\mathbf A_{F,S'})_X$ and $\mathcal S_0(\mathbf A_{F,S'})_X$.

## PDF page 352

**352** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

**PROPOSITION 7.3.2.2 (Semigroup $J^{\ge 1}_{F,S'}$-action on the absolute PW-levels).** *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_\chi$ be the finite set of finite places of $F$ at which $\chi$ is ramified. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Assume $S_\chi\subset S$ and $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.*

*Let $S_0$ be a saturated finite set of finite places of $F$ disjoint from $S$, and define $S' := S\cup S_0$.*

*Let $\chi_{S'}$ be the unique continuous character of $J_{F,S'}$ obtained by descending by $\widehat{\mathcal O}^{\times}_{F,\Sigma_F-S'}$-invariance the restriction of $\chi$ to $C_{F,S'}$.*

*Let $X > 0$ be a real number.*

*(1) If $Y > X$, then we have:*

$$
\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \mathrm{PW}_{Y}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \tag{7.3.2.8}
$$

*and:*

$$
\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S_0(\mathbf A_{F,S'})) \subset \mathrm{PW}_{Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})). \tag{7.3.2.9}
$$

*The directed unions $\mathrm{PW}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\mathrm{PW}_0(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, of the linear subspaces $\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, as $X\to +\infty$, is sequentially dense in $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S_0(\mathbf A_{F,S'}))$.*

*(2) There exists a real number $\lambda(X) > 0$ depending on $X$ and $\chi$, such that*

$$
\overline{\pi}_{S'}(\Phi_{F,\chi_{S'}|_{J^1_{F,S'}}}(f)) = \Phi_{F,\chi_{S'}|_{J^1_{F,S'}}}(f\otimes\rho_{\Sigma_F-S'})
$$

*for $\rho_{\Sigma_F-S'} := \bigotimes_{v\notin S'}1_{\mathcal O_{F_v}}$, as a function of $g\in C_F$, is supported over $C^{\ge 1/\lambda(X)}_F$, for every $f\in\mathcal S_0(\mathbf A_{F,S'})_X$.*

*(3) There exists a real number $\lambda(X) > 0$ depending on $X$ and $\chi$, such that $\Phi_{F,\chi_{S'}|_{J^1_{F,S'}}}(\widehat{f})$, as a function of $g\in J_{F,S'}$, is supported over $J^{\le\lambda(X)}_{F,S'}$.*

*(4) The linear subspaces $\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, are stable under the continuous left-translation action of the semigroup $J^{\ge 1}_{F,S'}$.*

*PROOF.* (1) : Let $f\in\mathcal S_0(\mathbf A_{F,S'})_X$. Then $f = f_0\otimes\rho_{S_0}$, and $\widehat{f}_0$ is compactly supported and its support is contained in the hypercube $Q_X\subset\mathbf A_{F,S}$.

If $Y > X$, then we have $Q_X\subset Q_Y$, and hence we have $f\in\mathcal S_{Y,0}(\mathbf A_{F,S'})$, which gives $\Phi_{F,\chi_{S'}|_{J^1_{F,S'}}}(f_0\otimes\rho_{S_0}) \in \mathrm{PW}_{Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$.

Upon showing that the directed union of the $\mathcal S_0(\mathbf A_{F,S'})_X$ within $\ker(\delta_0)\cap\ker(\widehat{\delta}_0)\subset\mathcal S(\mathbf A_{F,S})\otimes\rho_S$ is sequentially dense, then so is the directed union of the $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ within $\overline{\pi}_{S,S'}\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))$ (where $\overline{\pi}_{S,S'}$ is the transition operator, a linear topological embedding, induced by $\pi_{S,S'}$ compatibly with $\Phi_{F,S}$, respectively $\Phi_{F,S'}$, as per the First Structure Theorem, Theorem 5.2.1.1), since $\Phi_{F,S,\chi_S|_{J^1_{F,S}}}$ is open.

The directed union of the $\mathcal S_0(\mathbf A_{F,S'})_X$ within $\ker(\delta_0)\cap\ker(\widehat{\delta}_0)\subset\mathcal S(\mathbf A_{F,S})\otimes\rho_{S_0}$ contains the linear subspace

$$
\mathcal{F}^{-1}_{S'}((\mathcal D(\mathbf A_{F,S})\otimes\rho_{S_0})\cap\ker(\delta_0)\cap\ker(\widehat{\delta}_0)) = \mathcal{F}^{-1}_{S'}((\mathcal D(\mathbf A_{F,S})\otimes\rho_{S_0}))\cap\ker(\delta_0)\cap\ker(\widehat{\delta}_0).
$$

Since the Fourier transform $\mathcal F_{S'}$ is a linear topological automorphism of $\mathcal S(\mathbf A_{F,S'})$, it is enough to show that the linear subspace:

$$
V_0 := \mathcal D(\mathbf A_{F,S})\cap\ker(\delta_0)\cap\ker(\widehat{\delta}_0) \subset \mathcal S(\mathbf A_{F,S})\cap\ker(\delta_0)\cap\ker(\widehat{\delta}_0)
$$

is sequentially dense.

Let $f_1,f_2\in\mathcal S(\mathbf A_{F,S})$ be such that $f_1(0) = 0$ and $\widehat{f}_1(0)\neq 0$, $f_2(0)\neq 0$ and $\widehat{f}_2(0) = 0$. We choose $f_1$ and $f_2$ to be compactly supported.

## PDF page 353

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **353**

We have:

$$
(\mathcal S(\mathbf A_{F,S})\cap\ker(\delta_0)\cap\ker(\widehat{\delta}_0))\oplus\mathbf C\cdot f_1\oplus\mathbf C\cdot f_2 = \mathcal S(\mathbf A_{F,S}) \tag{7.3.2.10}
$$

linearly and topologically.

By [Sch-a, Ch.VII,§3,Thm.III,p.237], $\mathcal D(\mathbf A_{F,S})\subset\mathcal S(\mathbf A_{F,S})$ is sequentially dense. The closure in the direct sum within the left side of (7.3.2.10) of $X_0\oplus\mathbf C\cdot f_1\oplus\mathbf C\cdot f_2$ contains $\mathcal D(\mathbf A_{F,S})$ by [Jar, Part I,Ch.4,§4.5,Cor.4,p.82], and hence it cannot be a proper closed subspace. It follows that $V_0$ is sequentially dense in $\ker(\delta_0)\cap\ker(\widehat{\delta}_0)$.

The case of $\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, without incorporating the two linear conditions $f(0) = \widehat{f}(0) = 0$, is seen by means of the same argument.

(2) and (3) : By Theorem 2.2.3.2, we have:

$$
\Phi_{F,\chi|_{C^1_F}}(f\otimes\rho_{\Sigma_F-S'})(g) = |g|^{-1}_F\Phi_{F,\overline{\chi}|_{C^1_F}}(\widehat{f}\otimes\rho_{\Sigma_F-S'})(g^{-1})
$$

as continuous functions on $C_F$. It is therefore enough to show that there exists a real number $\lambda(X) > 0$ such that $\Phi_{F,\overline{\chi}|_{C^1_F}}(\widehat{f}\otimes\rho_{\Sigma_F-S'})$ vanishes outside of $C^{\le\lambda(X)}_F$.

We let $f = f_0\otimes\rho_{S_0}$ for some $f_0\in\mathcal S(\mathbf A_{F,S})$ whose Fourier transform is compactly supported, with support contained within $Q_X\subset\mathbf A_{F,S}$ (see (7.3.2.3)), and $f_0(0) = \widehat{f}_0(0) = 0$.

We call $f_1 := \widehat{f}_0$ and note that $f_1$ is supported over $Q_X\subset\mathbf A_{F,S}$. Moreover, we have $\widehat{f} = f_1\otimes\rho_{S_0}$ since $\chi$ is unramified outside $S$.

We let $\tau$ be a continuous homomorphic section to the idelic norm with image contained within $F^\times_{v_0}\subset\mathrm{GL}_1(\mathbf A_{F,S_\infty})\times\{1\}\subset\mathrm{GL}_1(\mathbf A_F)$ for a choice $v_0\in S_\infty$ of Archimedean place.

The condition on $(\xi,g_0,t)\in F^\times\cdot E^1_F\times\mathbf R_{>0}$, for $E^1_F$ the global idelic fundamental domain from (A.2.3.14) of Definition A.2.3.6:

$$
\widehat{f}(\xi g_0\tau(t)) \neq 0 \tag{7.3.2.11}
$$

reads $|\xi(g_0)_v|_v\le 1$ for all $v\in\Sigma_{F,f} - S_\chi$, $|\xi(g_0)_v|_v = 1$ for all $v\in S_\chi$, and $|\xi(g_0)_v|_v\le X$ for all $v\in S_\infty-\{v_0\}$, and $|\xi(g_0)_{v_0}\tau(t)|_{v_0}\le X$.

We then obtain that $\xi$ must vary over the nonzero elements of a fractional ideal $I_\chi\subset F^\times$, whose image into $\mathbf A_{F,S}$ is a discrete subset $I_{S,\chi}\subset\mathbf A_{F,S}$.

Since $E^1_F$, and hence its image in $\mathrm{GL}_1(\mathbf A_{F,S})$ under the continuous quotient $\mathrm{GL}_1(\mathbf A_F)\to\mathrm{GL}_1(\mathbf A_{F,S})$, is relatively compact, we deduce that for (7.3.2.11) to hold, we must have $|\xi|_v\le X_v$ for each $v\in S-\{v_0\}$ and for real numbers $X_v\ge X$. There exists a real number $X_{v_0}\ge X$ such that $|\xi(g_0)_{v_0}\tau(t)|_{v_0}\le X$ for every $g_0\in E^1_F$, implies that $|\xi\tau(t)|_{v_0}\le X_{v_0}$ also holds.

Since, for any fixed $Y > 0$, $|\xi|_{v_0}\le Y$ holds for at most finitely many $\xi\in I_{S,\chi}$, in light of discreteness of $I_{S,\chi}$ and the fact that the boundedness conditions $|\xi|_v\le X_v$ for all Archimedean places $v\neq v_0$ already all hold, we deduce that the condition $t = |\xi\tau(t)|_{v_0}\le X_{v_0}$ holds only for $t\in (0,\lambda(X))$ for some $\lambda(X) > 0$. Formation of $I_{S,\chi}$ does not depend on $f_1$, but only on $\chi$.

Alternatively, we observe that we have $|I_{S,\chi}|_{F,S} = \prod_{v\in S}|I_{S,\chi}|_v\subset [a,+\infty)$ for some real number $a > 0$. Moreover, we have:

$$
Q_X\cap\mathrm{GL}_1(\mathbf A_{F,S})\subset B_X := \{x\in\mathrm{GL}_1(\mathbf A_{F,S}) : |x|_{F,S}\le X^{|S|}\}
$$

and since $I^{-1}_{S,\chi}\cdot B_X\subset a^{-1}\cdot B_X$, and since the image of $E^1_F$ in $\mathrm{GL}_1(\mathbf A_{F,S})$ is relatively compact, hence contained in a large enough compact subset $K\subset\mathrm{GL}_1(\mathbf A_{F,S})$, we deduce that (7.3.2.11) holds so long as $\tau(t)\in K^{-1}\cdot a^{-1}\cdot B_X$, a compact subset of $\mathbf A_{F,S}$.

The subset $(K^{-1}\cdot a^{-1}\cdot B_X)\times\prod_{v\in S'}\mathcal O_{F_v}$ is compact within $\mathbf A_{F,S'}$. There therefore exists $\lambda(X) > 0$ such that $\tau([\lambda(X),+\infty))\subset\mathrm{GL}_1(\mathbf A_{F,S'})$ does not intersect $((K^{-1}\cdot a^{-1}\cdot B_X)\times\prod_{v\in S'}\mathcal O_{F_v})\cap\mathrm{GL}_1(\mathbf A_{F,S'})$ within $\mathrm{GL}_1(\mathbf A_{F,S'})$. This proves (3).

## PDF page 354

**354** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

(4) : To see this, we choose a continuous homomorphic section $\tau$ to the idelic norm, whose image is contained within $\mathrm{GL}_1(\mathbf A_{F,S})\times\{1\}\subset\mathrm{GL}_1(\mathbf A_F)$.

Let $g_0\in\mathrm{GL}_1(\mathbf A_{F,S'})^1$ be an arbitrary element. Then if $f_0\in\mathcal S(\mathbf A_{F,S})$ is such that $\widehat{f}_0$ is supported over $Q_X\subset\mathbf A_{F,S}$ and $f_0(0) = \widehat{f}_0(0) = 0$, the element $\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(f_0\otimes\rho_{S_0})(g^{-1}_0x)$ as a continuous function of $x\in J_{F,S'}$, equals $\overline{\chi}_{S'}(g_0)\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(f_0\otimes\rho_{S_0})(x)$, i.e. a nonzero scalar multiple of $\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(f_0\otimes\rho_{S_0})$, and it is therefore again an element of $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$.

We let $t\in\mathbf R_{>0}$ be an arbitrary positive real number. Then as functions of $x\in\mathbf A_{F,S'}$, both $f_0\otimes\rho_{S_0}(x)$ and $f_0\otimes\rho_{S_0}(\tau(t)^{-1}x)$ are in the intersection of the two hyperplanes $\ker(\delta_0)$ and $\ker(\widehat{\delta}_0)$.

Since $\widehat{f}_0$ is compactly supported over the hypercube $Q_X\subset\mathbf A_{F,S}$, then $\mathcal F_{S'}(f_0\otimes\rho_{S_0}(\tau(t)^{-1}x)) = t\cdot\widehat{f}_0(\tau(t)x)\rho_{S_0}(x_{S'})$ (where $x_{S'}$ is the projection of $x$ onto the $S'$-indexed coordinates) is nonzero only if $(\tau(t)x)_S = \tau(t)x_S\in Q_X\subset\mathbf A_{F,S}$, which reads $x_S\in\tau(t)^{-1}\cdot Q_X\subset Q_X$.

This shows that the effect of the continuous left translation action of $\mathrm{GL}_1(\mathbf A_{F,S'})^{\ge 1}$ on $f_0\otimes\rho_{S_0}$ preserves the defining conditions of $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$.

We deduce that we have:

$$
\rho_{F,S'}(J^{\ge 1}_{F,S'},\mathrm{PW}_{S,X,0}(\chi|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))) \subset \mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))
$$

and hence $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ is a continuous sub-representation of the abelian semigroup $J^{\ge 1}_{F,S'}$, upon endowing $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ with the subspace topology inherited from $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$.

The same argument also applies to show the same assertion for $\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ $\square$

The reason why we termed the closed subspaces

$$
\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))
$$

and its closed codimension-2 subspace $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, *absolute* Paley-Wiener Levels, is that the defining constraint on the Fourier transform of the elements of $\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$ is assigned by requiring that the $S$-local tensor factor of the arbitrary representative

$$
\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(f_S\otimes\rho_{S_0})
$$

for $\rho_{S_0}$ as defined in (7.3.2.5) and $f_S\in\mathcal S_0(\mathbf A_{F,S})$ (such representative always existing by the Fifth Structure Theorem.

See Theorem 6.2.1.1) to have Fourier transform $\widehat{f}_S$ that is supported over the compact hypercube $Q_X\subset\mathbf A_{F,S}$ of (7.3.2.3), as opposed to being supported over the closed $\mathcal O^{\times}_{F,S}$-invariant subset

$$
\widetilde{Q}_Y := \{x\in\mathbf A_{F,S} : \prod_{v\in S}|x|_v\le Y\}.
$$

Note that for $Y = X^{|S|}$, the latter contains the former.

We will now discuss and study a variant of the absolute Paley-Wiener Levels, by using $\widetilde{Q}_Y$ as opposed to $Q_X$: we will be terming them *invariant Paley-Wiener Levels*, and the absolute Paley-Wiener levels will be used to provide examples of elements of the invariant Paley-Wiener Levels.

**DEFINITION 7.3.2.3 (Invariant Paley-Wiener spaces of level $Y$).** Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_\chi$ be the finite set of finite places of $F$ at which $\chi$ is ramified. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Assume $S_\chi\subset S$ and $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.

Let $S_0$ be a saturated finite set of finite places of $F$ disjoint from $S$, and define $S' := S\cup S_0$.

Let $\chi_{S'}$ be the unique continuous character of $J_{F,S'}$ obtained by descending by $\widehat{\mathcal O}^{\times}_{F,\Sigma_F-S'}$-invariance the restriction of $\chi$ to $C_{F,S'}$.

## PDF page 355

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **355**

Let $Y > 0$ be a real number.

We define:

(1) The linear subspace:

$$
\widetilde{\mathcal S}(\mathbf A_{F,S'})_Y \subset \mathcal S(\mathbf A_{F,S'}) \tag{7.3.2.12}
$$

of those Schwartz-Bruhat functions over $\mathbf A_{F,S'}$ of the following form:

$$
\pi_{S,S'}(f) = f\otimes\bigotimes_{v\in S_0}1_{\mathcal O^\times_{F_v}} \tag{7.3.2.13}
$$

where $\pi_{S,S'}$ is the transition operator $\mathcal S(\mathbf A_{F,S}) \to \mathcal S(\mathbf A_{F,S'})$ from (2.1.4.2) of Proposition 2.1.4.1, and $f\in\mathcal S(\mathbf A_{F,S})$ is a Schwartz-Bruhat function on $\mathbf A_{F,S}$ whose Fourier transform is compactly supported, with support contained within the hypercube:

$$
\widetilde{Q}_Y := \{x\in\mathbf A_{F,S} : \prod_{v\in S}|x|_v\le Y\} \subset \mathbf A_{F,S}. \tag{7.3.2.14}
$$

We further define:

$$
\widetilde{\mathcal S}_0(\mathbf A_{F,S'})_Y \subset \widetilde{\mathcal S}(\mathbf A_{F,S'})_Y \tag{7.3.2.15}
$$

to be the codimension-2 subspace obtained by intersecting $\widetilde{\mathcal S}(\mathbf A_{F,S'})_Y$ with $\ker(\delta_0)$ and $\ker(\widehat{\delta}_0)$ within $\mathcal S(\mathbf A_{F,S'})$.

(2) The linear subspaces:

$$
\widetilde{\mathrm{PW}}_{S,Y}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \tag{7.3.2.16}
$$

and

$$
\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S'}}, \mathcal S_0(\mathbf A_{F,S'})) \tag{7.3.2.17}
$$

to be the closures of the linear images under $\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}$ of $\widetilde{\mathcal S}_0(\mathbf A_{F,S'})_Y$, respectively under $\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}$ of $\widetilde{\mathcal S}_0(\mathbf A_{F,S'})_Y$.

We refer to $\widetilde{\mathrm{PW}}_{S,Y}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, as the *invariant Paley-Wiener subspace of level $Y$* in $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S_0(\mathbf A_{F,S'}))$.

We abbreviate the terminology and refer to the invariant Paley-Wiener levels as the *invariant PW-levels*.

The following is an analog of Proposition 7.3.2.2:

**PROPOSITION 7.3.2.4 (Semigroup $J^{\ge 1}_{F,S'}$-action on the invariant PW-levels).** *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_\chi$ be the finite set of finite places of $F$ at which $\chi$ is ramified. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Assume $S_\chi\subset S$ and $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.*

*Let $S_0$ be a saturated finite set of finite places of $F$ disjoint from $S$, and define $S' := S\cup S_0$.*

*Let $\chi_{S'}$ be the unique continuous character of $J_{F,S'}$ obtained by descending by $\widehat{\mathcal O}^{\times}_{F,\Sigma_F-S'}$-invariance the restriction of $\chi$ to $C_{F,S'}$.*

*Let $Y > 0$ be a real number.*

*(1) If $Y' > Y$, then we have:*

$$
\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \widetilde{\mathrm{PW}}_{S,Y',0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \tag{7.3.2.18}
$$

*and:*

$$
\widetilde{\mathrm{PW}}_{S,Y}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \widetilde{\mathrm{PW}}_{S,Y'}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})). \tag{7.3.2.19}
$$

## PDF page 356

**356** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

*The directed unions $\widetilde{\mathrm{PW}}_0(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\widetilde{\mathrm{PW}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, of the linear subspaces $\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\widetilde{\mathrm{PW}}_{S,Y}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, as $Y\to +\infty$, is sequentially dense in $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S_0(\mathbf A_{F,S'}))$, respectively $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$.*

*(2) There exists a real number $\lambda(Y) > 0$ depending on $Y$ and $\chi$, such that $\Phi_{F,\chi|_{C^1_F}}(f\otimes\rho_{\Sigma_F-S'})$, as a function of $g\in C_F$, is supported over $C^{\ge 1/\lambda(Y)}_F$, for every $f\in\widetilde{\mathcal S}_0(\mathbf A_{F,S'})_Y$.*

*(3) The linear subspaces $\widetilde{\mathrm{PW}}_{S,Y}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, are stable under the continuous left-translation action of the semigroup $J^{\ge 1}_{F,S'}$.*

*(4) The following inclusions hold:*

$$
\mathrm{PW}_{S,X}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \widetilde{\mathrm{PW}}_{S,X^{|S|}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \tag{7.3.2.20}
$$

*and*

$$
\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \subset \widetilde{\mathrm{PW}}_{S,X^{|S|},0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})). \tag{7.3.2.21}
$$

*PROOF.* (1) : Let $f_0\in\mathcal S_0(\mathbf A_{F,S})$ and assume that $\widehat{f}_0$ is supported over $\widetilde{Q}_Y$, which is contained in $\widetilde{Q}_{Y'}$, and hence the containments in (7.3.2.18) and (7.3.2.19) both hold. The sequential denseness assertion follows from (4), to be proved below, and Proposition 7.3.2.2(1).

(2) and (3) : By Theorem 2.2.3.2, for any $f\in\widetilde{\mathcal S}_0(\mathbf A_{F,S'})_Y$, in order to show that there exists $\lambda(Y) > 0$ such that $\Phi_{F,\chi|_{C^1_F}}(f\otimes\rho_{\Sigma_F-S'})$ is supported over $C^{\ge 1/\lambda(Y)}_F$, it is enough to show that there exists $\lambda(Y) > 0$ such that $\Phi_{F,\overline{\chi}|_{C^1_F}}(\widehat{f}\otimes\rho_{\Sigma_F-S'})$ is supported over $(0,\lambda(Y)]$.

We replace $f$ with $\widehat{f}$, and write $f = f_0\otimes\rho_{\Sigma_F-S'}$ for some $f_0\in\mathcal S_0(\mathbf A_{F,S})$, noting that we have $\widehat{\rho}_{\Sigma_F-S'} = \rho_{\Sigma_F-S'}$, supported over $\widetilde{Q}_Y$.

We choose a continuous homomorphic section $\tau$ to the idelic norm, whose image is contained in $\mathrm{GL}_1(\mathbf A_{F,S_\infty})\times\{1\}\subset\mathrm{GL}_1(\mathbf A_F)$. We let $g_0\in E^1_F$ be arbitrary, where $E^1_F$ is the idelic fundamental domain from (A.2.3.14), and let $t\in\mathbf R_{>0}$ be arbitrary.

The condition on $\xi\in F^\times$:

$$
f(\xi g_0\tau(t)) \neq 0 \tag{7.3.2.22}
$$

implies that the following inequalities all hold: $|\xi|_v\le 1$ for all $v\notin S$, since $|g_0|_v\le 1$ for all such $v$, since $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.

We choose a splitting of the quotient homomorphism $F^\times\to F^\times/\mathcal O^{\times}_{F,S}$ (which exists, its target being a free abelian group), and write $F^\times = \mathcal O^{\times}_{F,S}\cdot\Gamma$, where $\Gamma$ is a free abelian subgroup of $F^\times$ mapped isomorphically onto $F^\times/\mathcal O^{\times}_{F,S}$, such that $\Gamma\cap\mathcal O^{\times}_{F,S} = 1$.

Since $|\Gamma|_{F,S}\subset [1,+\infty)$, we have that, for each $\gamma\in\Gamma$, the condition on $g_{0,S}\tau(t)$:

$$
f_0(\gamma g_{0,S}\tau(t)) \neq 0
$$

for $g_{0,S}$ the projection of $g_0$ onto $\mathrm{GL}_1(\mathbf A_{F,S})$, implies $g_{0,S}\tau(t)\in\gamma^{-1}\cdot\widetilde{Q}_Y\subset\widetilde{Q}_Y$, and so $\tau(t)\in K^{-1}_S\cdot\widetilde{Q}_Y$, where $K_S$ is the relatively compact image of $E^1_F$ onto $\mathrm{GL}_1(\mathbf A_{F,S})^1$ under the quotient homomorphism $\mathrm{GL}_1(\mathbf A_F)^1\to\mathrm{GL}_1(\mathbf A_{F,S})^1$.

It follows that we have $t = |\tau(t)|_{F,S}\in |K^{-1}_S\cdot\widetilde{Q}_Y|_{F,S}\subset\mathbf R_{\ge 0}$, which is relatively compact, since $|\cdot|_{F,S}$ is continuous. It follows that there exists $\lambda(Y) := \sup |K^{-1}_S\cdot\widetilde{Q}_Y|_{F,S} < +\infty$, such that $\Phi_{F,\overline{\chi}|_{C^1_F}}(f)$ is supported over $(0,\lambda(Y)]$.

The Mellin transform $L_S$ from (5.1.1.2), respectively $L$ from (5.1.1.1), turns the action by left-translation of $g_0\in J^1_{F,S}$, respectively $g_0\in C^1_F$, into multiplication by $\overline{\chi}_S(g_0)$, respectively $\overline{\chi}(g_0)$, and therefore preserves the linear subspaces $\widetilde{\mathrm{PW}}_{S,Y}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$.

## PDF page 357

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **357**

Upon reprising the argument from the foregoing, for any $t\in [1,+\infty)$ we have:

$$
\mathcal F_{S'}(f_0(\tau(t)^{-1}x_S)\rho_{S_0}(x_{S_0})) = t\widehat{f}_0(\tau(t)x_S)\rho_{S_0}(x_{S_0}) \neq 0
$$

which implies that $\tau(t)x\in\widetilde{Q}_Y$, which reads $x\in\tau(t)^{-1}\cdot\widetilde{Q}_Y\subset\widetilde{Q}_Y$.

It follows that the continuous left-translation action of $J^{\ge 1}_{F,S'}$ preserves the linear subspaces $\widetilde{\mathrm{PW}}_Y(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$, respectively $\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))$.

(4) : Both inclusions in (7.3.2.20) are seen to hold upon observing that we have $Q_X\subset\widetilde{Q}_{X^{|S|}}$ within $\mathbf A_{F,S}$. $\square$

**7.3.3. Orbital Schauder Bases on the Paley-Wiener Levels.** In this subsection, we extend Weil's Principal Value operators $\mathrm{PV}_{S,S_0}$, introduced in Definition 5.3.1.4 of §5.3.1, for $S_0$ a finite set of finite places satisfying certain saturation properties, to the invariant and the asbolute Paley-Wiener spaces introduced in the previous subsection.

This will enable us to construct Schauder bases for the orthogonals to their range, even on the Paley-Wiener spaces, building on the work that was done in §6.3.2 on the Orbital Schauder Bases.

The Orbital Schauder Bases on the Paley-Wiener levels will then enable us to deconstruct the global geometric kernel $k^{\mathrm{geom}}_{\varphi,a,s}$ from 10.4.3.27 of Chapter 6, “lifted” to a kernel on $\mathrm{GL}_1(\mathbf A_F)\times C_F$ using the methods from §12.2.1, step by step, into an $S$-local kernel whose integral along the diagonal can be computed explicitly with a volume calculation.

We recall from Situation 7.3.1.1 the following:

SITUATION 7.3.3.1. Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places.

Let $S_0$ be a finite set of finite places of $F$ satisfying the following assumptions:

(1) $S_0\cap S = \varnothing$.

(2) We assume $S_0$ is saturated in the sense of Situation 7.3.1.1(1): if $v\in S_0$ and $p$ is the residue characteristic of $v$, then all places $w$ of $F$ of residue characteristic $p$ are also contained in $S_0$. We denote by $\{p_1,\dots,p_N\}$ the finitely many residue characteristics of the finite places contained in $S_0$, and call $S_{p_k}$, for $1\le k\le N$, the finite set of those finite places of $F$ whose residue characteristic is $p_k$. In particular, we have $S_0 = \bigcup_{1\le k\le N}S_{p_k}$.

(3) We assume $S$ is so large so as to ensure $\mathrm{Pic}(\mathcal O_{F,S}) = 1$.

We define $S' := S\cup S_0$.

**PROPOSITION 7.3.3.2 (Weil's Principal Values on the Paley-Wiener Levels).** *Let $F$ be a number field. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Let $\chi\in\widehat{C_F}$ be a continuous character, unramified outside $S$. Let $S_0$ be a saturated finite set of finite places disjoint from $S$, and define $S' := S\cup S_0$.*

*Assume the choices and assumptions from Situation 7.3.3.1 are in force.*

*Let $X,Y > 0$ be real numbers.*

*For any saturated finite subset $S_1\subset S_0$, Weil's Principal Value Operator:*

$$
\mathrm{PV}_{S',S_1} : \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'})) \to \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}}, \mathcal S(\mathbf A_{F,S'}))
$$

## PDF page 358

**358** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

*from* (5.3.1.9), *extends by continuity to the operators* $\mathrm{PV}^{\mathrm{ABS}}_{S',S_1}$ *and* $\widetilde{\mathrm{PV}}_{S',S_1}$ *below, promoting the following to a commutative diagram of continuous linear operators:*

(7.3.3.1)

```latex
\begin{tikzcd}
\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'})) \arrow[r] \arrow[d, "\mathrm{PV}^{\mathrm{ABS}}_{S',S_1}"'] & \widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'})) \arrow[r] \arrow[d, "\widetilde{\mathrm{PV}}_{S',S_1}"'] & \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S_0(\mathbf A_{F,S'})) \arrow[d, "\mathrm{PV}_{S',S_1}"] \\
\mathrm{PW}_{S,X',0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'})) \arrow[r] & \widetilde{\mathrm{PW}}_{S,Y',0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'})) \arrow[r] & \mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S_0(\mathbf A_{F,S'}))
\end{tikzcd}
```

*compatible with the structures of continuous representations of the closed abelian semigroup* $J^{\ge 1}_{F,S'}\subset J_{F,S'}$, *where* $X'$ *and* $Y'$ *are related to* $X$ *and* $Y$ *by the following formulas:*

$$
Y\ge X^{|S|},\quad X'=q_{S_1}X,\quad Y'=q_{S_1}Y \tag{7.3.3.2}
$$

*with* $q_{S_1}:=\prod_{v\in S_1}N(\mathfrak p_v)$, *where, for each* $v\in S_1$, $\mathfrak p_v\subset\mathcal O_F$ *is the unique prime ideal associated to the finite place* $v\in S_1$.

PROOF. Since $\mathrm{PV}_{S',S_1}$ is already defined on the level of the Hausdorff locally convex topological $\mathbf C$-vector space $\mathcal S(\mathbf A_{F,S'})$ of $S'$-local Schwartz-Bruhat functions on the $S'$-adeles $\mathbf A_{F,S'}$, to prove the existence of $\mathrm{PV}^{\mathrm{ABS}}_{S',S_1}$ and $\widetilde{\mathrm{PV}}_{S',S_1}$ it is sufficient to show that $\mathrm{PV}_{S',S_1}:\mathcal S(\mathbf A_{F,S'})\to\mathcal S(\mathbf A_{F,S'})$ sends the closed subspace $\mathcal S_0(\mathbf A_{F,S'})_X$, respectively $\widetilde{\mathcal S}_0(\mathbf A_{F,S'})_Y$, up to averaging under the continuous left-translation action of $\mathcal O^\times_{F,S'}$ on $\mathcal S(\mathbf A_{F,S'})$, into $\mathcal S_0(\mathbf A_{F,S'})_{X'}$, respectively $\widetilde{\mathcal S}_0(\mathbf A_{F,S'})_{Y'}$, for some $X'$, $Y'$ related to $X$, $Y$.

Since $\mathrm{PV}_{S',S_1}=\prod_{v\in S_1}\mathrm{PV}_v$, the product denoting composition of continuous linear endomorphisms of $\mathcal S(\mathbf A_{F,S'})$, we show that the same assertions hold for the operator $\mathrm{PV}_v$ for a single finite place $v$ of $F$ contained in $S_1$.

We denote by $\mathfrak p_v\subset\mathcal O_F$ the unique prime ideal of $\mathcal O_F$ associated to the finite place $v\in S_1$, and by $q_v$ its norm $N(\mathfrak p_v)$.

We let $\pi_v\in\mathcal O_{F_v}$ be a choice of uniformizer at $v$.

Then for any $f\in\mathcal S(\mathbf A_{F,S'})$, $\mathrm{PV}_v(f)=f-\rho_{F,S'}(\pi_v,f)$, where $\rho_{F,S'}$ denotes the continuous left-translation action of $\mathrm{GL}_1(\mathbf A_{F,S'})$ on $\mathcal S(\mathbf A_{F,S'})$, i.e. $\rho_{F,S'}(g,f)(x):=f(g^{-1}x)$ as functions of $x\in\mathbf A_{F,S'}$.

We let $f_0\in\mathcal S_0(\mathbf A_{F,S})$ be such that $\widehat f_0$ is compactly supported over $Q_X$, respectively supported (not necessarily compactly) over $\widetilde Q_Y$.

Then $\mathrm{PV}_v(f_0\otimes\rho_{S_0})$ is the Schwartz-Bruhat function, up to a linear topological isomorphism induced by reordering of the finite places of $F$:

$$
\mathrm{PV}_v(f_0\otimes\rho_{S_0})=f_0\otimes\rho_{S^v_0}\otimes 1_{\mathcal O^\times_{F_v}}=f_0\otimes\rho_{S^v_0}\otimes 1_{\mathcal O_{F_v}}-f_0\otimes\rho_{S^v_0}\otimes 1_{\pi_v\mathcal O_{F_v}}
$$

where $\rho_{S^v_0}:=\bigotimes_{w\in S_0,w\ne v}1_{\mathcal O_{F_w}}\in\mathcal S(\widehat\prod_{w\in S_0,w\ne v}(F_w,\mathcal O_{F_w}))$.

We now show that there exist real numbers $X'$, $Y'$, such that there exists $f_1\in\mathcal S_0(\mathbf A_{F,S})$ such that $\widehat f_1$ is compactly supported with support contained within $Q_{X'}$, respectively supported (not necessarily compactly) over $\widetilde Q_{Y'}$, satisfying the following property:

$$
\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(\mathrm{PV}_v(f_0\otimes\rho_{S_0}))=\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(f_1\otimes\rho_{S_0}).
$$

To this end, it suffices to find $f_2\in\mathcal S_0(\mathbf A_{F,S})$ such that $\widehat f_2$ is compactly supported with support contained within $Q_{X'}\subset\mathbf A_{F,S}$, respectively supported (not necessarily compactly) over $\widetilde Q_{Y'}$, such that:

$$
\Phi_{F,S',\chi|_{J^1_{F,S'}}}(f_0\otimes\rho_{S^v_0}\otimes 1_{\pi_v\mathcal O_{F_v}})=\Phi_{F,\chi_{S'}|_{J^1_{F,S'}}}(f_2\otimes\rho_{S_0}) \tag{7.3.3.3}
$$

## PDF page 359

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **359**

in which case we define $f_1:=f_0-f_2$. Since $\mathrm{Pic}(\mathcal O_{F,S})=1$, we can arrange $\pi_v$ to be the image in $F_v$ of an $S$-integer $\xi_0$, satisfying $|\xi_0|_w=1$ for all $w\notin S$, $w\ne v$. We call $\xi_{0,S}$ the image of $\xi_0$ in $\mathrm{GL}_1(\mathbf A_{F,S})$ under the composition $F^\times\to\mathrm{GL}_1(\mathbf A_F)\to\mathrm{GL}_1(\mathbf A_{F,S})$, the second map being the continuous homomorphic projection from the global ideles to the $S$-ideles.

We define $f_2:=\rho_{F,S}(\xi^{-1}_{0,S},f_0)$, i.e. $f_2(x):=f_0(\xi_{0,S}x)$ as a function of $x\in\mathbf A_{F,S}$. Up to left-translation of $\rho_{S_0}$ by an element of $\prod_{w\in S_0}\mathcal O^\times_{F_w}$, which does not change $\rho_{S_0}$ and $\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(f_2\otimes\rho_{S_0})$ since $\chi$ is unramified outside $S$, we have that (7.3.3.3) holds.

Since $f_0(0)=\widehat f_0(0)=0$, the same vanishing conditions are satisfied by $f_2$.

Moreover, the Fourier transform $\mathcal F_S(f_2)$ is supported over $\xi_{0,S}\cdot Q_X$, respectively $\xi_{0,S}\cdot\widetilde Q_Y$ (noting that the Fourier transform conjugates the left-translation action by $\mathrm{GL}_1(\mathbf A_{F,S})$ on $\mathcal S(\mathbf A_{F,S})$ over to the right-translation action by $\mathrm{GL}_1(\mathbf A_{F,S})$ on $\mathcal S(\widehat{\mathbf A}_{F,S})\simeq\mathcal S(\mathbf A_{F,S})$).

We have:

$$
\xi_{0,S}\cdot Q_X\subset Q_{q_vX},\ \xi_{0,S}\cdot\widetilde Q_Y=\widetilde Q_{q_vY}. \tag{7.3.3.4}
$$

We define $X':=q_vX$ and $Y':=q_vY$ and deduce that indeed $\mathrm{PV}^{\mathrm{ABS}}_{S',S_1}$ and $\widetilde{\mathrm{PV}}_{S',S_1}$ exist, for $X':=q_{S_0}X$ and $Y':=q_{S_0}Y$.

By Proposition 7.3.2.4, the condition $Y\ge X^{|S|}$ ensures that the leftmost top and bottom continuous inclusion operators in (7.3.3.1) exist.

It remains to show that the sub-squares of the diagram in (7.3.3.1) are cartesian as diagrams of $\mathbf C$-linear maps among $\mathbf C$-vector spaces.

$\square$

Before we state and prove the main Theorem of this section, we introduce some terminology and notation:

Definition 7.3.3.3 (p-primary PW Orbital Quotients). Let $F$ be a number field, $S$ a saturated finite set of places of $F$ containing all the Archimedean places. Let $S_0$ be a saturated finite set of finite places of $F$ disjoint from $S$. We define $S':=S\cup S_0$.

Let $p$ be a prime number such that $S_p\subset S_0$.

Assume the notation and choices in Situation 7.3.3.1 are in force.

Let $X$, $Y>0$ be real numbers. Denote by $q_{S_p}$ the integer $q_{S_p}:=\prod_{v\in S_p}q_v$, with $q_v:=N(\mathfrak p_v)$, for $\mathfrak p_v\subset\mathcal O_F$ the unique prime ideal of $\mathcal O_F$ corresponding to the finite place $v$.

We define:

(1) The quotient:

$$
\mathscr{E}^{\mathrm{ABS}}_{S',S_p,X}(\chi|_{J^1_{F,S'}}):=\mathrm{PW}_{S,q^{-1}_{S_p}X,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))/\mathrm{PV}^{\mathrm{ABS}}_{S',S_p}\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'})) \tag{7.3.3.5}
$$

endowed with the quotient topology, where $\mathrm{PV}^{\mathrm{ABS}}_{S',S_p}$ is the continuous linear operator with closed range induced by Weil's Principal Value Operators as per Proposition 7.3.3.2.

We refer to $\mathscr{E}^{\mathrm{ABS}}_{S',S_p,X}(\chi|_{J^1_{F,S}})$ as the p-primary absolute PW Orbital Quotient.

(2) The quotient:

$$
\widetilde{\mathscr{E}}_{S',S_p,Y}(\chi|_{J^1_{F,S'}}):=\widetilde{\mathrm{PW}}_{S,q^{-1}_{S_p}Y,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))/\widetilde{\mathrm{PV}}_{S',S_p}\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'})) \tag{7.3.3.6}
$$

endowed with the quotient topology, where $\widetilde{\mathrm{PV}}_{S',S_p}$ is the continuous linear operator with closed range induced by Weil's Principal Value Operators as per Proposition 7.3.3.2.

We refer to $\widetilde{\mathscr{E}}_{S',S_p,X}(\chi|_{J^1_{F,S}})$ as the p-primary invariant PW Orbital Quotient.

The following is the main Theorem of this section. It says that so long as we choose the constraint on the support $X$, $Y$ on the Fourier transform, which defines the Paley-Wiener levels of $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))$, large enough, i.e. $X$, $Y\gg 0$, depending on the finitely many places in $S_p$ for a fixed prime $p$, with $S_p\subset S_0$,

## PDF page 360

**360** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

then the Paley-Wiener levels inherit the absolute Schauder bases and their dual bases, which we have already identified on the p-primary Orbital Quotients

$$
\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})
$$

and their strong duals (see Definition 7.3.1.3 and Theorem 7.3.1.6).

Theorem 7.3.3.4 (Orbital Schauder Bases II - Bases on the PW-levels). *Let $F$ be a number field. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Let $\chi\in\widehat{C_F}$ be a continuous character, unramified outside $S$. Let $S_0$ be a saturated finite set of finite places disjoint from $S$, and define $S':=S\cup S_0$.*

*Assume the choices and assumptions from Situation 7.3.3.1 are in force.*

*We denote by $N_p$ is the number of finite places of $F$ whose residue characteristic is $p$. Assume $S_p\subset S_0$.*

Let $\chi\in\widehat{C^1_F}$ be a continuous character.

We define the two subsets:

$$
P_{S',S_p}(\chi|_{J^1_{F,S}}):=\{a_k(\cdot,c):m_S(c)-N_p(c)<k\le m_S(c)\}\subset\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))'_\beta \tag{7.3.3.7}
$$

and:

$$
E_{S',S_p}(\chi|_{J^1_{F,S'}}):=\{\widehat\delta^{(k)}_c:0\le k\le N_p(c)-1\}\subset\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))'_\beta \tag{7.3.3.8}
$$

*where $\widehat\delta^{(k)}_c$ is the continuous functional obtained as the composition of the Fourier transform*

$$
\mathcal F_{S'}:\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))\to\mathrm H_{0,\mathrm{cont}}(\overline\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S}))
$$

*followed by the Mellin transform $L_{S'}$, and by the $k$th derivative of the point-evaluation functional at $\widehat c\in\Omega(J_{F,S'})$, i.e. $\widehat\delta^{(k)}_c$ is uniquely determined by the assignment, on the arbitrary $f\in\mathcal S(\mathbf A_{F,S'})$:*

$$
\widehat\delta^{(k)}_c(f):=\partial^k_s L_{S'}(\widehat f,\overline\chi_{S'}|\cdot|^{1-s}_{F,S'})|_{s=s_c} \tag{7.3.3.9}
$$

*with $s_c=\frac{2\pi i m_{c,v}}{\log(q_v)}-it_v$ for a, equivalently any, choice of $v\in S_p$ such that $c\in\mathcal U_{S',v}$.*

*Then the sets in (7.3.3.7), respectively (7.3.3.8), satisfy the following properties:*

(1) Any enumeration of the sets:

$$
P^{\mathrm{ABS}}_{S',S_p}(\chi|_{J^1_{F,S'}}),\ E^{\mathrm{ABS}}_{S',S_p}(\chi|_{J^1_{F,S'}}),\ \widetilde P_{S',S_p}(\chi|_{J^1_{F,S'}}),\ \widetilde E_{S',S_p}(\chi|_{J^1_{F,S'}}) \tag{7.3.3.10}
$$

*of continuous functionals obtained as the image of either countable set $P_{S',S_p}(\chi|_{J^1_{F,S'}})$ and $E_{S',S_p}(\chi|_{J^1_{F,S'}})$ under the continuous linear map:*

$$
\mathscr{E}_{S',S_p}(\chi_{S'}|_{J^1_{F,S'}})'_\beta\to\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))'_\beta\to\widetilde{\mathrm{PW}}_{S',Y,0}(\chi_{S'}|_{J^1_{F,S'}})'_\beta\to\mathrm{PW}_{S',X,0}(\chi_{S'}|_{J^1_{F,S'}})'_\beta \tag{7.3.3.11}
$$

*for $Y\ge X^{|S|}$, where $\widetilde{\mathrm{PW}}_{S',Y,0}(\chi_{S'}|_{J^1_{F,S'}})$, respectively $\mathrm{PW}_{S',X,0}(\chi_{S'}|_{J^1_{F,S'}})$, are the invariant, respectively absolute, PW-levels, is an unconditional Schauder basis for:*

$$
\mathscr{E}^{\mathrm{ABS}}_{S',S_p,X}(\chi|_{J^1_{F,S}})'_\beta \tag{7.3.3.12}
$$

and for:

$$
\widetilde{\mathscr{E}}_{S',S_p,Y}(\chi|_{J^1_{F,S}})'_\beta \tag{7.3.3.13}
$$

*both equipped with the strong topology, for all large enough $X$, respectively $Y$.*

(2) Their bi-orthogonal sets:

$$
P^\vee_{S',S_p}(\chi|_{J^1_{F,S'}}),\ E^\vee_{S',S_p}(\chi|_{J^1_{F,S'}})\subset\mathscr{E}_{S',S_p}(\chi|_{J^1_{F,S'}}) \tag{7.3.3.14}
$$

*equipped with the induced enumeration, are contained in the range of the continuous linear operators induced by the inclusions of each Paley-Wiener level into $\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))$ provided by Proposition 7.3.3.2,*

## PDF page 361

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **361**

*and they are an absolute Schauder basis in each of the two subquotients $\mathscr{E}^{\mathrm{ABS}}_{S',S_p,X}(\chi|_{J^1_{F,S}})$, respectively $\widetilde{\mathscr{E}}_{S',S_p,Y}(\chi|_{J^1_{F,S}})$.*

(3) *The absolute Schauder basis induced by the pre-image of $E_{S',S_p}(\chi_{S'}|_{J^1_{F,S'}})$ in the subquotients $\mathscr{E}^{\mathrm{ABS}}_{S',S_p,X}(\chi|_{J^1_{F,S}})$, respectively $\widetilde{\mathscr{E}}_{S',S_p,Y}(\chi|_{J^1_{F,S}})$, and its dual basis in each strong dual, satisfies the growth and decay estimates from Theorem 7.3.1.6(4) and (5), with same terminology and notation.*

The proof of the Theorem proceeds in the same manner as the proof of Theorem 7.3.1.6, with one important difference. Instead of using Theorem 4.6.1.5 to source the sought for Schauder bases, we use its “compactly supported” version, Theorem 4.6.2.1, exercising caution in keeping track of how the support condition on the Fourier transforms, defining the Paley-Wiener levels, is adjusted under the effect of Weil's Principal Value Operators: this, we can do thanks to Proposition 7.3.3.2.

Proof. We define $I:=(0,+\infty)\subset\mathbf R$.

We inspect the following diagram of linear operators:

(7.3.3.15)

```latex
\begin{tikzcd}
\mathrm{PV}_{S',S_p}(\widehat W) \arrow[r, "(1)"] \arrow[d, "(\mathrm{a})"'] & \widehat W \arrow[r, "(2)"] \arrow[d, "(\mathrm{b})"] & \widehat W/\mathrm{PV}_{S',S_p}(\widehat W) \arrow[d, "(\mathrm{c})"] \\
E_{S',S_p} \arrow[r, "(3)"] \arrow[d, "(\mathrm{d})"'] & E \arrow[r, "(4)"] \arrow[d, "(\mathrm{e})"] & E/E_{S',S_p} \arrow[d, "(\mathrm{f})"] \\
\mathcal F_{S'}E_{S',S_p} \arrow[r, "(5)"] \arrow[d, "(\mathrm{g})"'] & \mathcal F_{S'}E \arrow[r, "(6)"] \arrow[d, "(\mathrm{h})"] & (\mathcal F_{S'}E)/(\mathcal F_{S'}E_{S',S_p}) \arrow[d, "(\mathrm{i})"] \\
P_U\mathcal S_{-1+I}(J_{F,S'})(\overline{\chi}_{S'}|_{J^1_{F,S'}})\times P_U\mathcal S_I(J_{F,S'})(\chi_{S'}|_{J^1_{F,S'}}) \arrow[r, "(7)"] \arrow[d, "(\mathrm{j})"'] & \mathcal S_{-1+I}(J_{F,S'})(\overline{\chi}_{S'}|_{J^1_{F,S'}})\times\mathcal S_I(J_{F,S'})(\chi_{S'}|_{J^1_{F,S'}}) \arrow[r, "(8)"] \arrow[d, "(\mathrm{k})"] & \mathcal S_{U,\overline\chi_{S'}}(J_{F,S'}) \arrow[d, "(\mathrm{l})"] \\
P_U\mathcal S_{-1+I}(J_{F,S'})(\overline\chi_{S'}|_{J^1_{F,S'}}) \arrow[r, "(9)"'] & \mathcal S_{-1+I}(J_{F,S'})(\overline\chi_{S'}|_{J^1_{F,S'}}) \arrow[r, "(10)"'] & \mathcal S_{U,\overline\chi_{S'}}(J_{F,S'})
\end{tikzcd}
```

where, we follow the notation from Situation 4.6.1.1 and (4.5.3.3) for the operator $P_U:\mathcal S_J(G)(\xi|_{G^1})\to\mathcal S_J(G)(\xi|_{G^1})$ for $G$ an $\mathbf R_{>0}$-modulated group, $\xi\in\widehat G$ a continuous character, $J\subset\mathbf R$ a non-empty connected interval, $U=(\gamma_1,\dots,\gamma_N)$ a vector of $N$ elements of $G$ such that $|\gamma_k|_G>1$ for each $1\le k\le |S_p|$, we set $G=J_{F,S'}$, $\xi=\overline{\chi}_{S'}$, $U=(\pi^{-1}_v)_{v\in\in S_p}$, $J=I$.

The $\mathbf C$-vector space $E$ is defined to be either:

$$
\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'})) \tag{7.3.3.16}
$$

or:

$$
\widetilde{\mathrm{PW}}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'})) \tag{7.3.3.17}
$$

respectively, and $E_{S',S_p}$ is either:

$$
\mathrm{PW}_{S,X,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))\cap\mathrm{PV}_{S',S_p}\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S_0(\mathbf A_{F,S'})) \tag{7.3.3.18}
$$

or:

$$
\widetilde{\mathrm{PW}}_{S,Y,0}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))\cap\mathrm{PV}_{S',S_p}\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S_0(\mathbf A_{F,S'})) \tag{7.3.3.19}
$$

respectively, where $\mathcal F_{S'}$ is the Fourier transform:

$$
\mathcal F_{S'}:\mathrm H_{0,\mathrm{cont}}(\chi_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))\to\mathrm H_{0,\mathrm{cont}}(\overline{\chi}_{S'}|_{J^1_{F,S'}},\mathcal S(\mathbf A_{F,S'}))
$$

## PDF page 362

**362** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

from (5.2.4.1) of Theorem 5.2.4.1, and $\mathcal F_{S'}E$, respectively $\mathcal F_{S'}E_{S',S_p}$, denotes the linear image of $E$, respectively $E_{S',S_p}$, under $\mathcal F_{S'}$, a linear topological isomorphism onto its range.

The $\mathbf C$-vector space $\widehat W$ is defined as the pre-image under $\mathcal F_{S'}$ of a $\mathbf C$-vector subspace $W\subset\mathcal F_{S'}E$ to be constructed. We will proceed by means of analogy with the proof of Theorem 7.3.1.6, where $W$ was constructed as a linear copy of $|\cdot|^{-1}_{F,S}\cdot\mathcal{S}_{\mathrm{E}}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, providing access to Theorem 4.6.1.5 to source the absolute Schauder basis on $\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})$.

The existence of such linear copy of $|\cdot|^{-1}_{F,S}\cdot\mathcal{S}_{\mathrm{E}}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ was, in turn, provided by the combination Proposition 5.3.4.4 together with Lemma 5.3.4.2 and Remark D.3.3.6 (on the stability of $\mathcal{S}_{\mathrm{E}}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$ and $\mathcal S_{00}(\mathbf A_{F,S})$ under pointwise multiplication by $|\cdot|^a_{F,S}$ for $a\in\mathbf R$), and the Second Structure Theorem (see Theorem 5.4.1.1) was then used to prove cartesianity properties of some of the sub-squares in the diagram from (7.3.1.20), which (7.3.3.15) mirrors.

We choose a continuous homomorphic section $\tau$ to the $S$-idelic norm.

We consider $K_S$ a compact subset of the $\mathbf R_{>0}$-modulated group $J_{F,S}$, of the following form:

$$
K_S=\tau([1/a^2,1/a])\cdot J^1_{F,S}\subset J_{F,S} \tag{7.3.3.20}
$$

for $a>1$ a real number. We assume that $a$ satisfies:

$$
a>q_{S_0}:=\prod_{v\in S_0}q_v=\prod_{v\in S_0}N(\mathfrak p_v). \tag{7.3.3.21}
$$

For any $\varphi\in\mathcal D_{K}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, we then consider the smooth compactly supported function obtained from $\varphi$ as follows: we enumerate $S_0=\{v_1,\dots,v_N\}$, and we define $\varphi_0:=\varphi$, and, for each $1\le k\le N$:

$$
\varphi_k(x):=\varphi_{k-1}(x)-c_{k-1}\cdot\varphi_{k-1}(\tau(q_{v_k})x) \tag{7.3.3.22}
$$

as smooth compactly supported functions on $J_{F,S}$, where $c_{k-1}\in\mathrm U(1)\subset\mathbf C^\times$ is the complex number:

$$
c_{k-1}:=\overline{\chi}(\mathfrak p_{v_k})q^{-ix_0}_{v_k} \tag{7.3.3.23}
$$

for $x_0\in\mathbf R$ the unique real number such that $\chi(\tau(t))=t^{ix_0}$ as smooth functions of $t\in\mathbf R_{>0}$.

Since $\varphi\in\mathcal D_{K_S}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, then $\varphi_N\in\mathcal D(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})\subset\mathcal{S}_{\mathrm{E}}(J_{F,S})(\overline{\chi}|_{J^1_{F,S}})$, which, by Proposition 5.3.4.4(3), implies $\varphi_N=\Phi_{F,S',\chi_{S'}|_{J^1_{F,S'}}}(f)$ for some choice of $f=f(\varphi_N)\in\mathcal S(\mathbf A_{F,S})$.

We note that the function:

$$
f(\varphi_N)\otimes\bigotimes_{v\in S_0}1_{\mathcal O_{F_v}} \tag{7.3.3.24}
$$

is a Schwartz-Bruhat function over $\mathbf A_{F,S'}$, with $f(\varphi_N)$ a Schwartz-Bruhat function over $\mathbf A_{F,S}$ whose image under $\Phi_{F,S,\overline{\chi}_S|_{J^1_{F,S}}}$ is contained within $\mathrm H_{0,\mathrm{cont}}(\overline{\chi}_S,\mathcal S_{00}(\mathbf A_{F,S}))$.

We refer the reader to (5.3.4.1) from Definition 5.3.4.1, and to Proposition 5.3.4.4 for more on $\mathcal S_{00}(\mathbf A_{F,S})$: this is a closed subspace of $\mathcal S(\mathbf A_{F,S})$ providing elements $\Phi_{F,S,\overline{\chi}_S|_{J^1_{F,S}}}(f)$ in $\mathrm H_{0,\mathrm{cont}}(\overline{\chi}_S|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ have entire Mellin transform $Z_S(f,c)$ for $c\in\Omega(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})$, i.e. over the connected component of the Riemann surface $\Omega(J_{F,S})$ parametrized by $\overline{\chi}_S|_{J^1_{F,S}}$.

If $\chi_S=|\cdot|^{ix_0}_{F,S}$ and we assume $\varphi$ satisfies the vanishing condition $M(\varphi)(s)|_{s=1-ix_0}=0$, then so does $\varphi_N$, since this is a linear condition, and $\varphi_N$ is a finite linear combination of dilations of $\varphi$, each of which has, therefore, itself Mellin transform that vanishes at $s=1-ix_0$, since $\varphi$ does.

In this case, $\varphi_N$ is contained within $\mathrm H_{0,\mathrm{cont}}(\overline{\chi}_S|_{J^1_{F,S}},\mathcal S_0(\mathbf A_{F,S})\cap\mathcal S_{00}(\mathbf A_{F,S}))$, i.e. $f(\varphi_N)$ can be chosen to satisfy the following properties: $f(\varphi_N)$ is compactly supported, with support entirely contained within $\mathrm{GL}_1(\mathbf A_{F,S})\subset\mathbf A_{F,S}$ (in particular, we have $f(\varphi_N)(0)=0$), and it satisfies $\mathcal F_S(f(\varphi_N))(0)=0$.

## PDF page 363

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **363**

We note that if $\chi_S|_{J^1_{F,S}}\ne 1$, then

$$
\mathrm H_{0,\mathrm{cont}}(\overline{\chi}_{S''}|_{J^1_{F,S''}},V)=\mathrm H_{0,\mathrm{cont}}(\overline{\chi}_{S''}|_{J^1_{F,S''}},\mathcal S(\mathbf A_{F,S''})) \tag{7.3.3.25}
$$

for $V=\ker(\delta_0)$, respectively $V=\ker(\widehat\delta_0)$, and hence for $V=\mathcal S_0(\mathbf A_{F,S''})$, for any finite set of places of $F$ containing $S$. Indeed, if the inclusion of the left side into the right side from (7.3.3.25) was strict, then in the case $V=\ker(\delta_0)$, $\delta_0$ would descend to the quotient $\mathrm H_{0,\mathrm{cont}}(\overline{\chi}_{S''}|_{J^1_{F,S''}},\mathcal S(\mathbf A_{F,S''}))$ inducing a continuous functional, which cannot be since $\delta_0$ is homogeneous of weight zero, and hence it cannot be $\chi_{S''}|_{J^1_{F,S''}}$-homogeneous, since $\chi_{S''}|_{J^1_{F,S''}}$ is non-trivial. The same argument applies to $\widehat\delta_0$, which is homogeneous of weight 1, and hence cannot be $\chi_{S''}|_{J^1_{F,S''}}$-homogeneous (as all continuous functionals on $\mathrm H_{0,\mathrm{cont}}(\overline{\chi}_{S''}|_{J^1_{F,S''}},\mathcal S(\mathbf A_{F,S''}))$, instead, are).

We have, as meromorphic functions over $\Omega(J_{F,S'})(\overline{\chi}_{S'}|_{J^1_{F,S'}})$:

$$
L_{S'}(f(\varphi_N)\otimes\bigotimes_{v\in S_0}1_{\mathcal O_{F_v}},\overline{\chi}_{S'}|\cdot|^{1+s}_{F,S'})=Z_S(f(\varphi_N),\overline{\chi}_S|\cdot|^{1+s}_{F,S})\prod_{v\in S_0}\frac{1}{1-\overline{\chi}(\mathfrak p_v)q^{-1-s}_v} \tag{7.3.3.26}
$$

and we further have, as meromorphic (in fact, entire) functions over $\Omega(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})$:

$$
Z_S(f(\varphi_N),\overline{\chi}_S|\cdot|^{1+s}_{F,S})=M(\varphi_N)(1+s-ix_0) \tag{7.3.3.27}
$$

$$
=M(\varphi)(1+s-ix_0)\prod_{1\le k\le N}(1-\overline{\chi}(\mathfrak p_{v_k})q^{-ix_0}_{v_k}q^{-1-s+ix_0}_{v_k}) \tag{7.3.3.28}
$$

$$
=M(\varphi)(1+s-ix_0)\prod_{1\le k\le N}(1-\overline{\chi}(\mathfrak p_{v_k})q^{-1-s}_{v_k}). \tag{7.3.3.29}
$$

We define $W$ to be the linear image under $\Phi_{F,S',\overline{\chi}_{S'}|_{J^1_{F,S'}}}$ of the $\mathbf C$-linear subspace of $\mathcal S(\mathbf A_{F,S'})$ linearly generated by the elements $f((|\cdot|^{-1}_{F,S}\cdot\varphi)_N)\otimes\bigotimes_{v\in S_0}1_{\mathcal O_{F_v}}$ (noting that for any smooth compactly supported function $\varphi$ on $J_{F,S}$, $|\cdot|^a_{F,S}\cdot\varphi$ is also smooth compactly supported for any $a\in\mathbf R$. We further refer the reader to Remark D.3.3.6).

With this choice of $W$, up to enlarging $X>0$, respectively $Y>0$, once, to ensure that as $\varphi$ varies over $\mathcal D_{K_S}(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})$, then the image of $(|\cdot|^{-1}_{F,S}\cdot\varphi)_N$ under the linear inclusion

$$
\mathcal D(J_{F,S})(\overline{\chi}_S|_{J_{F,S}})\to\mathcal{S}_{\mathrm{E}}(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})\to\mathcal{S}_I(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})
$$

is contained in the image of

$$
\mathcal F_S(\mathcal S_0(\mathbf A_{F,S})_X),\ \mathcal F_S(\widetilde{\mathcal S}_0(\mathbf A_{F,S})_Y)
$$

into $\mathcal{S}_I(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})$ under $\Phi_{F,S,\overline{\chi}_S|_{J^1_{F,S}}}$.

The argument provided in the proof of Theorem 7.3.1.6 then applies, and by the choice made for $K_S$, by Theorem 4.6.2.1 and Corollary 4.6.3.1 we obtain that the composition of the four rightmost vertical arrows is surjective, which implies that the composition of (f) and (i) is surjective, hence open by [NB, Thm.14.4.5], being source and target Fréchet spaces.

The vertical arrows (c), (f) and (i) are injective by design of the closed subspaces $E_{S',S_p}$ and $\mathcal F_{S'}E_{S',S_p}$ from (7.3.3.18), respectively (7.3.3.19).

Indeed, since $0\in -1+I$, the composition of the vertical arrows (b), (e), (h) and (k), for the definition of which we refer the reader to the proof of Theorem 7.3.1.6, the linear subspace $\widehat W\subset E$ is sent onto the linear subspace

$$
\mathcal D_{K_S}(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})\subset\mathcal{S}_{\mathrm{E}}(J_{F,S'})(\overline{\chi}_{S'}|_{J^1_{F,S'}})
$$

where the inclusion is induced by the inclusion $\mathcal D_{K_S}(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})\subset\mathcal{S}_{\mathrm{E}}(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})$, followed by the linear topological isomorphism:

$$
\mathcal{S}_{\mathrm{E}}(J_{F,S})(\overline{\chi}_S|_{J^1_{F,S}})\to\mathcal{S}_{\mathrm{E}}(J_{F,S'})(\overline{\chi}_{S'}|_{J^1_{F,S'}}) \tag{7.3.3.30}
$$

## PDF page 364

**364** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

induced by the continuous linear inclusion $\mathcal{S}_{\mathrm{E}}(J_{F,S})\to\mathcal{S}_{\mathrm{E}}(J_{F,S'})$ of the closed subspace of $\Gamma$-invariant Schwartz-Bruhat functions of exponential decay on $J_{F,S'}$, for $\Gamma\subset J^1_{F,S'}$ the closed subgroup defined as the image of the closed subgroup $\prod_{v\in S_0}\mathcal O^\times_{F_v}\subset\mathrm{GL}_1(\mathbf A_{F,S'})$.

The linear inclusion in (7.3.3.30) is indeed surjective since $\chi$ is unramified outside $S$.

By Lemma 7.3.1.5, the remaining assertions follow from Theorem 4.6.1.5.

$\square$

**7.3.4. Poles of the $\Gamma$-factors.** We discuss an analog of Theorem 7.3.1.2 isolating the coefficients of the principal parts at the poles of the $\Gamma$-factors only.

Notation 7.3.4.1 (Filtration by orders of poles - Archimedean local factors). Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\chi\in\widehat{J_{F,S}}$ be a continuous character.

We denote by $S_{\infty,r}$, respectively $S_{\infty,c}$, the sets of real places, respectively complex places of $F$. We choose an enumeration $S_{\infty,r}=\{v_1,\dots,v_{r_1}\}$ and $S_{\infty,c}=\{w_1,\dots,w_{r_2}\}$.

We denote by $(\underline{n},\underline{p})$ the arbitrary element of $\mathbf N^{r_1}\times\mathbf N^{r_2}$, lexicographically according to the chosen enumerations (i.e. $(\underline{n},\underline{p})\le (\underline{n}',\underline{p}')$ if and only if for every $\underline{n}\le \underline{n}'$ under the lexicographical ordering on $\mathbf N^{r_1}$, and $\underline{p}\le \underline{p}'$ under the lexicographical ordering on $\mathbf N^{r_2}$).

We choose an integer tuple $(\underline{n},\underline{p})\in\mathbf N^{r_1}\times\mathbf N^{r_2}$ and define:

$$
\mathcal U_{\le (\underline{n},\underline{p})}:=\bigcup_{1\le k\le r_1}\psi^{-1}_{v_k}(\mathcal U^{\le n_{v_k}}_{v_k})\cup\bigcup_{1\le k\le r_2}\psi^{-1}_{w_k}(\mathcal U^{\le p_{v_k}}_{w_k}) \tag{7.3.4.1}
$$

where $\mathcal U^{\le n_{v_k}}_{v_k}$ denotes the set of poles of the Euler factor $L_v(c_v)$ of the Hecke $L$-function $L(c)$ in $\Omega(F^\times_v)(\omega_v)$ whose ordinate $\sigma(c_{v_k})$ satisfies $\sigma(c_{v_k})\ge -2n_{v_k}-\epsilon(c_{v_k})$ for $\epsilon(c_{v_k})=0$ if $\omega_{v_k}$ is trivial, and $\epsilon(c_{v_k})=1$ if $\omega_{v_k}$ is the sign character, and where $\mathcal U^{\le p_{w_k}}_{w_k}$ denotes the set of poles of the Euler factor $L_v(c_v)$ of the Hecke $L$-function $L(c)$ in $\Omega(F^\times_v)(\omega_v)$ whose ordinate $\sigma(c_{w_k})$ satisfies $\sigma(c_{w_k})\ge -p_{w_k}-\epsilon(c_{w_k})$ where $\epsilon(c_{w_k})=|n|/2$ if $\omega_{w_k}=c_n\in\widehat{\mathrm U(1)}$.

We define the filtration:

$$
F^{(\underline{n},\underline{p})}_S(\chi|_{J^1_{F,S}})\subset\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})) \tag{7.3.4.2}
$$

of those elements $\Phi_{F,S,\omega}(f)\in\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ whose $S$-idelic Mellin transform $Z_S(f,c)$ (which, recall from Lemma 5.1.2.2(2), only depends on $f$ through $\Phi_{F,S,\omega}(f)$) has no poles over $\mathcal U_{\le (\underline{n},\underline{p})}$. We endow the linear subspace $F^{(\underline{n},\underline{p})}_S(\chi|_{J^1_{F,S}})$ with the subspace topology, promoting it to a Hausdorff locally convex topological $\mathbf C$-vector subspace.

We refer to the filtration $F^{(\bullet,\bullet)}_S(\chi|_{J^1_{F,S}})$ as the filtration by orders of pole on $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$.

We denote by:

$$
\mathscr{E}_{S,S_\infty}(\chi|_{J^1_{F,S}}):=\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))/\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S_{00}(\mathbf A_{F,S})) \tag{7.3.4.3}
$$

the quotient of the closed subspace $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ of $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$, by the closed subspace $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S_{00}(\mathbf A_{F,S}))$, equipped with the quotient topology, promoting it to a nuclear Fréchet space.

Theorem 7.3.4.1 (S-local Polar Orbital Schauder Basis - II). *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $\chi\in\widehat{J_{F,S}}$ be a continuous character.*

(1) The subspace $F^{(\underline{n},\underline{p})}_S(\chi|_{J^1_{F,S}})$ of $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$ is closed.

(2) *The orthogonal $F^{(\underline{n},\underline{p})}_S(\chi|_{J^1_{F,S}})^\perp$ with respect to the duality*

$$
\langle\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})),\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))'_\beta\rangle
$$

## PDF page 365

**7.3. PALEY-WIENER LEVELS AND SCHAUDER BASES OF PRINCIPAL PARTS** · **365**

*endowed with the strong topology on the continuous dual of the quotient*

$$
\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))/F^{(\underline{n},\underline{p})}_S(\chi|_{J^1_{F,S}})
$$

*is linearly and topologically generated by the finitely many $\mathbf C$-linearly independent continuous functionals:*

$$
\{a_k(\cdot,c),c\in\mathcal U_{\le (\underline{n},\underline{p})},1\le k\le m_{S_\infty}(c)\}. \tag{7.3.4.4}
$$

(3) *We have, as closed subspaces of $\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))$:*

$$
\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S_{00}(\mathbf A_{F,S}))=\bigcap_{(\underline{n},\underline{p})}F^{(\underline{n},\underline{p})}_S(\chi|_{J^1_{F,S}}). \tag{7.3.4.5}
$$

(4) *The quotient topology on the linear quotient:*

$$
\mathscr{E}_{S,S_\infty}(\chi|_{J^1_{F,S}}):=\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))/\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S_{00}(\mathbf A_{F,S})) \tag{7.3.4.6}
$$

*is equivalent to the projective topology induced by the countable family of linear quotient maps:*

$$
q_{(\underline{n},\underline{p})}:\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))/\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S_{00}(\mathbf A_{F,S}))\to\mathrm{PV}_{S,S_f}\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S})/F^{(\underline{n},\underline{p})}_S(\chi|_{J^1_{F,S}}). \tag{7.3.4.7}
$$

*The quotient in (7.3.4.6) is linearly and topologically isomorphic to the linear space $\prod_{(\underline{n},\underline{p})}\mathbf C$ topologized with the product topology. Its strong dual is linearly and topologically isomorphic to the orthogonal $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S_{00}(\mathbf A_{F,S})^\perp$ topologized with the strong topology on the continuous dual of the quotient, in turn linearly and topologically isomorphic to $\bigoplus_{(\underline{n},\underline{p})}\mathbf C$ topologized with the finest locally convex topology.*

(5) *Any enumeration of the continuous functionals*

$$
\{a_k(\cdot,c),1\le k\le m_{S_\infty}(c),c\in\mathcal U_{S_\infty}\} \tag{7.3.4.8}
$$

*is a Schauder basis for the orthogonal $\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}},\mathcal S_{00}(\mathbf A_{F,S})^\perp$ topologized with the strong topology on the continuous dual of the quotient.*

Proof. (1), (2), (3) and (4) of the Theorem were proved throughout the proof of Theorem 5.4.1.1, to which we refer the reader. We will recall here how to construct dual basis elements for each of the sets of finitely many functionals in (7.3.4.4).

We exhibit Schwartz-Bruhat functions in $\mathcal S(\mathbf A_{F,S})$ whose image under $\Phi_{F,S,\omega}$ has prescribed poles and orders of poles at the points of each $\mathcal U^{\le (\underline{n},\underline{p})}$.

Each local character $\omega_v=\chi_v|_{\{u\in F^\times_v:|u|_v=1\}}$ for each Archimedean place $v$, uniquely determines a Schwartz-Bruhat function $f_v$ on $F_v$ whose local $L$-function is the $\Gamma$-factor at $v$. We refer the reader to [CF, Ch.XV,§2.5,pp.316-319] and [RV, Ch.7,§7.1,pp.249-253] for the explicit definition of such functions, satisfying the self-duality properties in [CF, Ch.XV,§2.5,pp.316-319] with respect to the real and complex Fourier transforms.

We consider a tuple of nonnegative integers $(\underline{n},\underline{p})=((n_v)_{v\in\Sigma_{F,r}},(p_v)_{v\in S_{\infty,c}})$ where $S_{\infty,r}$ denotes the real places of $F$, and $S_{\infty,c}$ denotes the complex places, and define the linear map:

$$
M_{(\underline{n},\underline{p})}:=\bigotimes_{v\in S_{\infty,r}}M_{x^{2n_v}_v}\otimes\bigotimes_{v\in S_{\infty,c}}M_{z^{p_v}_v\bar z^{p_v}_v}:\mathcal S(\mathbf A_{F,S_\infty})\to\mathcal S(\mathbf A_{F,S_\infty}). \tag{7.3.4.9}
$$

We further define

$$
M^S_{(\underline{n},\underline{p})}:=M_{(\underline{n},\underline{p})}\otimes\bigotimes_{v\in S_f-S_\chi}1_{\mathcal O^\times_{F_v}}\otimes\bigotimes_{v\in S_\chi}\omega^{-1}_v1_{\mathcal O^\times_{F_v}}:\mathcal S(\mathbf A_{F,S_\infty})\to\mathcal S(\mathbf A_{F,S_\infty})\otimes\bigotimes_{v\in S_f}\mathcal S(F^\times_v)
$$

and, upon calling $f_\infty:=\bigotimes_{v\in S_\infty}f_v$ for $f_v\in\mathcal S(F_v)$ the above choice of “self-dual” Schwartz-Bruhat function, the Schwartz-Bruhat functions on $\mathbf A_{F,S}$ obtained as $M^S_{(\underline{n}',\underline{p}')}(f_\infty)$ for each $(\underline{n}',\underline{p}')\le (\underline{n},\underline{p})$, satisfy the desired spanning properties (see Proposition 5.3.3.4).

## PDF page 366

**366** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

We now show that any enumeration of the countable set of continuous functionals from (7.3.4.8) indeed is a Schauder basis for the orthogonal $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal{S}_{00}(\mathbf A_{F,S})^\perp \subset \mathrm{PV}_{S,S_f} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal{S}(\mathbf A_{F,S}))'_\beta$.

Since the orthogonal carries the finest locally convex topology, any countable algebraically linearly independent set of topological generators is a topological basis. The countable set in (7.3.4.8) is algebraically linearly independent by (2), and it is a set of topological generators by (2) and (3). By [Jar, Part II, Ch.14, §14.2, Thm.5, p.293], it is a Schauder basis. $\square$

**7.4. Nuclearity**

Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $a \in \mathbf R$ be a fixed real number. For $p$ a fixed prime number, we denote by $S_p$ the finite set of places of $F$ dividing $p$. In this subsection we discuss nuclearity of the regularized action of $C_F$ on

$$
\mathscr{H}_{F,a}(\chi|_{C^1_F}) := \mathcal{S}_\mathrm{E}(C_F)(\chi|_{C^1_F})/|\cdot|^a_F \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F)) \tag{7.4.0.1}
$$

and on the subquotients:

$$
\mathscr{E}_{S_p}(\chi|_{C^1_F}) := \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))/\mathrm{PV}_{S_p} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F)). \tag{7.4.0.2}
$$

**7.4.1. Spectral Nuclearity.** The following Theorem will never be used throughout this work. Rather, Theorem 10.3.1.1 will, which is a weaker yet sufficient analog.

Theorem 7.4.1.1 (Strong Topologies and Nuclearity - I). *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $N \ge 1$ be an integer.*

(1) *The linear subspace $|\cdot|^a_F \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F)) \subset \mathcal{S}_\mathrm{E}(C_F)(\chi|_{C^1_F})$ is a closed $\mathcal D(C_F)$-submodule.*

(2) *For each $\varphi \in \mathcal D(C_F)$, upon denoting by $A_{\mathrm{spec},a,\chi,N}(\varphi)$ the operator induced on the closed subspace of $\mathscr{H}_{F,a}$ linearly and topologically generated by the subset of the bi-orthogonal set $\{\psi_{\chi,t,m}\}$ to the functionals $\{U(\delta^{m}_\rho)\}$ provided by Theorem 7.1.4.2, for which $0 \le m \le N-1$, by $A(\varphi)$ on $\mathcal{S}_\mathrm{E}(C_F)(\chi|_{C^1_F})$, then $A_{\mathrm{spec},a,\chi,N}(\varphi)$ is a strongly nuclear operator whose nuclear trace is computed by the formula:*

$$
\mathrm{Trace}(A_{\mathrm{spec},a,\chi,N}(\varphi)) = \sum_{\rho: L(-a+\rho,\chi)=0} N_0(\chi|\cdot|^{-a+\rho}_F) \int_{C_F} \varphi(g)\chi(g)|g|^{-a+\rho}_F\,\mathrm{d}\overline{\mu}(g) \tag{7.4.1.1}
$$

*where the sum is over the complex numbers $\rho$ such that $\chi|\cdot|^{-a+\rho}_F$ is a zero of the Hecke $L$-function $L(c)$ contained in the connected component $\Omega(C_F)(\chi|_{C^1_F})$, and $N_0(\chi|\cdot|^{-a+\rho}_F)$ is the minimum between the multiplicity of $\chi|\cdot|^{-a+\rho}_F$ as a zero of $L(c)$, and $N$.*

Proof. Since multiplication by $|\cdot|^{-a}_F$ on $\mathcal{S}_\mathrm{E}(C_F)$ is a bounded and boundedly invertible linear endomorphism, we may and do assume $a=0$ in (1). By Theorem 7.1.4.2, to show strong nuclearity of the operator $A_{\mathrm{spec},\chi,N}(\varphi)$ (i.e. that it is an operator of order $0$, for the discussion of which we refer the reader to [Gro-a, Ch.II, §1, No.2, Def.2, p.6]) it is enough to show that the sequence $\{\Phi^{(m)}(\rho)\}_{(\rho,m)}$ where $\Phi(s) := \int_{C_F} \varphi(g)\chi(g)|g|^s_F\,\mathrm{d}\overline{\mu}(g)$ and the labelling of the pairs $\{(\rho,m)\}$ with $0 \le m \le N_0(\chi|\cdot|^\rho_F)-1$ is prescribed by the chosen enumeration of the set of functionals provided by Theorem 7.1.4.2(3), is a sequence with of rapid decay (see [Gro-a, Ch.II, §1, No.1, (1), p.4] and the discussion on [Gro-a, Ch.II, §1, No.1, p.5]). To see this, we proceed as follows. We prove that the expression:

$$
A_{\mathrm{spec},a,\chi,N}(\varphi) = \sum_{\rho} \sum_{0 \le m_\rho \le N_0(\rho)-1} \langle \cdot, A(\varphi)'U(\delta^{(m_\rho)}_\rho)\rangle_{\mathscr{H}_{F,0},\mathscr{H}'_{F,0}}\,\psi_{(\rho,m_\rho)} \tag{7.4.1.2}
$$

## PDF page 367

**7.4. NUCLEARITY** · **367**

where $\{\psi_{(\rho,m_\rho)}\}$ is the bi-orthogonal set in $\mathscr{H}_{F,0}$ associated to the set $\{U(\delta^{(m)}_\rho)\}$ (the subset of the full set of continuous functionals $U(\delta^{(m)}_\rho)$ from (7.1.4.6), for which $0 \le m \le N-1$) exhibits $A(\varphi)'$ as being of the form $\sum_{i \ge 0} \lambda_i \langle \cdot,\varphi_i\rangle_{\mathscr{H}_{F,0},\mathscr{H}'_{F,0}} u_i$ for $\{u_i\}_{i \ge 0} \subset \mathscr{H}_{F,a}$ a bounded subset (given by the elements of the bi-orthogonal sequence to $\{U(\delta^{(m)}_\rho)\}_{(\rho,m_\rho)}$ as $0 \le m_\rho \le N_0(\rho)-1$, suitably renormalized by a real number $c_{(\rho,m)} > 0$), and $\{\varphi_i\}_{i \ge 0} \subset (\mathscr{H}_{F,0})'_\beta$ an equicontinuous subset (given by the set of continuous functionals $\{U(\delta^{(m)}_\rho)\}_{(\rho,m_\rho)}$ as $0 \le m_\rho \le N_0(\rho)-1$, suitably renormalized by a real number $c'_{(\rho,m)} > 0$), with $\{\lambda_i\}_{i \ge 0}$ a sequence of complex numbers of rapid decay (obtained from the values of $\Phi^{(m)}(s)$ at the zeros $\rho$ and as $m$ varies over $0 \le m \le N_0(\rho)-1$, from sums of length at most $N_0(\rho)$ of such values and with uniformly bounded (by $2^{N_0(\rho)}$) coefficients, with the index set $i$ being the chosen enumeration of the set of functionals indexed by the pairs $(\rho,m)$, listing $\psi_{\rho,m_\rho}$ with multiplicity if necessary, and multiplied by the reciprocal of $c_{(\rho,m)}\cdot c'_{(\rho,m)}$). Compare with the proof of Theorem 10.3.1.1(1).

Since the zeros of $L(s,\chi)$ are all located within the vertical strip of bounded width $\mathbf{C}_{[0,1]}$ of the complex $s$-plane, and they are a discrete subset, the rapid decay of the $\lambda_i$'s then follows from $\Phi(s)$ and all of its holomorphic derivatives being Schwartz uniformly on any vertical strip of bounded width of the complex $s$-plane, only finitely many of which (at most $N$) occur in (7.4.1.2).

The real numbers $c_{(\rho,m)}$, $c'_{(\rho,m)}$ that qualify for the intended purpose, can be chosen to be equal, for each pair $(\rho,m)$, and to be $1/N(\rho)!$, where we note that $N(\rho)!$ is $O(|\mathrm{Im}(\rho)|)$: multiplying a sequence of complex numbers depending on $(\rho,m)$ that decays rapidly as $|\mathrm{Im}(\rho)| \to +\infty$, by $N(\rho)!$, therefore preserves its rapid decay condition, providing the coefficients $\lambda_i$ satisfying the required decay property.

The nuclear trace of $A_{\mathrm{spec},a,\chi,N}(\varphi)$ therefore agrees with its matrix trace by [Lit-II, §4, Cor.2, p.61], which is computed by the formula in (7.4.1.1). $\square$

**7.4.2. Orbital Nuclearity - non-Archimedean places.**

Theorem 7.4.2.1 (Strong Topologies and Nuclearity - II). *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $p$ be a prime number.*

(1) The linear subspace

$$
\mathrm{PV}_{S_p} \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F)) \subset \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))
$$

is a closed $\mathcal D(C_F)$-submodule.

(2) *For each $\varphi \in \mathcal D(C_F)$, upon denoting by $A_{\mathrm{geom},p,\chi}(\varphi)$ the operator induced on $\mathscr{E}_{S_p}$ by $A(\varphi)$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))$, then $A_{\mathrm{geom},p,\chi}(\varphi)$ is strongly nuclear:*

$$
\mathrm{Trace}(A_{\mathrm{geom},p,\chi}(\varphi)) = \sum_{\varepsilon_p} N(\chi|\cdot|^{\varepsilon_p}_F) \int_{C_F} \varphi(g)\chi(g)|g|^{\varepsilon_p}_F\,\mathrm{d}\overline{\mu}(g) \tag{7.4.2.1}
$$

*where the sum is over the complex numbers $\varepsilon_p$ such that $\chi|\cdot|^{\varepsilon_p}_F$ is a zero of the entire function $\prod_{v \in S_p} L_v(\chi|\cdot|^s_F)^{-1}$ of multiplicity $N(\chi|\cdot|^{\varepsilon_p}_F)$, contained in the connected component $\Omega(C_F)(\chi|_{C^1_F})$, where $L_v(\chi|\cdot|^s_F)$ is the local Euler factor at $v$ of the Hecke $L$-function $L(s,\chi)$.*

Proof. The same argument as for Theorem 7.4.1.1, upon using Theorem 7.1.4.3 in place of Theorem 7.1.4.2 and Proposition 7.1.4.3 in place of Theorem 7.1.4.2, shows that $A_{\mathrm{geom},p,\chi}(\varphi)$ is strongly nuclear (noting that, following the argument in Proposition 7.1.4.3, $[F:\mathbf Q]$ bounds from above the multiplicity function $N(\chi|\cdot|^{\varepsilon_p}_F)$). It follows that its trace agrees with its matrix trace by [Lit-II, §4, Cor.2, p.61], which is computed by the formula in (7.4.2.1) upon repeating the calculation from (11.2.2.12) of Theorem 11.2.2.1. $\square$

**7.4.3. Orbital Nuclearity - Archimedean places.** The following is an analog of Theorem 7.1.4.3 treating the Archimedean local factors of the Hecke $L$-function $L(s,\chi)$, as opposed to the non-Archimedean local factors as discussed in Theorem 7.1.4.3.

## PDF page 368

**368** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

It uses Theorem 7.3.4.1 as an input, relating the poles of the Archimedean local factors and the resulting polar Schauder basis whose existence is discussed in Theorem 7.3.4.1, to the trivial zeros of the finite Hecke $L$-function.

Theorem 7.4.3.1 (Global Orbital Schauder Basis - infinite places). *Let $F$ be a number field. Let $\chi \in \widehat{C_F}$ be a continuous character. If $\chi|_{C^1_F}=1$, let $t_0 \in \mathbf R$ be the unique real number such that $\chi = |\cdot|^{-it_0}_F$.*

*Let $\tau$ be a choice of continuous homomorphic section to the idelic norm. We define the closed subspace:*

$$
\mathcal{S}_{\infty,0}(\mathbf A_F) := \mathcal{S}_{00}(\mathbf A_{F,S_\infty}) \otimes_\pi \mathcal{S}(\mathbf A^f_F) \subset \mathcal{S}(\mathbf A_F) \tag{7.4.3.1}
$$

*where $\mathcal{S}_{\infty,0}(\mathbf A_{F,S_\infty})$ is the closed subspace of $\mathcal{S}_{00}(\mathbf A_{F,S_\infty})$ defined as the intersection of $\mathcal{S}_{00}(\mathbf A_{F,S_\infty})$ and $\ker(T) \cap \ker(\widehat T)$, where $T = \delta_0$ and $\widehat T = \widehat\delta_0$, the Fourier transform of $\delta \in \mathcal{S}(\mathbf A_{F,S_\infty})'_\beta$, if $\chi|_{C^1_F}$, and $T = \widehat T = 0$ otherwise.*

Then:

(1) *The linear image $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{00}(\mathbf A_F)) := \Phi_{F,\chi|_{C^1_F}}(\mathcal{S}_{00}(\mathbf A_F))$ is a nonzero closed subspace of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))$.*

(2) *Let $\mathcal{U}_{S_\infty}$ be the subset of $\Omega(C_F)$ defined as in (5.3.4.13):*

$$
\mathcal{U}_{S_\infty} := \bigcup_{v \in S_\infty} \psi_v^{-1}(\mathcal{U}_v) \tag{7.4.3.2}
$$

*for $\psi_v : \Omega(C_F) \to \Omega(F^\times_v)$ the surjective local analytic isomorphism induced by restricting a continuous quasi-character in $\Omega(C_F)$ to $F^\times_v$, and for $\mathcal{U}_v \subset \Omega(F^\times_v)$ the subset of poles of the Euler factor at $v$ of the Hecke $L$-function $L(c)$. We let $N_{S_\infty}$ be the multiplicity function defined as in (5.3.4.14):*

$$
N_{S_\infty}(c) := \sum_{v \in S_\infty} \mathrm{ord}_{c'=\psi_v(c)} L_v(\psi_v(c')). \tag{7.4.3.3}
$$

*We write $\chi|\cdot|^{s_c}_F$ for the parametrization of each $c \in \mathcal{U}_{S_\infty}$. Then the orthogonal $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))$ with respect to the duality*

$$
\langle \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F)), \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))'_\beta \rangle
$$

*equipped with the subspace topology inherited from the strong topology, is linearly and topologically generated by the continuous functionals:*

$$
D^m_c(f) := \partial^m_s Z(f,\chi|\cdot|^s_F)|_{s=s_c} = \int_{\mathbf R_{>0}} \left(\int^{+i\infty}_{-i\infty} t^{-s} Z(\phi,\chi|\cdot|^s_F)\,\mathrm{d}s \right) t^{s_c} (\log(t))^m \,\frac{\mathrm{d}t}{t} \tag{7.4.3.4}
$$

*for $0 \le m \le N'_{S_\infty}(c)-1$, and as $c$ varies over the discrete set $\mathcal{U}_{S_\infty} \cap \Omega(C_F)(\chi|_{C^1_F})$ and $N'_{S_\infty}$ agrees with the multiplicity function $N_{S_\infty}$ over $\mathcal{U}_{S_\infty} - \{|\cdot|^{it_0}_F\}$, and, at $c = |\cdot|^{it_0}_F$, it is redefined to be $N'_{S_\infty}(|\cdot|^{it_0}_F) := N_{S_\infty}(|\cdot|^{it_0}_F)-1$.*

(3) *Any enumeration of the countable set $\{D^m_c\}_{(c,m)}$ of continuous functionals on $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))$ from (7.4.3.4), as $c$ varies over the discrete set $\mathcal{U}_{S_\infty} \cap \Omega(C_F)(\chi|_{C^1_F})$, and as $m$ varies over the integers $0 \le m \le N'_{S_\infty}(c)-1$, is a Schauder basis for the orthogonal $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))^\perp$ equipped with the dual strong topology of the quotient topology.*

(4) *The linear image of the closed subspace $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))$ of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))$ under the global Mellin transform $L$ from (5.1.1.1), is the closed subspace of $A\mathcal S^p(\mathbf C)$:*

$$
\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C) \cap A\mathcal S^p(\mathbf C) \tag{7.4.3.5}
$$

where $\Lambda_f(s,\chi) := (s-1-it_0)^{\delta_\chi} L_f(s,\chi)$, with $\delta_\chi = 1$ if $\chi|_{C^1_F}=1$, and $\delta_\chi = 0$ if $\chi|_{C^1_F} \ne 1$.

(5) *The strong dual of the quotient:*

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))/\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))
$$

## PDF page 369

**7.4. NUCLEARITY** · **369**

*carries the finest locally convex topology.*

Proof. (1) : We fix an arbitrary continuous character $\chi \in \widehat{C_F}$. We let $S$ be a finite set of places of $F$ containing all the Archimedean places, and such that $\chi$ is unramified outside $S$. We choose $S$ large enough so as to have $\mathrm{Pic}(\mathcal O_{F,S}) = 1$. Assume $\varphi_v \in \mathcal D(F_v)$ for each Archimedean place $v$, and define $\varphi := \bigotimes_{v \in S_\infty} \varphi_v$, a smooth compactly supported function on $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$.

We consider, for each $v \in S_f$, the Schwartz-Bruhat function $\rho_v := 1_{\mathcal O_{F_v}}$ if $\chi$ is unramified at $v$, and $\rho_v := \chi_v^{-1} \cdot 1_{\mathcal O^\times_{F_v}}$ if $\chi$ is ramified at $v$.

Then $f_0 := \varphi \otimes \bigotimes_{v \in S_f} \rho_v$ is a Schwartz-Bruhat function on $\mathbf A_{F,S}$, since the extension by zero of $\varphi$ is smooth and compactly supported over $\mathbf A_{F,S_\infty}$, hence Schwartz on the Euclidean space $\mathbf A_{F,S_\infty}$ (we further refer the reader to Lemma 5.3.3.3(3)).

We call $\chi_S$ the unique continuous character of $J_{F,S}$ obtained by descending to $J_{F,S}$ the restriction of $\chi$ to $C_{F,S}$ by $\widehat{\mathcal O}_{S_\infty-S}$-invariance.

Then $f := \pi_S(f_0)$ is such that $\Phi_{F,\chi|_{C^1_F}}(f)$ is an element of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{00}(\mathbf A_F))$. Assume that $\Phi_{F,\chi|_{C^1_F}}(f)$. Then so is $Z(f,c)$ over the connected component $\Omega(C_F)(\chi|_{C^1_F})$.

We have, parametrizing by $\chi|\cdot|^s_F$ the connected component $\Omega(C_F)(\chi|_{C^1_F})$:

$$
Z(f,\chi|\cdot|^s_F) = \prod_{v \in S_\infty} L_v(\varphi_v,\chi_v|\cdot|^s_v) \prod_{v \in \Sigma_{F,f}} L_v(\chi_v|\cdot|^s_v). \tag{7.4.3.6}
$$

The vanishing of $Z(f,\chi|\cdot|^s_F)$ forces the vanishing of at least one of the $L_v(\varphi_v,\chi_v|\cdot|^s_v)$ for some $v \in S_\infty$. We now let $\psi_v$ be smooth, real-valued, nonnegative, compactly supported over $F^\times_v$, for each Archimedean place $v$, and define $\varphi_v := \chi_v^{-1} \cdot \psi_v$. The functions $\varphi_v$ are also, respectively, smooth, compactly supported over $F^\times_v$, and so $\varphi$ qualifies to define $f$ as in the foregoing. The vanishing of $L_v(\varphi_v,\chi_v|\cdot|^s_v)$ would, however, force the vanishing of $\varphi_v$ by Fourier inversion.

Upon assuming that each of the $\varphi_v$, equivalently each of the $\psi_v$, is nonzero, we therefore obtain examples of Schwartz-Bruhat functions $f \in \mathcal{S}_{00}(\mathbf A_F)$ such that $\Phi_{F,\chi|_{C^1_F}}(f)$ is nonzero, hence a nonzero element of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{00}(\mathbf A_F))$.

(2) : We choose $S$ a finite set of places of $F$ containing all the Archimedean places, such that $\chi$ is unramified outside $S$, and such that $\mathrm{Pic}(\mathcal O_{F,S}) = 1$. We denote by $\chi_S$ the unique continuous character of $J_{F,S}$ obtained by descending the restriction of $\chi$ to $C_{F,S}$ by $\widehat{\mathcal O}^\times_{\Sigma_F-S}$-invariance. We denote by $\chi_{S,\infty}$ the restriction of $\chi$ to $\mathrm{GL}_1(\mathbf A_{F,S_\infty})$

By Theorem 6.2.2.1, every element $\phi$ of the linear image of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{00}(\mathbf A_F))$ under the global Mellin transform $L$ is of the form:

$$
\phi(s) = u(s) L_f(s,\chi) \tag{7.4.3.7}
$$

where $u$ is an entire function on the complex $s$-plane of the following form: there exists a Schwartz-Bruhat function $f_0 \in \mathcal{S}_{00}(\mathbf A_{F,S_\infty})$ such that, in the special case $\chi|_{C^1_F}=1$, $f_0$ additionally satisfies the linear condition $\widehat f_0(0)=0$, and such that we have:

$$
u(s) = \int_{\mathbf R_{>0}} t^s \,\Psi_{F,S,\chi_{S,\infty}}(f_0)(\tau(t))\,\frac{\mathrm{d}t}{t}
$$

as entire functions on the complex $s$-plane (see Theorem 6.2.2.1 for a study of the operator $\Psi_{F,S,\chi_{S,\infty}}$). The $\Gamma$-factor

$$
\Gamma_F(\chi,s) := \prod_{v \in S_\infty} L_v(\psi_v(\chi|\cdot|^s_F))
$$

## PDF page 370

**370** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

of the Hecke $L$-function $L(c)$ on $\Omega(C_F)(\chi|_{C^1_F})$ is such that its reciprocal is entire as a function of $s$, and has zeros at the trivial zeros of the finite Hecke $L$-function $L_f(s,\chi)$, with matching multiplicities.

We have, for every $s \in \mathbf C$ and upon defining

$$
\phi(s) = \frac{u(s)}{\Gamma_F(\chi,s)((s+it_0)(s-1-it_0))^{\delta_\chi}} ((s+it_0)(s-1-it_0))^{\delta_\chi} L(s,\chi)
$$

where $\delta_\chi = 0$ if $\chi|_{C^1_F}$ is non-trivial, and $\delta_\chi = 1$ if $\chi|_{C^1_F}=1$, and the ratio $\frac{u(s)}{\Gamma_F(\chi,s)((s+it_0)(1-s-it_0))^{\delta_\chi}}$ has only removable singularities.

We denote by $u_0$ the unique analytic continuation of such ratio to an entire function on the complex $s$-plane. It has zeros at each of the trivial zeros of the finite Hecke $L$-function $L_f(s,\chi)$ with at least the same multiplicity.

We deduce that the image of $\mathcal{S}_{\infty,0}(\mathbf A_F)$ under the global Mellin transform $L$ to $A\mathcal S^p(\mathbf C)$ is contained within the closed subspace:

$$
\frac{\Lambda(s,\chi)}{\Gamma_F(\chi,s)(s+it_0)^{\delta_\chi}} \mathscr{O}(\mathbf C) \cap A\mathcal S^p(\mathbf C) = (s-1-it_0)^{\delta_\chi} L_f(s,\chi)\,\mathscr{O}(\mathbf C) \cap A\mathcal S^p(\mathbf C). \tag{7.4.3.8}
$$

We will be granting for the moment that it in fact agrees with this closed subspace. We define:

$$
\Lambda_f(s,\chi) := (s-1-it_0)^{\delta_\chi} L_f(s,\chi)
$$

an entire function of $s$ with at most polynomial growth as $|s| \to +\infty$ uniformly over each vertical strip of bounded width of the complex $s$-plane. By Dirichlet's Unit Theorem and the Class Number Formula, the order of zero $N$ at $s=-it_0$ of $\Lambda_f(s,\chi)$ is exactly $N_{S_\infty}(|\cdot|^{it_0}_F)-1$, where $N_{S_\infty}(|\cdot|^{it_0}_F)$ is the order of pole of $\Gamma_F(\chi,s)$ at the same point.

The quotient $\mathbf C$-linear space:

$$
\mathscr{O}(\mathbf C)/\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C) \tag{7.4.3.9}
$$

is Hausdorff, since $\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C)$ is closed in $\mathscr{O}(\mathbf C)$, and it is complete, since $\mathscr{O}(\mathbf C)$ is a Fréchet space, and Hausdorff quotients of Fréchet spaces are complete by [Scha, Ch.I, §6, 6.3, p.31]. We define:

$$
K_z := \mathbf C[s]/(1-s/z)^{N(z)} \tag{7.4.3.10}
$$

equipped with the Euclidean topology, for $z$ in the discrete set of zeros of $\Lambda_f(s,\chi)$, with multiplicity $N(z)$. $K_z$ is linearly and topologically isomorphic to $\mathscr{O}(\mathbf C)/(1-s/z)^{N(z)}\mathscr{O}(\mathbf C)$, which is seen by the same argument as for Theorem 7.1.4.2(1), using faithful flatness of $\mathbf C[s] \to \mathscr{O}(\mathbf C)$ and denseness of $\mathbf C[s] \subset \mathscr{O}(\mathbf C)$, by [Cnw-b, Ch.VIII, Cor.1.15, p.200].

As a $\mathbf C$-vector space, the quotient $\mathscr{O}(\mathbf C)/\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C)$ is linearly isomorphic to the direct product of the $K_z$, i.e. to $\prod_{z \in \mathbf C: \Lambda_f(\rho,\chi)=0} K_z$. This is seen as in the argument for Theorem 7.1.4.2(1), since $\mathbf C$ is Stein and the set of zeros of $\Lambda_f(s,\chi)$ is countable and discrete: upon denoting by $\mathscr{J} \subset \mathscr{O}$ the ideal sheaf globally generated by $\Lambda_f(s,\chi)$, we have

$$
\check{\mathrm{H}}(\mathbf C,\mathscr{O}/\mathscr{J}) = \mathrm{H}^1(\mathbf C,\mathscr{O}/\mathscr{J}) = 0
$$

and hence upon choosing a locally finite countable open cover $\{B_m\}_{m \ge 0}$ of the complex $s$-plane by open balls each of which contains at most one of the zeros $z$ of $\Lambda_f(s,\chi)$, then, upon denoting by $B_{\underline{k}}$ the intersection $\bigcap_{m \in \underline{k}} B_m$ for $\underline{k}$ varying over all non-empty finite subsets of the nonnegative integer, we deduce that $\mathrm{H}^0(B_{\underline{k}},\mathscr{J})$ is trivial if $\underline{k}$ contains at least two elements, and it is either trivial or $K_z$ if $\underline{k}$ contains one element exactly.

## PDF page 371

**7.4. NUCLEARITY** · **371**

This computes

$$
\mathscr{O}(\mathbf C)/\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C) = \check{\mathrm{H}}^0(\mathbf C,\mathscr{O}/\mathscr{J})
$$

to be $\prod_{z: \Lambda_f(z,\chi)=0} K_z$. The quotient topology $\mathscr{O}(\mathbf C)/\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C)$ is the product topology, since any compact subset $K \subset \mathbf C$ is contained in the union of at most finitely many of the $B_m$, and hence the linear bijection $\mathscr{O}(\mathbf C)/\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C) \to \prod_{z: \Lambda_f(z,\chi)=0} K_z$ is continuous. Being source and target Fréchet spaces, it is a linear topological isomorphism by [NB, Thm.14.4.5(b)].

The orthogonal of $\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C)$ in $\mathscr{O}(\mathbf C)'_\beta$, equipped with the subspace topology of the strong topology, is linearly isomorphic to the direct sum $\bigoplus_{z: \Lambda_f(z,\chi)=0} K'_z$. The subspace topology on the orthogonal $(\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C))^\perp$ inherited from the strong topology on $\mathscr{O}(\mathbf C)'_\beta$ is the finest locally convex topology, and hence the continuous linear bijection $(\mathscr{O}(\mathbf C)/\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C))'_\beta \to (\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C))^\perp$ is a linear topological isomorphism.

The continuous linear operator

$$
(\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C))^\perp \to \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))^\perp \tag{7.4.3.11}
$$

adjoint to the continuous linear map:

$$
A\mathcal S^p(\mathbf C)/L \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F)) \to \mathscr{O}(\mathbf C)/\Lambda_f(s,\chi)\,\mathscr{O}(\mathbf C).
$$

which is, in turn, injective with dense linear image, by denseness of $A\mathcal S^p(\mathbf C)$ in $\mathscr{O}(\mathbf C)$ and openness of the quotient linear operators, is injective with weakly dense range by [NB, Thm.8.13.1].

Since $A\mathcal S^p(\mathbf C)$ is a Fréchet space by Lemma D.3.1.2, nuclear by Proposition D.3.2.5, its quotient by the closed subspace $L \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))$ is also nuclear Fréchet, hence Montel, and by [Jar, Part II, Ch.11, §11.5, Prop.1, p.230] the range of the continuous linear operator from (7.4.3.11) is strongly dense. This implies that the continuous functionals from (7.4.3.4) are indeed linear topological generators for $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))^\perp$ in $A\mathcal S^p(\mathbf C)'_\beta$.

It remains to show that the image of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))$ under the Mellin transform $L$ into $A\mathcal S^p(\mathbf C)$ agrees with the closed subspace from (7.4.3.5).

(3), (4), (5) : By the global functional equation from (3.2.2.2) of Theorem 3.2.2.1, $Z(f,c')$ has a zero at $c'=c$ if and only if $Z(\widehat f,c')$ has a zero at $c'=\widehat c$, with matching multiplicities.

We now choose a large enough finite set $S$ of places of $F$ containing all the Archimedean places, such that $\chi$ is unramified outside $S$ and $\mathrm{Pic}(\mathcal O_{F,S})=1$. By Theorem 6.2.1.1(2), the operator:

$$
\overline{\pi}_S : \mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}(\mathbf A_{F,S})) \to \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}(\mathbf A_F))
$$

is a linear topological isomorphism, compatible with passage to the closed codimension-2 subspaces $\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf A_{F,S}))$ on the source, with $\mathcal{S}_0(\mathbf A_{F,S})=\ker(\delta_0)\cap\ker(\widehat\delta_0)$, on the source, and $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))$ on the target.

We can write, for each $\phi \in \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))$, $\phi = \overline{\pi}_S \circ \mathrm{PV}^{-1}_{S,S_f}(\phi_0)$ for a unique $\phi_0 \in \mathcal{S}_{00}(\mathbf A_{F,S})$, and hence the linear topological embedding with closed range (by Lemma 5.3.1.5) $\overline{\pi}_S \circ \mathrm{PV}^{-1}_{S,S_f}$ induces a linear topological isomorphism $\overline{\pi}_S \circ \mathrm{PV}^{-1}_{S,S_f}$ :

$$
\mathrm{PV}_{S,S_f} \mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf A_{F,S}))/\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_{00}(\mathbf A_{F,S})\cap\ker(\widehat\delta_0)) \to \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))/\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F)). \tag{7.4.3.12}
$$

In particular, the orthogonal of the subquotient on the rightmost side of (7.4.3.12) carries the finest locally convex topology, and it is linearly and topologically isomorphic to the strong dual of the quotient:

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))/\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))
$$

by Theorem 7.3.4.1(3).

## PDF page 372

**372** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

We now use calculations similar to those made in (8.1.0.10) from the proof of Theorem 7.5.0.1 and the formula for the coefficients of the principal parts of the $S$-idelic Zeta functions provided by Theorem 7.2.1.4. We write, for $\phi \in \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))$, $Z(\phi,\chi|\cdot|^s_F) = u(s) L_f(s,\chi)$ where $u(s) = Z_S(\phi_0,\chi_S|\cdot|^s_{F,S})$ for a unique $\phi_0 \in \mathrm{PV}_{S,S_f} \mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf A_{F,S}))$.

We therefore have, upon denoting by $\widehat u(s) := Z_S(\widehat\phi_0,\overline{\chi}_S|\cdot|^{1-s}_{F,S})$:

$$
Z(\widehat\phi,\overline{\chi}|\cdot|^{1-s}_F) = \widehat u(s)\,\widehat L_f(\chi,s)
$$

and by the same calculation in the proof of Theorem 7.5.0.1 (see (8.1.0.10)) using that $\widehat L_f(\chi,s)$ does not vanish for $s \in i\mathbf R$, equivalently $L_f(\overline{\chi},s)$ does not vanish for $s \in 1+i\mathbf R$, we deduce that the continuous functionals in (7.4.3.4) are indeed topologically free by Theorem 7.3.4.1(4), and hence any enumeration is a Schauder basis for $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))^\perp$ equipped with the subspace topology inherited from the strong topology, by [Jar, Part II, Ch.14, §14.2, Prop.3, p.292] (since, in this special case, such topology is the finest locally convex topology, and the convergence axiom for Schauder bases is satisfies since the possibly infinite sums involved in it are all convergent, being finite).

This also shows that the linear image of the continuous linear operator in (7.4.3.11) is strongly dense, because all the functionals $D^m_c$ from (7.4.3.4) are in the image. By [NB, Thm.8.10.6(e)], the linear image of $\mathcal{S}_{\infty,0}(\mathbf A_F)$ under the global Mellin transform $L$ to $A\mathcal S^p(\mathbf C)$, equivalently of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F))$, is weakly dense in the closed subspace of $A\mathcal S^p(\mathbf C)$ from (7.4.3.5) (because its continuous adjoint maps a sequence of topologically free topological generators into a topologically free set and it is therefore injective, and hence the Theorem applies).

By [Jar, Part II, Ch.11, §11.5, Prop.1, p.230], it is strongly dense, and hence it agrees with the closed subspace from (7.4.3.5), since it is itself closed (since $L$ has closed range by Theorem 7.1.4.3 and $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F)) \subset \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))$ is closed). This finishes the proof of (2) and hence of (3), (4) and (5). $\square$

We recall that we defined the closed subspace:

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F)) \subset \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))
$$

in (7.4.3.1), and Theorem 7.4.3.1 exhibits a Schauder basis for the strong dual of the subquotient:

$$
\mathscr{E}_{S_\infty} := \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))/\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F)) \tag{7.4.3.13}
$$

We recall from Theorem 7.4.3.1 that $\mathscr{E}_{S_\infty}$ is linearly and topologically isomorphic to the Hausdorff locally convex topological $\mathbf C$-vector space of formal power series in finitely many indeterminates, topologized with the topology of Euclidean-norm convergence of the coefficients, and its strong dual is linearly and topologically isomorphic to the Hausdorff locally convex topological $\mathbf C$-vector space of polynomials in the same number of indeterminates, carrying the finest locally convex topology.

The following is an Archimedean analog of Theorem 7.4.2.1.

Theorem 7.4.3.2 (Strong Topologies and Nuclearity - III). *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $\tau$ be a choice of continuous homomorphic section to the idelic norm.*

(1) *The linear subspace*

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_{\infty,0}(\mathbf A_F)) \subset \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))
$$

*defined in (7.4.3.1), is a closed $\mathcal D(C_F)$-submodule.*

(2) *Let $\varphi \in \mathcal D(C_F)$ be a test function. Assume $\varphi$ is supported over $C^{>1}_F$. Upon denoting by $A_{\mathrm{geom},\infty,\chi}(\varphi)$ the operator induced on $\mathscr{E}_{S_\infty}$ by $A(\varphi)$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}_0(\mathbf A_F))$, then $A_{\mathrm{geom},\infty,\chi}(\varphi)$ is a continuous operator whose matrix trace with respect to the Schauder basis provided by*

## PDF page 373

**7.4. NUCLEARITY** · **373**

Theorem 7.4.3.1(3), is finite, with value:

$$
\mathrm{Trace}(A_{\mathrm{geom},\infty,\chi}(\varphi)) = \sum_{z} N(\chi|\cdot|^z_F) \int_{C_F} \varphi(g)\chi(g)|g|^z_F\,\mathrm{d}\overline{\mu}(g) - \delta_\chi \cdot \int_{C_F} \varphi(g)|\cdot|^{-ix_0}_F\,\mathrm{d}\overline{\mu}(g) \tag{7.4.3.14}
$$

*where $x_0 \in \mathbf R$ is the unique real number such that $\chi(\tau(t)) = t^{ix_0}$ as smooth functions on $\mathbf R_{>0}$, and where the sum is over the complex numbers $z$ such that $\chi|\cdot|^z_F$ is a zero of the entire function $\prod_{v \in S_\infty} L_v(\chi|\cdot|^s_F)^{-1}$ of multiplicity $N(\chi|\cdot|^z_F)$, contained in the connected component $\Omega(C_F)(\chi|_{C^1_F})$, with $L_v(\chi|\cdot|^s_F)$ the local Euler factor at $v$ of the Hecke $L$-function $L(s,\chi)$, and $\delta_\chi = 0$ if $\chi|_{C^1_F} \ne 1$, and $\delta_\chi = 1$ if $\chi|_{C^1_F}=1$.*

Remark 7.4.3.3. We note that since the strong dual $(\mathscr{E}_{S_\infty})'_\beta$ carries the finest locally convex topology, then $A_{\mathrm{geom},\infty,\chi}(\varphi)$ cannot be nuclear, since the only nuclear operators on $(\mathscr{E}_{S_\infty})'_\beta$ are the finite rank operators. Nonetheless, $A_{\mathrm{geom},\infty,\chi}(\varphi)$ has a matrix trace, computed with respect to the chosen Schauder basis provided by Theorem 7.4.3.1(3).

Proof. We are to show that the sum in the right side of (7.4.3.14) is absolutely convergent: it formally agrees with the matrix trace of $A_{\mathrm{geom},\infty,\chi}(\varphi)$ by following the same calculation in (10.3.1.8) from the proof of (10.3.1.3) of Theorem 10.3.1.1. This is a consequence of the assumption made on the support of $\varphi$.

Indeed, upon fixing real numbers $a,b > 0$, then by Proposition B.2.1.9(4), upon writing:

$$
\Phi(s) := \int_{C_F} \varphi(g)\chi(g)|g|^s_F\,\mathrm{d}\overline{\mu}(g)
$$

the entire function $\Phi$ is an element of $H^p(\mathbf{C}_{<b})$ for every $p \ge 1$ (see §B.2.1), and hence the Asymptotic Residue Theorem (see Theorem B.3.2.1) implies that we have, upon defining $\Gamma_F(\chi,s) := \prod_{v \in S_\infty} L_v(\chi_v|\cdot|^s_v)$:

$$
-\frac{1}{2\pi i} \int^{-a+i\infty}_{-a-i\infty} \Phi(s)\frac{\Gamma_F(\chi,s)'}{\Gamma_F(\chi,s)}\,\mathrm{d}s + \frac{1}{2\pi i} \int^{b+i\infty}_{b-i\infty} \Phi(s)\frac{\Gamma_F(\chi,s)'}{\Gamma_F(\chi,s)}\,\mathrm{d}s = \sum_{z: \mathrm{Re}(z) \in (-a,b)} N(\chi|\cdot|^z_F)\Phi(z) \tag{7.4.3.15}
$$

and since $\Phi$ is an element of the Hardy space $H^2(\mathbf{C}_{<b})$, then the line integral over the $-a$-line tends to zero as $a \to +\infty$, the sum in the right side of (7.4.3.15) being finite and indexed by the singularities of $\Gamma_F(\chi,s)'/\Gamma_F(\chi,s)$ contained within the vertical strip $\mathbf{C}_{(-a,b)}$.

Upon choosing $b > 1$, the sum in the right side of (7.4.3.15) tends to the sum in (7.4.3.14) with the $\Phi(-ix_0)$ summand removed, as $a \to +\infty$, showing that the desired convergence assertion holds.

To see that the mode of convergence is absolute, we proceed as in [Den, §2, (2.16), (2.17), pp.9-10]. We have:

$$
\frac{\Gamma(s)'}{\Gamma(s)} = -\gamma - \sum_{m \le -1} \left(\frac{1}{m} + \frac{1}{s-m}\right) - \frac{1}{s} \tag{7.4.3.16}
$$

which is valid over $\mathbf C - \mathbf N_{<0}$ and is a consequence of Euler's Duplication Formula, the convergence of the sum in the right side of (7.4.3.16) being uniform over the compact subsets of $\mathbf C - \mathbf N_{<0}$.

By (B.4.1.22) from Lemma B.4.1.9, the sum also satisfies the estimate:

$$
\sum_{m \le -1} \left|\frac{1}{m} + \frac{1}{s-m}\right| \ll |s|.
$$

We further refer the reader to [Den, §2, Lemma 2.11, p.8] for a stronger estimate.

Since $\Phi(s)$ is Schwartz uniformly on the vertical strips of bounded width of the complex $s$-plane, the integral $\int^{b+i\infty}_{b-i\infty} |\Phi(s)|\,|s|\,|\mathrm{d}s|$ converges, and bounds from above the sum:

$$
\sum_{m \le -1} |\Phi(m)| = \frac{1}{2\pi} \sum_{m \le -1} \left|\int^{b+i\infty}_{b-i\infty} \Phi(s) \left\{\frac{1}{m} + \frac{1}{s-m}\right\}\,\mathrm{d}s\right| \le \frac{1}{2\pi} \int^{b+i\infty}_{b-i\infty} |\Phi(s)|\,|s|\,|\mathrm{d}s| \tag{7.4.3.17}
$$

## PDF page 374

**374** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

where we used Theorem B.2.2.4 (see also [Dur, Ch.11,Thm.11.8]). The estimate in (7.4.3.17) implies that the sum in the right side of (7.4.3.15) tends to its limit absolutely, and hence the sum in the right side of (7.4.3.14) is absolutely convergent.
$\square$

**7.5. Strong Co-Primality**

The Theorems contained within this subsection and the next are not logically necessary for the rest of the arguments leading to the main trace calculation, which is the subject of this work.

However, we will be using them to explain the presence and role of certain structures underlying the nuclear Fréchet spaces

$$
\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S})),\quad \mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))
$$

for $\chi\in \widehat{C_F}$ a continuous character, and $S$ a finite set of places of the number field $F$ containing all the Archimedean places, and such that $\chi$ is unramified outside $S$.

Specifically, we will be dicussing how predictions of Deninger on the existence of a “space” exhibiting periodic orbits and fixed points related to the primes, both infinite and finite, of $F$, are indeed correct, and the role that such structures play behind the scenes (without directly entering the arguments).

The next Theorem is an important ingredient leading to the construction of such periodic orbits and fixed points, and the space hosting them: a topological stack built as a quotient of a sub-locus within the $S$-adeles $\mathbf A_{F,S}$ for all large $S$, serving as the equivariant support for the eigendistributions and their derivatives, of which the unconditional Schauder bases we have identified throughout the previous sections on large subquotients of

$$
\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))
$$

are comprised.

In other words, the periodic orbits and fixed points whose existence and role Deninger predicted, serve, in a precise sense to be explained in the next subsection, as the supports of the Orbital Schauder bases, therefore justifying the terminology.

The Mellin transform, both $S$-local and global, sets up a correspondence between these, and certain divisors on the Riemann surfaces $\Omega(J_{F,S})$ and $\Omega(C_F)$.

The following Theorem, uses the existence of classical zero-free regions (through the non-vanishing and polynomial growth of the reciprocal of the finite Hecke $L$-function on the $1$-line; see Theorem B.6.1.6), together with the existence and properties of the $S$-local Orbital Schauder Bases provided by Theorem 7.3.1.6, as an input.

Theorem 7.5.0.1 (Strong Co-Primality). *Let $F$ be a number field, $\chi\in \widehat{C_F}$ a continuous character. Let $S_0$ be a finite set of finite places of $F$. The canonical continuous linear map:*

$$
\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))/\mathrm{PV}_{S_0}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \to \mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{S_0}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F}) \tag{7.5.0.1}
$$

*induced by the linear topological embedding:*

$$
\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \to \mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F}) \tag{7.5.0.2}
$$

*is a linear topological isomorphism.*

*Proof.* We choose $N\ge 1$ distinct finite places $v_1,\dots,v_N$ of $F$, and choose local uniformizers $\pi_{v_k}$ for $1\le k\le N$.

We recall that for $G$ an $\mathbf R_{>0}$-modulated group (in particular, $G$ is Hausdorff, locally compact, abelian), and $|\cdot|_G:G\to\mathbf R_{>0}$ the proper surjective module homomorphism with compact kernel $G^1$ (see Definition D.2.1.1), and for $\gamma\in G$ such that $|\gamma|_G>1$, we defined in (4.5.1.3) from Proposition 4.5.1.1 the continuous

## PDF page 375

**7.5. STRONG CO-PRIMALITY** · **375**

linear operator with closed range:

$$
P_\gamma:\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})\to\mathcal{S}_{\mathrm{E}}(G)(\chi|_{G^1})
$$

for each $\chi\in\widehat{G}$, assigned by sending $\phi\in\mathcal{S}_{\mathrm{E}}(G)$ to $\phi(x)-\phi(\gamma x)$.

For $\gamma=\pi_{v_k}^{-1}$ we therefore denote by $P_k$ the operator $P_{\pi_k^{-1}}$, with $G=C_F$, $|\cdot|_G=|\cdot|_F$.

We retain the notation from Situation 4.6.1.1, where $P_{(\pi_1^{-1},\pi_2^{-1})}$ denotes the composition $P_1P_2$ on $\mathcal{S}_{\mathrm{E}}(C_F)$ and its $C^1_F$-isotypes.

We define:

$$
\mathcal{E}_{\{v_1,\dots,v_N\}}(\chi|_{C^1_F}):=\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))/\mathrm{PV}_{\{v_1,\dots,v_N\}}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \tag{7.5.0.3}
$$

and:

$$
\mathcal{E}_{N-1,N}(\chi|_{C^1_F}):=\mathrm{PV}_{\{v_1,\dots,v_{N-1}\}}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))/\mathrm{PV}_{\{v_1,\dots,v_N\}}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \tag{7.5.0.4}
$$

and analyze the following diagram of continuous linear operators, all induced by the linear topological embedding from (7.5.0.2):

(7.5.0.5)

```latex
\begin{tikzcd}
\mathscr{E}_{1,2}(\chi|_{C^1_F}) \arrow[r] \arrow[d] & \mathscr{E}_{\{v_1,v_2\}}(\chi|_{C^1_F}) \arrow[r] \arrow[d] & \mathscr{E}_{\{v_1\}}(\chi|_{C^1_F}) \arrow[d] \\
P_1\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{(\pi_{v_1}^{-1},\pi_{v_2}^{-1})}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F}) \arrow[r] & \mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{(\pi_{v_1}^{-1},\pi_{v_2}^{-1})}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F}) \arrow[r] & \mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_1\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})
\end{tikzcd}
```

where we observe that the operator $\mathrm{PV}_{v_1}$ on $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))$ and the operator $P_1$ on $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$ induce the following commutative diagram of continuous linear operators:

(7.5.0.6)

```latex
\begin{tikzcd}
\mathscr{E}_{\{v_2\}}(\chi|_{C^1_F}) \arrow[r] \arrow[d] & \mathscr{E}_{1,2}(\chi|_{C^1_F}) \arrow[d] \\
\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_2\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F}) \arrow[r] & P_1\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{(\pi_{v_1}^{-1},\pi_{v_2}^{-1})}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})
\end{tikzcd}
```

By (4.6.1.7) from Lemma 4.6.1.3, the bottom horizontal arrow in (8.1.0.5) is a linear topological isomorphism, and since reciprocal Euler factors are bounded uniformly on vertical strips of bounded width, and Euler factors are periodic meromorphic functions whose poles are located on $i\mathbf R$ only and with, therefore, slow growth near their poles in the sense of Definition B.3.1.1, an application of the Asymptotic Residue Theorem (see Theorem B.3.2.1) shows that the top horizontal arrow is surjective.

If the leftmost vertical arrow in (8.1.0.5) is also injective, then it is a linear topological isomorphism by [NB, Thm.14.4.5(a)], being source and target Fréchet spaces, and so are the remaining three arrows in (8.1.0.5), since they would then all be continuous bijections between Fréchet spaces.

This observation, combined with commutativity of the diagram in (8.1.0.4), whose rows are linearly and topologically exact by another application of the Asymptotic Residue Theorem (see the argument provided for Lemma 4.6.1.3, which applies to the bottom row in (8.1.0.4) directly, and adapts to the top row), shows that for the continuous linear operator in (7.5.0.1) to be a linear topological isomorphism, it is enough to show that it is so if $S=\{v\}$, a single finite place of $F$.

From Theorem 7.1.4.3 combined with Lemma 4.4.2.6, we deduce that the rightmost vertical arrow in (8.1.0.4) is injective, by an application of [NB, Thm.8.10.6(e)] (which applies by reflexivity of source and target, which in turn holds since both source, by Corollary 6.2.1.2, and target, by Theorem D.3.3.7(1), are nuclear, by [Scha, Ch.III,§7,Thm.7.4,p.103], Fréchet spaces, hence Montel by [Tre, Part III,Ch.50,Cor.3,p.520], hence reflexive), since the dual Schauder basis on $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_1\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$ provided by Lemma 4.4.2.6 (which discusses the Exponential System on the $G^1$-isotypes of $\mathcal S(G/\gamma^{\mathbf Z})$ for $G$ an $\mathbf R_{>0}$-modulated group,

## PDF page 376

**376** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

$\gamma\in G$ an element with $|\gamma|_G>1$), maps under the continuous adjoint of the continuous linear operator which is the rightmost vertical arrow in (8.1.0.4), onto a topologically free set of continuous functionals in the strong dual of $\mathscr{E}_{\{v_1\}}(\chi|_{C^1_F})$ (because any of its enumerations admits a bi-orthogonal sequence by the Theorem, and [Jar, Part II,Ch.14,§14.1,Prop.1,p.289] applies).

It follows that in order to prove that the rightmost vertical arrow in (8.1.0.4) is surjective, hence a linear topological isomorphism by [NB, Thm.14.4.5(a)], being source and target Fréchet spaces, it is enough to show that the middle vertical arrow in (8.1.0.4) is a linear topological isomorphism.

It is therefore enough to show that the continuous linear map:

$$
\mathscr{E}_{\{v_1,\dots,v_N\}}(\chi|_{C^1_F})\to\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{S_p}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F}) \tag{7.5.0.7}
$$

where $p$ is the residue characteristic of $v_1:=v$, and $S_p=\{v_1,\dots,v_N\}$ is the finite set of all those finite places of $F$ whose residue characteristic is $p$.

By Theorem 7.1.4.3, the continuous linear operator in (8.1.0.7) is injective, since the continuous functionals given by evaluation at the zeros $z$ of $\prod_{v\in S_p}(1-\chi(\mathfrak p_v)q_v^{-s})$ and their derivatives of order $0\le m\le N(z)-1$, for $N$ the multiplicity function of the zeros of $\prod_{v\in S_p}(1-\chi(\mathfrak p_v)q_v^{-s})$, pre-composed by the global Mellin transform $L$ from (5.1.1.1) uniquely determined by the assignment $f\mapsto Z(f,\chi|\cdot|^s_F)$ for $f\in\mathcal S_0(\mathbf A_F)$, map under the continuous adjoint to the continuous linear operator (8.1.0.7) to a subset of a topologically free set of continuous functionals in the strong dual of $\mathscr{E}_{\{v_1,\dots,v_N\}}(\chi|_{C^1_F})$, hence itself topologically free (because any of its enumerations admits a bi-orthogonal sequence by the Theorem, and hence [Jar, Part II,Ch.14,§14.1,Prop.1,p.289] applies).

We may therefore replace $S_0$ with $S_p$ in the statement of Theorem 7.5.0.1. We observe that by Theorem 7.1.4.3 and [NB, Thm.8.10.6(e)], which applies, as in the foregoing, by reflexivity of source and target, that the continuous linear operator in (7.5.0.1) is injective.

Upon showing it is surjective, it is therefore a linear topological isomorphism by [NB, Thm.14.4.5(a)].

We will now use the $S$-local Orbital Schauder Basis provided by Theorem 7.3.1.6, with $S:=S_\infty\cup S_p\cup S_1$, to show that the continuous injective linear operator from (7.5.0.1) is surjective, with $S_1$ a finite set of finite places of $F$, disjoint from $S_p$, chosen so as to arrange $S$ to be large enough so that $\chi$ is unramified outside $S$, and $\mathrm{Pic}(\mathcal O_{F,S})=1$.

Under these conditions on $S$, the transition operator:

$$
\overline{\pi}_S:\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))
$$

from Theorem 5.2.1.1(3), is a linear topological isomorphism. We denote by $\chi_S$ the unique continuous character of $J_{F,S}$ obtained from the restriction of $\chi$ to $C_{F,S}\subset C_F$ by descent by $\widehat{\mathcal O}^{\times}_{F,\Sigma_F-S}$-invariance.

The idea is to show that the image of the absolute Orbital Schauder Basis on the $p$-primary Orbital Quotients $\mathscr{E}_{S,S_p}(\chi_S|_{J^1_{F,S}})$ from (7.3.1.5) (see Definition 7.3.1.3) not only remains a Schauder basis in the global subquotient:

$$
\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))/\mathrm{PV}_{S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))
$$

which it does since $\overline{\pi}_S$ is a linear topological isomorphism compatible with Weil’s Principal Value operators $\mathrm{PV}_{S,S_p}$ on the source, and $\mathrm{PV}_{S_p}$ on the target, but also in $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{S_p}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$.

This is where the estimates in (7.3.1.17) from Theorem 7.3.1.6(4) are used, together with the rapid decay uniformly on vertical strips of bounded width of the complex $s$-plane, of the Mellin transform of the elements of $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$.

We will show below that, in order to prove the desired basis property, such estimates need to be combined with the polynomial growth of the derivatives of the Hecke $L$-function on vertical lines, and with, most importantly, the polynomial growth of the reciprocal of the finite Hecke $L$-function on the $1$-line (for which we refer the reader to Remark B.1.1.4 and Theorem B.6.1.6).

## PDF page 377

**7.5. STRONG CO-PRIMALITY** · **377**

This will indeed show surjectivity of (7.5.0.1) (we will be providing the argument below), therefore finishing the proof of the Theorem.

By Lemma 5.3.1.5, we have:

$$
\overline{\pi}_S\circ\mathrm{PV}_{S,S_p}=\mathrm{PV}_{S_p}\circ\overline{\pi}_S
$$

on $\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$.

By Theorem 6.2.1.1(2):

$$
\overline{\pi}_S:\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))\to\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))
$$

is a linear topological isomorphism.

We call, for $c$ the arbitrary zero of $L_v(c)^{-1}$ contained in $\Omega(C_F)(\chi|_{C^1_F})$, parametrized by $\chi|\cdot|^{s_c}_F$ (equivalently in $\Omega_S(J_{F,S})(\chi|_{J^1_{F,S}})$, since, in light of the assumption $\mathrm{Pic}(\mathcal O_{F,S})=1$, all the zeros of $L_v(c)^{-1}$ in $\Omega(C_F)(\chi|_{C^1_F})$ for each $v\in S$ are contained in $\Omega_S(C_F)(\chi|_{C^1_F})$, which admits a surjective local analytic isomorphism onto $\Omega(J_{F,S})(\chi|_{J^1_{F,S}})$ whose fibres are single-point discrete sets):

$$
\gamma^{(k)}_c(\phi):=\partial^k_s Z(\mathcal{F}(\phi), \overline{\chi}|\cdot|^s_F)|_{s=1-s_c} \tag{7.5.0.8}
$$

for $\mathcal{F}:\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))\to\mathrm H_{0,\mathrm{cont}}(\overline{\chi}|_{C^1_F}, \mathcal S(\mathbf A_F))$.

We have $\gamma^{(k)}_c\in\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S(\mathbf A_F))'_\beta$ for each zero $c$ of $L_v(c)^{-1}$ contained in $\Omega(C_F)(\chi|_{C^1_F})$ for each $v\in S_0$, and $0\le k\le N_S(c)-1$.

Assume $\phi=\overline{\pi}_S(\phi_0)$ for a unique $\phi_0\in\mathrm H_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal S(\mathbf A_{F,S}))$.

We have:

$$
\gamma^{(k)}_c(\phi)=\partial^k_s(Z_S(\mathcal{F}_S(\phi_0), \overline{\chi}|\cdot|^s_{F,S})L_S(\overline{\chi},s))|_{s=1-s_c}
$$

where $L_S(\overline{\chi},s)=\prod_{v\in S}L_v(\overline{\chi}_v|\cdot|^s_v)^{-1}\cdot L(\overline{\chi},s)$ for $s\in\mathbf C_{>0}$, extended meromorphically to the complex $s$-plane.

$$
\gamma^{(k)}_c(\phi)=\left\{\sum_{0\le m\le k}\binom{k}{m}\partial^m_s(Z_S(\mathcal{F}_S(\phi_0), \overline{\chi}|\cdot|^s_{F,S})\cdot\partial^{k-m}_s L_S(\overline{\chi},s)\right\}|_{s=1-s_c} \tag{7.5.0.9}
$$

$$
=\sum_{0\le m\le k}\binom{k}{m}\partial^m_s(Z_S(\mathcal{F}_S(\phi_0), \overline{\chi}|\cdot|^s_{F,S})|_{s=1-s_c}\cdot\partial^{k-m}_s L_S(\overline{\chi},s)|_{s=1-s_c} \tag{7.5.0.10}
$$

$$
=\sum_{0\le m\le k}\binom{k}{m}\delta^m_{S,c}(\phi_0)\cdot\partial^{k-m}_s L_S(\overline{\chi},s)|_{s=1-s_c} \tag{7.5.0.11}
$$

where we have denoted by $\delta^m_{S,c}$ the continuous functionals:

$$
\widehat\delta^{(m)}_c
$$

from (7.3.1.13) of Theorem 7.3.1.6, which, by the Theorem, constitute, upon choosing an enumeration of their set, an unconditional Schauder basis for $\mathscr{E}_{S,S_p}(\chi_S|_{J^1_{F,S}})'_\beta$.

We rewrite (8.1.0.8) in matrix form

$$
\overline{\pi}'_S(\gamma^{(k)}_c)=(\delta^m_{S,c})_{1\le m\le k}\cdot A_{c,k,\chi} \tag{7.5.0.12}
$$

## PDF page 378

**378** · **CHAPTER 7. SCHAUDER BASES OF IDELIC ZETA FUNCTIONS**

with $A_{c,k,\chi}$ the $k\times k$ triangular matrix with complex coefficients:

$$
\begin{bmatrix}
L_S(\overline{\chi},1-s_c) & L^{(1)}_S(\overline{\chi},1-s_c) & L^{(2)}_S(\overline{\chi},1-s_c) & L^{(3)}_S(\overline{\chi},1-s_c) & L^{(4)}_S(\overline{\chi},1-s_c) & \cdots & L^{(k)}_S(\overline{\chi},1-s_c) \\
0 & L_S(\overline{\chi},1-s_c) & 2L^{(1)}_S(\overline{\chi},1-s_c) & 3L^{(2)}_S(\overline{\chi},1-s_c) & 4L^{(3)}_S(\overline{\chi},1-s_c) & \cdots & kL^{(k-1)}_S(\overline{\chi},1-s_c) \\
0 & 0 & L_S(\overline{\chi},1-s_c) & 3L^{(1)}_S(\overline{\chi},1-s_c) & 6L^{(2)}_S(\overline{\chi},1-s_c) & \ldots & \binom{k}{2}L^{(k-2)}_S(\overline{\chi},1-s_c) \\
0 & 0 & 0 & L_S(\overline{\chi},1-s_c) & 4L^{(1)}_S(\overline{\chi},1-s_c) & \cdots & \binom{k}{3}L^{(k-3)}_S(\overline{\chi},1-s_c) \\
\cdots & \cdots & \cdots & \cdots & \cdots & \cdots & \cdots \\
0 & 0 & 0 & 0 & 0 & \cdots & L_S(\overline{\chi},1-s_c)
\end{bmatrix} \tag{7.5.0.13}
$$

Its determinant is $L_S(\overline{\chi},1-s_c)^{k}\ne 0$, where its non-vanishing is a consequence of the non-vanishing of the Hecke $L$-function $L(\overline{\chi},s)$ on the $1$-line, which holds by [CF, Ch.VIII,§2,Thm.2,p.212].

We now observe that we have $\gamma^{(m)}_c=U(\delta^{(m)}_c)$ (the notation being as in Theorem 7.1.4.3(2)), by the global functional equation from (3.2.2.2) of Theorem 3.2.2.1, where $\delta^{(m)}_c$ and $U(\delta^{(m)}_c)$ are the continuous functionals in $\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))'_\beta$ from (7.1.4.27) of Theorem 7.1.4.3.

By Theorem 4.6.1.5 applied to $G=C_F$, $|\cdot|_G=|\cdot|_F$, to the choice of continuous character $\chi$, with the set $S$ of elements of $G$ chosen to be $(\pi_{v}^{-1})_{v\in S_p}$, upon choosing an ordering for the finite set $S_p$, and adopting the notation from Situation 4.6.1.1(3), we deduce that the set $\{\gamma^{(k)}_c\}_{c\in \mathcal{U}_{S_p},0\le k\le N_p(c)-1}$ is the image under the continuous adjoint of (7.5.0.1) of the unconditional Schauder basis given by the functionals defined in (4.6.1.14), for the strong dual of $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{S_p}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$.

We now rewrite:

$$
\gamma^{(k)}_c=((\overline{\pi}^{-1}_S)'(\delta^m_{S,c}))_{1\le m\le k}\cdot A_{c,k,\chi} \tag{7.5.0.14}
$$

The bi-orthogonal set to $\{\gamma^{(k)}_c\}_{c\in \mathcal{U}_{S_p},0\le k\le N_p(c)-1}$ in $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{S_p}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$ is therefore obtained from the bi-orthogonal set to the unconditional Schauder basis $\{(\overline{\pi}^{-1}_S)'(\delta^m_{S,c})\}_{c\in \mathcal{U}_{S_p},0\le m\le N_p(c)-1}$ by right multiplication of each finite subset of $N_p(c)$ indexed by the same fixed $c\in \mathcal{U}_{S_p}$, by $A^{-1}_{c,N_p(c),\chi}$.

The operator norm of each matrix $A^{-1}_{c,N_p(c),\chi}$ (whose rank is, recall, bounded above by $[F:\mathbf Q]$, the degree of the number field, since $N_p(c)\le[F:\mathbf Q]$) grows polynomially with respect to the ordinate of $c$ with respect to the holomorphic parametrization $c=\chi|\cdot|^s_F$, by Theorem B.6.1.6 and Remark B.1.1.4.

By the estimates from (4.6.1.17) of Theorem 4.6.1.5 and from (7.3.1.17) of Theorem 7.3.1.6 respectively, and the exponential decay of every element $\phi$ of $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$, which implies that the sequence of complex numbers $(\overline{\pi}^{-1}_S)'(\delta^m_{S,c})(\phi)$ for each of the finitely many fixed $0\le m\le N_p(c)-1\le[F:\mathbf Q]$ decays rapidly (with respect to the integer $m_v$ parametrizing the point $c=\chi|\cdot|^{\frac{2\pi im_v}{\log(q_v)}-it_v}_F$ as per Lemma 7.1.2.2, for a, equivalently any, choice of $v\in S_p$ such that $c\in\psi^{-1}_v(\mathcal{U}_v)$, as $|m_v|\to+\infty$) the image in $\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})/P_{S_p}\mathcal{S}_{\mathrm{E}}(C_F)(\chi|_{C^1_F})$ of the absolute Schauder basis $\{(\overline{\pi}^{-1}_S)'(\delta^m_{S,c})\}_{c\in \mathcal{U}_{S_p},0\le m\le N_p(c)-1}$ is an absolute Schauder basis.

This implies surjectivity of (7.5.0.1) in the special case $S_0=S_p$, which finishes the proof of the Theorem. $\square$

Remark 7.5.0.2. Theorem 7.5.0.1 implies that for each prime $p$, the subquotients:

$$
\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F))/\mathrm{PV}_{S_p}\mathrm H_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal S_0(\mathbf A_F)) \tag{7.5.0.15}
$$

all nuclear Fréchet spaces, carry Hausdorff locally convex topologies that can be understood concretely.

Indeed, by Theorem 6.2.1.1, they are linearly and topologically isomorphic to the nuclear Fréchet spaces:

$$
\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_{F,S}))/\mathrm{PV}_{S_p}\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal S_0(\mathbf A_F)) \tag{7.5.0.16}
$$

for $S$ a finite set of finite places of $F$ containing all the Archimedean places, and such that $\chi$ is unramified outside $S$, and $\mathrm{Pic}(\mathcal O_{F,S})=1$ (upon denoting by $\chi_S$ the unique continuous character of $J_{F,S}$ obtained by descending by $\widehat{\mathcal O}^{\times}_{\Sigma_F-S}$-invariance the restriction of $\chi$ to $C_{F,S}$), and the subquotients in (7.5.0.16) are in turn

## PDF page 379

**7.5. STRONG CO-PRIMALITY** · **379**

linearly and topologically isomorphic to closed subspaces of quotients by a closed subspace of a finite product of copies of $\mathcal S(\mathbf R_{>0}/q^{\mathbf Z})$ for $q$ ranging over finitely many powers of $p$.

Under these assumptions, $\overline{\pi}_S$ is a linear topological isomorphism (see Theorem 6.2.1.1) compatible with the operators $\mathrm{PV}_{S,S_p}$ and $\mathrm{PV}_{S_p}$ on source, respectively target (see Lemma 5.3.1.5).

In particular, they are Köthe Sequence Spaces.

The strong dual of the subquotient in (7.5.0.15) is in turn therefore linearly and topologically isomorphic to a quotient by a closed subspace of a closed subspace of a finite locally convex direct sum of copies of

$$
\mathcal S\left(\frac{2\pi i}{\log(q)}\mathbf Z\right)\simeq\mathcal S(\mathbf Z).
$$

We will be collecting the following Corollary, which is a strong form of the non-vanishing of the Hecke $L$-function $L(s,\chi)$ on the $1$-line. By solving the a Second Cousin Problem for the pair of entire functions $(\Lambda(s,\chi),(1-\chi(\mathfrak p_v)q_v^{-s}))$, we know from the non-vanishing of $L(s,\chi)$ (see [CF, Ch.VIII,Thm.2,p.212]) that there exist entire functions $u,v\in\mathscr{O}(\mathbf C)$ such that:

$$
\Lambda(s,\chi)\cdot u(s)+(1-\chi(\mathfrak p_v)q_v^{-s})\cdot v(s)=1
$$

as entire functions over the complex $s$-plane.

We have no way to tell anything about the growth behavior of $u,v$. Using the Schauder Bases identified throughout this Chapter, and as a consequence of Theorem 7.5.0.1, we have the following:

Corollary 7.5.0.3 (Strong Co-Primality). *Let $F$ be a number field, $\chi\in \widehat{C_F}$ a continuous character. Let $S$ be a finite set of finite places of $F$ at which $\chi$ is unramified. We write, for each $v\in S$, $q_v:=N(\mathfrak p_v)$, with $\mathfrak p_v\subset\mathcal O_F$ the unique prime ideal corresponding to the finite place $v$. Let $\tau$ be a choice of continuous homomorphic section to the idelic norm. For any entire function $\phi\in A\mathcal{S}(\mathbf C)$, there exist entire functions $u\in\mathscr{O}(\mathbf C)$ such that $\Lambda(s,\chi)\cdot u\in A\mathcal{S}(\mathbf C)$, and $v\in A\mathcal{S}(\mathbf C)$, such that:*

$$
\Lambda(s,\chi)\cdot u(s)+\prod_{v\in S}(1-\chi(\mathfrak p_v)q_v^{-s})\cdot v(s)=\phi(s) \tag{7.5.0.17}
$$

*with $\Lambda(s,\chi):=((s+ix_0)(s+ix_0-1))^{\delta_\chi}L(s,\chi)$, for $\delta_\chi=1$ if $\chi|_{C^1_F}=1$, and $\delta_\chi=0$ otherwise, for $x_0\in\mathbf R$ the unique real number such that $\chi(\tau(t))=t^{ix_0}$ as smooth functions of $t\in\mathbf R_{>0}$.*

*Proof.* The Corollary follows upon combining Theorem 7.5.0.1 with Theorem 6.3.2.2. $\square$

## PDF page 380
