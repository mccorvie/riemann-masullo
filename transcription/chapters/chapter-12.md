## PDF page 497

CHAPTER 12

Trace formula: Geometric Side

12.1.
Smoothenings along the diagonal
498

12.1.1.
Localization along the global diagonal
498

12.2.
Lebesgue Differentiation along the diagonal
504

12.2.1.
Indentations
504

12.2.2.
Regular points on the diagonal and indentations
507

12.3.
Putting the pieces together: global to $S$-local deconstruction of the geometric kernel
514

12.4.
$S$-local trace calculation
514

12.4.1.
$S$-local trace on the Paley-Wiener Levels
514

12.5.
Trace formula: the Main Theorem of this work
519

12.5.1.
Trace Formula: the statement
519

497

## PDF page 498

**498** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

**12.1. Smoothenings along the diagonal**

**12.1.1. Localization along the global diagonal.** In this subsection we discuss how to use the kernel functions $k^{\mathrm{geom}}_{\varphi,a,s}(x,y)$, $k^{\mathrm{spec}}_{\varphi,a,s}$, and their products with $(\Lambda,\varepsilon)$ cutoffs functions $\rho(x)$ on $C_F$ in the sense of Definition 9.3.3.1, to compute the traces of $P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)$ as $\rho\to 1$ (as $\Lambda\to +\infty$ while having $\varepsilon\Lambda = o(1)$), and of $P^{\mathrm{spec}}_a\circ A(\varphi)$.

This requires a discussion of how to make sense of each of the above kernel functions along the diagonal in $C_F\times C_F$, a null set with respect to the product measure $\overline{\mu}\otimes\overline{\mu}$.

To this end, we will be using the analog for the idele class group $C_F$ (and later for its $S$-local subgroup $C_{F,S}$ and this latter's quotient $J_{F,S}$) of the Differentiation Theorem of Lebesgue, together with continuity properties of the Haar integral of $\overline{\mu}$-absolutely integrable functions over $C_F$.

This rests on an analog of the Hardy-Littlewood Maximal Theorem on Maximal functions, for which we refer the reader to Appendix A (see Theorem A.5.3.7 and Theorem A.5.4.1).

We begin with some results of a general nature, on Hilbert-Schmidt kernels on $L^2(G,\lambda)$, where $G$ is a Hausdorff locally compact second countable abelian group, and $\lambda$ is a Radon measure on $G$ subordinate to a choice of Haar measure $\mu_G$, i.e. such that there exists a locally $\mu_G$-integrable function $f\colon G\to\mathbf R_{\ge 0}$ satisfying $f\mu_G = \lambda$ as Radon measures on $G$.

Definition 12.1.1.1. Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is second countable. Let $\{U_k\}_{k\ge 0}$ be a $D'$-sequence for $G$ in the sense of Definition A.5.2.1.

Let $\phi\in L^1_{\mathrm{loc}}(G,\mu_G)$ be a locally $\mu_G$-integrable complex-valued function on $G$. We define the smoothening of $\phi$ to be the function defined as:

$$
\widetilde{\phi}(x) := \lim_{k\to +\infty}\frac{1}{\mu_G(U_k)}\int_{xU_k}\phi(y)\,\mathrm{d}\mu_G(y) \tag{12.1.1.1}
$$

at each point $x\in G$ at which the limit in (12.1.1.1) exists and is finite, and zero elsewhere.

We call a point $x\in G$ at which the limit in (12.1.1.1) exists and is finite, a regular point for $\phi$.

We recall that a $D$-sequence for a Hausdorff locally compact abelian group $G$, with $\mu_G$ a choice of Haar measure on $G$, is the datum of a sequence $\{U_k\}_{k\ge 0}$ where for each integer $k\ge 0$, $U_k\subset G$ is a $\mu_G$-measurable subset, $U_{k+1}\subset U_k$, the $\mu_G$-measure of each $U_k$ is finite and nonzero, there exists a real number $C > 0$ such that $\mu_G(U_kU_k^{-1}) < C\,\mu_G(U_k)$ for every $k\ge 0$.

We say $\{U_k\}_{k\ge 0}$ is a Borel $D$-sequence, respectively an open, symmetric $D$-sequence, if and only if each of its members is a Borel set, respectively an open subset, respectively a symmetric subset (i.e. stable under the inversion homomorphism on $G$).

We say $\{U_k\}_{k\ge 0}$ is a $D'$-sequence, if it is a Borel $D$-sequence satisfying the following additional property: for every unit-neighborhood $V$ of $G$, there exists a large enough integer $k_0\ge 0$ such that $U_{k_0}\subset V$. In particular, there exists $k_0\ge 0$ such that for every $k\ge k_0$, $U_k$ has compact closure.

For instance, for $G = \mathbf R^N$, the two sequences $\{U_k := B(0,r_k)\}_{k\ge 0}$ and $\{U'_k := Q_{r_k}\}$, for $\{r_k\}_{k\ge 0}$ a strictly decreasing sequence of real numbers with $r_0 > 0$, and with $B(0,r)$ the closed ball centered at $0$ with radius $r$, and $Q_r$ the cube in $\mathbf R^N$ of the form $[-r,r]^N$, are both symmetric $D'$-sequences.

The Hausdorff locally compact abelian groups under consideration throughout this work (global ideles, $S$-local ideles, their class groups, their closed subgroups of norm-one elements, their class groups of norm-one elements) are all equipped with symmetric $D'$-sequences. These are constructed in Appendix A, §A.5.2; see Definition A.5.2.1 and Definition A.5.2.18.

The presence of a $D'$-sequence in $G$ enables the definition of a corresponding maximal function analogous to the Hardy-Littlewood maximal function on Euclidean spaces, and analogs of the Maximal Theorem and of Lebesgue's Differentiation Theorem both hold. We refer the reader to [HR-2, Ch.XI, §44], and to Theorem A.5.3.7 and Theorem A.5.4.1.

## PDF page 499

**12.1. SMOOTHENINGS ALONG THE DIAGONAL** · **499**

In particular, maximal functions, the Maximal Theorem and Lebesgue's Differentiation Theorem, are available on the idelic groups and groups of idele classes being considered throughout this Chapter.

For locally integrable functions on $G\times G$, if $\{U_k\}_{k\ge 0}$ is a $D'$-sequence for $G$, we will be using the $D'$-sequence $\{U_k\times U_k\}_{k\ge 0}$ for $G\times G$ to define smoothenings (see Lemma A.5.2.5(1), which proves that indeed $\{U_k\times U_k\}_{k\ge 0}$ is a $D'$-sequence for $G\times G$).

The following Theorem explains the role of maximal functions and of the analogs of the Maximal Theorem of Hardy-Littlewood, and of the Differentiation Theorem of Lebesgue.

Theorem 12.1.1.2. *Let $G$ be a Hausdorff locally compact abelian group. Assume $G$ is second countable. Let $\mu_G$ be a choice of Haar measure on $G$. Let $\{U_k\}_{k\ge 0}$ be a $D'$-sequence for $G$ in the sense of Definition A.5.2.1.*

*Let $\lambda$ be a Radon measure on $G$ such that there exists a locally $\mu_G$-integrable function $f\colon G\to\mathbf R_{\ge 0}$ satisfying $\lambda = f\mu_G$ as Radon measures on $G$. Assume $f$ is continuous and nowhere vanishing on $G$.*

*Let $T\in \mathscr{L}_\beta(L^2(G,\lambda))$ be a nuclear operator, and $k\in L^2(G\times G,\lambda\otimes\lambda)$ a choice of representative for the Hilbert-Schmidt kernel of $T$.*

*Then, $\mu_G$-almost all points $(x,x)\in G\times G$ are regular for $k$.*

(1) *The function $\widetilde{k}(x,y)$ is a representative for the Hilbert-Schmidt kernel of $T$, and it is defined at $\mu_G$-almost all points of the diagonal in $G\times G$. The function $\widetilde{k}(x,x)$ of $x\in G$ is absolutely $\lambda$-integrable. We have:*

$$
\int_G \widetilde{k}(x,x)\,\mathrm{d}\lambda(x) = \mathrm{Trace}(T). \tag{12.1.1.2}
$$

(2) *Let $\rho\in C_c(G)$, and $M_\rho$ the corresponding multiplication operator on $L^2(G,\lambda)$. The smoothening of $\rho(x)k(x,y)$ is $\rho(x)\widetilde{k}(x,y)$, and both functions are representatives for the Hilbert-Schmidt kernel of the operator $M_\rho\circ T$ on $L^2(G,\lambda)$. If $\rho\in L^\infty(G,\lambda)$, then the function $\rho(x)\widetilde{k}(x,y)$ is a representative for the Hilbert-Schmidt kernel of the operator $M_\rho\circ T$, and we have:*

$$
\int_G \rho(x)\widetilde{k}(x,x)\,\mathrm{d}\lambda(x) = \mathrm{Trace}(M_\rho\circ T). \tag{12.1.1.3}
$$

(3) *For each integer $m\ge 0$, let $T_m\in \mathscr{L}_\beta(L^2(G,\lambda))$ be a finite rank operator, such that the sequence $\{T_m\}_{m\ge 0}$ converges in $S_p(L^2(G,\lambda))$ for $p = 1,2$, to $T$. Let $k_m\in L^2(G\times G,\lambda\otimes\lambda)$ be a choice of representative for the Hilbert-Schmidt kernel of $T_m$.*

*Then $k_m\to k$ and $\widetilde{k}_m\to\widetilde{k}$ in $L^2(G\times G,\lambda\otimes\lambda)$, and $\widetilde{k}_m(x,x)\to\widetilde{k}(x,x)$ weakly in $L^1(G,\lambda)$.*

(4) *Assume that there exists $\{\phi_m\}_{m\ge 0}$ a simple, normalized Schauder basis for $L^2(G,\lambda)$. Let $\{\theta_m\}_{m\ge 0}$ be the dual basis with respect to the duality pairing:*

$$
\langle\cdot,\cdot\rangle_\lambda\colon L^2(G,\lambda)\times L^2(G,\lambda^\vee)\to\mathbf C \tag{12.1.1.4}
$$

*where $\lambda^\vee$ is the Radon measure $(1/f)\mu_G$, defined by:*

$$
\langle\phi,\psi\rangle_\lambda := \int_G \phi(x)\psi(x)\,\mathrm{d}\mu_G(x). \tag{12.1.1.5}
$$

We define:

$$
k_N(x,y) := \sum_{0\le m\le N}\frac{(T'\theta_m)(y)}{f(y)}\phi_m(x) \tag{12.1.1.6}
$$

*where $T'\in \mathscr{L}_\beta(L^2(G,\lambda^\vee)$ is the adjoint of $T$ with respect to the duality $\langle L^2(G,\lambda),L^2(G,\lambda^\vee)\rangle_\lambda$.*

*Then $k_N\to k$ and $\widetilde{k}_N\to\widetilde{k}$ in $L^2(G\times G,\lambda\otimes\lambda)$, and $\widetilde{k}_N(x,x)\to\widetilde{k}(x,x)$ weakly in $L^1(G,\lambda)$.*

Proof. (1) : $T$ can be written as $T = A_1-A_2+i(A_3-A_4)$ where $A_i$ is nuclear and positive, for $1\le i\le 4$. Since formation of the smoothening of locally $\mu_G$-integrable functions on $G\times G$ with respect to the

## PDF page 500

**500** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

$D'$-sequence $\{U_k\times U_k\}_{k\ge 0}$ is $\mathbf C$-linear, we may rename each $A_i$ as $T$ and assume $T$ is nuclear and positive. By [Cnw-a, Ch.II, §2, Prop.2.12, p.33], $T$ is self-adjoint. Since $T$ is nuclear, $T$ is compact.

By [Cnw-a, Ch.II, §5, Cor.5.4, p.47], we have $T = \sum_{m\ge 0}\sigma_m(T)\langle\phi_m,\cdot\rangle_{L^2(G,\lambda)}\phi_m$, the convergence being with respect to the strong operator topology (see also Theorem C.3.6.1 applied to $E = F = L^2(G,\lambda)$), where the singular values of $T$ are listed decreasingly and counted with multiplicity.

Upon calling $P_m$ the orthogonal projector onto $\ker(T-\sigma_m(T)\mathrm{Id})$, then we may write $T = \sum_{m\ge 0}\sigma_m(T)P_m$, where the singular values of $T$ are now listed decreasingly and counted once for each integer $m\ge 0$. Each $P_m$ is self-adjoint by [Cnw-a, Ch.II, §2, Prop.2.12, p.33] and [Cnw-a, Ch.II, §3, Prop.3.3, p.37], and hence by Proposition C.3.6.5 (see also Corollary C.3.5.5), $P_mTP_m\to T$ in $S_p(L^2(G,\lambda))$ for $p = 1,2$.

The Hilbert-Schmidt kernel of $P_mTP_m$ is represented by the function

$$
k_m(x,y) := \sigma_m(T)\sum_{1\le r\le N_m}\overline{\phi}_{m,r}(y)\phi_{m,r}(x) \tag{12.1.1.7}
$$

where $N_m = \dim(\ker(T-\sigma_m(T)\mathrm{Id}))$ and $\{\phi_{m,r}\}_{1\le r\le N_m}$ is an orthonormal basis for $\ker(T-\sigma_m(T)\mathrm{Id})$.

Since $S_2(L^2(G,\lambda))$ is isometrically isomorphic to $L^2(G\times G,\lambda\otimes\lambda)$, and $P_mTP_m$ is sent to the class of $k_m(x,y)$ under such isometry, we deduce that the sequence of finite sums $\sum_{0\le m\le N}k_m(x,y)$ converges in $L^2(G\times G,\lambda\otimes\lambda)$.

We write:

$$
\psi_{m,r} := \phi_{m,r}\cdot (f)^{1/2} \tag{12.1.1.8}
$$

and observe that $\psi_{m,r}\in L^2(G,\mu_G)$ for every $m\ge 0$ and every $1\le r\le N_m$. Note that being $f$ continuous, real-valued and nonnegative, its square-root is well defined and single valued.

We define:

$$
k'_m(x,y) := \sigma_m(T)\sum_{1\le r\le N_m}\overline{\psi}_{m,r}(y)\psi_{m,r}(x) \tag{12.1.1.9}
$$

and observe that we have $k'_m\in L^2(G\times G,\mu_G\otimes\mu_G)$. The linear operator $\phi\mapsto\phi\cdot (f)^{1/2}$ is a surjective isometry $J_f\colon L^2(G,\lambda)\to L^2(G,\mu_G)$. It is indeed surjective, since its inverse is given by $\psi\mapsto\psi\cdot (f)^{-1/2}$, being $f$ nowhere vanishing over $G$.

The operator $J_f\circ (P_mTP_m)\circ J_f^{-1}$ is Hilbert-Schmidt and nuclear (in fact, of finite rank $N_m$) on $L^2(G,\mu_G)$, with kernel represented by the function $k'_m(x,y)$. The operator $J_f\circ T\circ J_f^{-1}$ is Hilbert-Schmidt and nuclear, with kernel:

$$
k'(x,y) := f(x)^{1/2}k(x,y)f(y)^{1/2}. \tag{12.1.1.10}
$$

Indeed, for any $\phi\in L^2(G,\mu_G)$, we have:

$$
\int_G k'(x,y)\phi(y)\,\mathrm{d}\mu_G(y) = f(x)^{1/2}\int_G k(x,y)f(y)^{1/2}\phi(y)\,\mathrm{d}\mu_G(y) = f(x)^{1/2}\int_G k(x,y)f(y)^{-1/2}\phi(y)\,\mathrm{d}\lambda(y) \tag{12.1.1.11}
$$

for $\mu_G$-almost all $x\in G$, and the rightmost side of (12.1.1.11) reads $J_f(TJ_f^{-1}(\phi))$.

Since $f$ is continuous, as is $1/f$, then by Corollary A.5.4.3 we may rename $\psi_{m,r}$ as $\phi_{m,r}$, and assume $f = 1$ identically over $G$. We are reduced to the case $\lambda = \mu_G$.

We now proceed as in the proof of [Bris-a, Thm.3.1, p.1185]. Since $T$ is nuclear and $\mathrm{Trace}(P_mTP_m)\to\mathrm{Trace}(T)$ by Proposition C.3.6.5, we deduce that for $\mu_G$-almost all $x\in G$, the sequence of finite sums:

$$
\sum_{1\le m\le N}\sigma_m(T)\sum_{1\le r\le N_m}|\phi_{m,r}(x)|^2 \tag{12.1.1.12}
$$

converges as $N\to +\infty$. Upon replacing the classical Hardy-Littlewood Maximal Theorem in $\mathbf R^n$ with Theorem A.5.3.7, using the Maximal function $M(\cdot)$ defined in (A.5.3.16), and applying the Theorem for $p = 2$ (i.e.

## PDF page 501

**12.1. SMOOTHENINGS ALONG THE DIAGONAL** · **501**

using the strong $(2,2)$ inequality from (A.5.3.18)), the argument for (1) is now identical to that provided in [Bris-a, pp.1185-1186] for [Bris-a, Thm.3.1], using the Differentiation Theorem of Lebesgue in its form from Theorem A.5.4.1 so as to find the set $Y$ in loc.cit. with $\mu_G(G-Y) = 0$ to carry out the rest of the argument.

(2) : We first assume $\rho\in C_c(G)$. Since $\rho(x)k(x,y)$ is a representative function for the Hilbert-Schmidt kernel of $M_\rho\circ T$ on $L^2(G,\lambda)$, and $\widetilde{k}(x,y)$ equals $k(x,y)$ on $(\mu_G\otimes\mu_G)$-almost every point, we have $k(x,y) = \widetilde{k}(x,y)$ also $(\lambda\otimes\lambda)$-almost everywhere, since $\lambda$ and $\mu_G$ have the same null sets (indeed, both $\lambda$ and $\mu_G$ are $\sigma$-finite Radon measures on $G$ since $G$ is second countable, and $f$ is the Radon-Nikodym derivative of $\lambda$ with respect to $\mu_G$. Since it is nowhere vanishing, $\lambda$ and $\mu_G$ are equivalent: a subset $A\subset G$ is $\mu_G$-measurable if and only if it is $\lambda$-measurable, and $\mu_G(A) = \int_A f(x)\,\mu_G(x) = 0$ if and only if $1_A(x)f(x) = 0$ for $\mu_G$-almost all $x\in A$, which forces $\mu_G(A) = 0$).

It follows that we have

$$
\rho(x)\int_G \widetilde{k}(x,y)\phi(y)\,\mathrm{d}\lambda(y) = \rho(x)\int_G k(x,y)\phi(y)\,\mathrm{d}\lambda(y) = (M_\rho\circ T\phi)(x)
$$

for $\lambda$-almost all $x\in G$, which shows that $\rho(x)\widetilde{k}(x,y)$ is another representative function for the Hilbert-Schmidt kernel of $M_\rho\circ T$. We write $k_\rho(x,y) := \rho(x)k(x,y)$, and compute $\widetilde{k}_\rho(x,y)$. Upon showing that we have, for $\mu_G$-almost all $x\in G$, $\widetilde{k}_\rho(x,x) = \rho(x)\widetilde{k}(x,x)$, then the same identity holds for $\lambda$-almost all $x\in G$, and then (12.1.1.3) follows from (12.1.1.2) of (1).

We have, for $(\mu_G\otimes\mu_G)$-almost every $(x,y)\in G$ (in fact, for any regular point $(x,y)\in G\times G$ for $k$):

$$
\widetilde{k}_\rho(x,y) = \lim_{k\to +\infty}\frac{1}{\mu_G(U_k)^2}\int_{xU_k\times yU_k}\rho(x')k'(x',y')\,\mathrm{d}(\mu_G\otimes\mu_G)(x',y') = \rho(x)\widetilde{k}(x,y) \tag{12.1.1.13}
$$

using Lemma A.5.2.5(1) to deduce that $\{U_k\times U_k\}_{k\ge 0}$ is a $D'$-sequence for $G\times G$. Indeed, by Corollary A.5.4.3, the limit in (12.1.1.13) exists and is finite exactly at the points at which the limit of the sequence $\{\mu_G(U_k)^{-2}\int_{xU_k\times yU_k}k'(x',y')\,\mathrm{d}(\mu_G\otimes\mu_G)(x',y')\}_{k\ge 0}$ does, and its value is $\rho(x)\widetilde{k}(x,y)$.

Let $\rho\in L^\infty(G,\lambda)$ be arbitrary, and by [Fol, Thm.2.10(b)], we choose a sequence $\{\rho_m\}_{m\ge 0}\subset A(G)$, the $\mathbf C$-algebra of simple functions on $G$ with complex coefficients, such that $\rho_m\to\rho$ in $L^\infty(G,\lambda)$. Then $M_{\rho_m}\to M_\rho$ with respect to the strong operator topology on $\mathscr{L}(L^2(G,\lambda))$ (in fact, with respect to the operator-norm topology, by [Cnw-a, Ch.II, §1, Thm.1.5, p.28]), and hence $M_{\rho_m}\circ T\to M_\rho\circ T$ in $S_p(L^2(G,\lambda))$ for $p = 1,2$ by Lemma C.3.4.4.

We may therefore assume $\rho = 1_E$ for $E$ a $\lambda$-measurable subset of $G$. We now let $\{K_n\}_{n\ge 0}$ be an exhaustion by compact subsets of $G$, and call $E_n := E\cap K_n$. Then $1_{E_n}\to 1_E$ pointwise $\lambda$-almost everywhere, and hence so does $1_{E_n}(x)\widetilde{k}(x,x)$. It follows that $M_{1_{E_n}}\to M_{1_E}$ as $n\to +\infty$ with respect to the strong operator topology on $\mathscr{L}(L^2(G,\lambda))$, and by Lemma C.3.4.4 we have $M_{1_{E_n}}\circ T\to M_{1_E}\circ T$ in $S_p(L^2(G,\lambda))$ for $p = 1,2$.

By Dominated Convergence, we may assume $\rho = 1_{E_n}$, the indicator function of a $\lambda$-measurable subset of $G$ of finite $\lambda$-measure. There now exists a sequence $\{\rho_m\}_{m\ge 0}\subset C_c(G)$ such that $\rho_m$ is real valued, nonnegative and bounded above by $1$ for every integer $m\ge 0$, and $\rho_m\to\rho$ pointwise $\lambda$-almost everywhere, and in fact in $L^p(G,\lambda)$ for every (finite) $p\ge 1$.

By the foregoing, we have:

$$
\int_G \rho_m(x)\widetilde{k}(x,x)\,\mathrm{d}\lambda(x) = \mathrm{Trace}(M_{\rho_m}\circ T) \tag{12.1.1.14}
$$

for every integer $m\ge 0$, and since $\widetilde{k}$ is $\lambda$-absolutely integrable over $G$, we have:

$$
\int_G \rho_m(x)\widetilde{k}(x,x)\,\mathrm{d}\lambda(x)\to\int_G \rho(x)\widetilde{k}(x,x)\,\mathrm{d}\lambda(x) \tag{12.1.1.15}
$$

as $m\to +\infty$, by Dominated Convergence.

We deduce that (12.1.1.3) holds.

## PDF page 502

**502** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

(3) : Since $S_2(L^2(G,\lambda))$ is isometrically isomorphic to $L^2(G\times G,\lambda\otimes\lambda)$, the isometry sending $T_m$ to the class of $k_m$ and $T$ to the class of $k$, we deduce that $T_m\to T$ implies (and is implied by) $k_m\to k$ in $L^2(G\times G,\lambda\otimes\lambda)$, and since, $(\lambda\otimes\lambda)$-almost everywhere on $G\times G$, we have $k_m = \widetilde{k}_m$ and $k = \widetilde{k}$, we deduce that we have $\widetilde{k}_m\to\widetilde{k}$ in $L^2(G\times G,\lambda\otimes\lambda)$.

We let $\rho\in L^\infty(G,\lambda)$ be a $\lambda$-essentially bounded, equivalently $\mu_G$-essentially bounded, measurable complex valued function on $G$, and $M_\rho\in \mathscr{L}_\beta(L^2(G,\lambda))$ the resulting multiplication operator.

By Lemma C.3.4.4, $M_\rho\circ T_m\to M_\rho\circ T$ in $S_p(L^2(G,\lambda))$ for $p = 1,2$, and by (2), we deduce from (12.1.1.3) that we have, as $m\to +\infty$:

$$
\int_G \rho(x)\widetilde{k}_m(x,x)\,\mathrm{d}\lambda(x) = \mathrm{Trace}(M_\rho\circ T_m)\to\mathrm{Trace}(M_\rho\circ T) = \int_G \rho(x)\widetilde{k}(x,x)\,\mathrm{d}\lambda(x). \tag{12.1.1.16}
$$

This means that $\widetilde{k}_m(x,x)\to\widetilde{k}(x,x)$ weakly in $L^1(G,\lambda)$.

(4) : We call $P_N\colon L^2(G,\lambda)\to L^2(G,\lambda)$ the $N$th basis projector:

$$
P_N := \sum_{0\le m\le N}\langle\theta_m,\cdot\rangle_\lambda\,\phi_m \tag{12.1.1.17}
$$

and observe that we have, upon defining $T_N := P_N\circ T$:

$$
T_N(\phi)(x) = \int_G k_N(x,y)\phi(y)\,\mathrm{d}\lambda(y) \tag{12.1.1.18}
$$

for $\lambda$-almost all $x\in G$. Indeed, we have:

$$
T_N(\phi)(x) = \sum_{0\le m\le N}\langle\theta_m,T\phi\rangle_\lambda\,\phi_m(x) = \sum_{0\le m\le N}\langle T'\theta_m,\phi\rangle_\lambda\,\phi_m = \sum_{0\le m\le N}\int_G (T'\theta_m)(y)\phi(y)\,\mathrm{d}\lambda(y)\,\phi_m(x) \tag{12.1.1.19}
$$

for $\lambda$-almost all $x\in G$. We deduce that (12.1.1.18) holds.

Since $\{\phi_m\}_{m\ge 0}$ is a simple, normalized Schauder basis, then $\{P_N\}_{N\ge 0}\subset \mathscr{L}_\beta(L^2(G,\lambda))$ is a bounded subset, and $P_N\to\mathrm{Id}$ with respect to the strong operator topology. By Proposition C.3.6.5, $T_N\to T$ in $S_p(L^2(G,\lambda))$ for $p = 1,2$. (4) therefore follows from (3).

$\square$

By Theorem A.5.4.1, $\widetilde{\phi}$ agrees with $\phi$ on a $\mu_G$-measurable subset $\mathcal{L}_\phi$ of $G$ whose complement is $\mu_G$-negligible. $\mathcal{L}_\phi$ is termed the Lebesgue set of $\phi$ (see Remark A.5.4.2). By Theorem A.5.4.1(2), the subset of $G$ of the points of continuity of $\phi$ (i.e. those points $x\in G$ such that there exists a neighborhood $V\subset G$ of $x$ in $G$ such that $\phi|_V$ is continuous) is included in $\mathcal{L}_\phi$.

The set of points of $G$ at which the limit in (12.1.1.1) defining the smoothening of a locally $\mu_G$-integrable function $\phi$ exists, may be larger than the Lebesgue set $\mathcal{L}_\phi$. We will be applying the smoothening construction to representative functions of the Hilbert-Schmidt kernel of a nuclear operator on an $L^2$-space of $G$, and while the Lebesgue set of such function may not contain the diagonal of $G\times G$ (which is a null set with respect to the product measure $\mu_G\otimes\mu_G$), the smoothening may still be defined over the diagonal, and it is under the assumptions of Theorem A.5.4.1.

Theorem 12.1.1.3 (Localization along the global diagonal). *Let $F$ be a number field, $a,s,\Lambda$ real numbers, $s\ge 3$ and $a,\Lambda,\varepsilon > 0$. Assume $0 < 1/\Lambda+\varepsilon < \Lambda-\varepsilon$. Let $\varphi\in\mathcal D(C_F)$ be a test function.*

(1) *For $\overline{\mu}$-almost all $x\in C_F$, the point $(x,x)\in C_F\times C_F$ is a regular point for the functions $k^{\mathrm{geom}}_{\varphi,a,s}$, $k^{\mathrm{spec}}_{\varphi,a,s}$. For every $x\in C_F$, $(x,x)\in C_F\times C_F$ is a regular point for the function $\varphi(xy^{-1})$.*

(2) Let $\rho\in\mathcal D(C_F)$ be a $(\Lambda,\varepsilon)$-cutoff. We have:

$$
\mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)) = \int_{C_F}\rho(x)\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)\,\mathrm{d}\overline{\mu}(x) \tag{12.1.1.20}
$$

## PDF page 503

**12.1. SMOOTHENINGS ALONG THE DIAGONAL** · **503**

and:

$$
\mathrm{Trace}\,(P^{\mathrm{spec}}_a\circ A(\varphi)) = \int_{C_F}\widetilde{k}^{\mathrm{spec}}_{\varphi,a,s}(x,x)\,\mathrm{d}\overline{\mu}(x). \tag{12.1.1.21}
$$

(3) *Assume $\varphi(1) = 0$. Then $\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)$ is absolutely $\overline{\mu}$-integrable over $C_F$, and we have:*

$$
\lim_{\Lambda\to +\infty,\varepsilon\Lambda = o(1)}\mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)) = \int_{C_F}\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)\,\mathrm{d}\overline{\mu}(x). \tag{12.1.1.22}
$$

Proof. (1) : By Theorem 12.1.1.2, Theorem 10.4.3.4 and Theorem 10.4.2.1, $\overline{\mu}$-almost all points of the diagonal in $C_F\times C_F$ is a regular point for $k^{\mathrm{spec}}_{\varphi,a,s}$. Since $\varphi(xy^{-1})$ is continuous over $C_F\times C_F$, by Theorem A.5.4.1(2) every point of $C_F\times C_F$ is a regular point, and hence $\overline{\mu}$-almost all points of the diagonal in $C_F\times C_F$ is regular for $k^{\mathrm{geom}}_{\varphi,a,s} = \varphi(xy^{-1})-k^{\mathrm{spec}}_{\varphi,a,s}$.

(2) : By Theorem 12.1.1.2(1) and Theorem 10.4.3.4, $\widetilde{k}^{\mathrm{spec}}_{\varphi,a,s}$ is a representative function for the Hilbert-Schmidt kernel of $P^{\mathrm{spec}}_a\circ A(\varphi)$, since $k^{\mathrm{spec}}_{\varphi,a,s}$.

Since $\rho$ is continuous, so is $\rho(x)\varphi(xy^{-1})$ as a function on $C_F\times C_F$, and hence, by Theorem 10.4.3.4, $\rho(x)\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}$ and $\rho(x)\widetilde{k}^{\mathrm{spec}}_{\varphi,a,s}$ are representative functions for the Hilbert-Schmidt kernels of $P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)$ and $P^{\mathrm{spec}}_{\rho,a}\circ A(\varphi)$, respectively.

By (12.1.1.2) from Theorem 12.1.1.2, (12.1.1.20) and (12.1.1.21) hold.

(3) : The function $\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)$ is the sum of two measurable functions of $x\in C_F$, and it is, as such, measurable. If $\varphi(1) = 0$, then we have:

$$
\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x) = -\widetilde{k}^{\mathrm{spec}}_{\varphi,a,s}(x,x) \tag{12.1.1.23}
$$

and by Theorem 10.4.3.1(4), the rightmost side of (12.1.1.23) is absolutely $\overline{\mu}$-integrable.

Since $\rho\to 1$ as $\Lambda\to +\infty$ in the regime $\varepsilon\Lambda = o(1)$, as continuous uniformly bounded (by $1$) functions on $C_F$, then $\rho(x)\,\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)\to\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)$ pointwise $\overline{\mu}$-almost everywhere over $C_F$. Since $|\rho(x)\,\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)|\le |\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)|$ for $\overline{\mu}$-almost all $x\in C_F$, by Dominated Convergence we deduce that we have:

$$
\lim_{\Lambda\to +\infty,\varepsilon\Lambda = o(1)}\int_{C_F}\rho(x)\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)\,\mathrm{d}\overline{\mu}(x) = \int_{C_F}\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)\,\mathrm{d}\overline{\mu}(x). \tag{12.1.1.24}
$$

By (10.4.3.32) and Theorem 12.1.1.2(1), the leftmost side of (12.1.1.24) equals

$$
\lim_{\Lambda\to +\infty,\varepsilon\Lambda = o(1)}\mathrm{Trace}\,(P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi))
$$

and so (10.4.3.31) holds.

$\square$

Remark 12.1.1.4. We note that, if $\varphi(1) = 0$, then, by Theorem 10.4.3.4(4), $\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,x)$ is absolutely $\overline{\mu}$-integrable, but this does not make the operator $P^{\mathrm{geom}}_a\circ A(\varphi)$ nuclear, since $(1+|\log|\cdot|_F|^2)^{-s/2}\,k^{\mathrm{spec}}_{\varphi,a,s}(x,y)$, while measurable over $C_F\times C_F$, is not square-integrable with respect to $((1+|\log|\cdot|_F|^2)^{s/2}\overline{\mu})^{\otimes 2}$.

As such, the induced integral operator is not Hilbert-Schmidt, and hence it cannot be nuclear.

The regular representation of $C_F$ on $W^{s,2}(C_F)$ induces operators $A(\varphi)$ that are not nuclear nor Hilbert-Schmidt, even in the special case $\varphi(1) = 0$. Responsible for this is the non-compactness of the idele class group.

This leads to the necessity of truncating $C_F$ into growing compact subsets with non-empty interior, i.e. $C^{[1/\Lambda,\Lambda]}_F$, since the resulting kernel functions $1_{[1/\Lambda,\Lambda]}(x)\,k^{\mathrm{geom}}_{\varphi,a,s}(x,y)$ are indeed the kernels of nuclear operators.

The aim is to use the truncated kernel functions $1_{[1/\Lambda,\Lambda]}(x)\,k^{\mathrm{geom}}_{\varphi,a,s}(x,y)$ and their operator-theoretic interpretation, to compute the integral of $k^{\mathrm{geom}}_{\varphi,a,s}(x,y)$ itself along the diagonal, by approximation.

We will be using the smoothened kernels $\rho(x)\,\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,y)$, with $\rho$ a $(\Lambda,\varepsilon)$-cutoff in the sense of Definition 9.3.3.1, with a view towards the main trace calculation. Passage from $1_{[1/\Lambda,\Lambda]}(x)\,k^{\mathrm{geom}}_{\varphi,a,s}(x,y)$ to $\rho(x)\,\widetilde{k}^{\mathrm{geom}}_{\varphi,a,s}(x,y)$ is harmless for the purposes of computing the value of the integral of $\lim_{\Lambda\to +\infty}\mathrm{Trace}\,(P^{\mathrm{geom}}_a\circ A(\varphi))$, since

## PDF page 504

**504** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

the respective smoothened kernels have masses along the diagonal which are asymptotically equal as we let $\rho\to 1$ (as a consequence of letting $\Lambda\to +\infty$ in the regime $\varepsilon\Lambda=o(1)$).

This is an example of an integral operator $(P^{\mathrm{geom}}_a\circ A(\varphi))$ whose integral kernel $(k^{\mathrm{geom}}_{\varphi,a,s}(x,y))$ can be made sense of along the diagonal (within $C_F\times C_F$), and is absolutely integrable there, without this being a sufficient condition for nuclearity.

For a simple example of how integrability along the diagonal of a piece-wise continuous integral kernel of an integral Hilbert-Schmidt operator on an $L^2$-space does not ensure nuclearity of the associated integral operator, we further refer the reader to [Bris-b, Example 3.2,p.1186].

12.2. Lebesgue Differentiation along the diagonal

In this section we analyze the Hilbert-Schmidt kernel of $P^{\mathrm{geom}}_{\Lambda,a}\circ A(\varphi)$ and its trace, as $\Lambda\to +\infty$, with the aim of reducing the computation of the limit value of the latter to separate simpler tasks, amounting to trace calculations for component kernels.

We recall that throughout this Chapter, for $(X,\mathcal A,\mu)$ a measure space, we will be assuming $X$ is a Hausdorff locally compact second countable topological space, the $\sigma$-algebra $\mathcal A$ contains the Borel $\sigma$-algebra $\mathcal B(X)$, $\mu$ is a complete positive Radon measure on $\mathcal A$, and, for simplicity, that $\mathcal A$ is the initial $\sigma$-algebra containing $\mathcal B(X)$ and such that $\mu$ is complete on $\mathcal A$. In particular, for any $N\subset X$ such that $\mu(N)=0$, $N$ is measurable.

Recall that any Radon measure on such $X$ is regular (see [Fol, Thm.7.8]).

We will be abbreviating $L^p(X,\mu)$ for $L^p(X,\mathcal A,\mu)$, for every real number $p\ge 1$.

Under these assumptions, for any element $\phi\in L^p(X,\mu)$, there exists a Borel measurable function $\phi_0:X\to\mathbf C$ such that $\phi=\phi_0$ away from a subset $N$ of $X$ such that $\mu(N)=0$.

Any element in $L^p(X,\mu)$ is, recall, an equivalence class of Lebesgue measurable functions on $X$, the equivalence relation being equality away from $\mu$-null subsets of $X$.

In light of [Fol, Prop.7.9], $L^p(X,\mu)$ is also obtained as the norm-completion of $C_c(X)$ with respect to the seminormed topology induced by the $L^p$-seminorm (in fact a norm) on $C_c(X)$, i.e. $||f||_p:=\left(\int_X|f(x)|^p\,\mathrm{d}\mu(x)\right)^{1/p}$.

Both perspectives on the elements of $L^p(X,\mu)$ will be used below.

In light of [Fol, Prop.7.1] (see also [Bou-I, Ch.III,§1,n.3,(4),INT III.7]; see also [Bou-I, Ch.III,§1,n.5,Thm.1,INT III.12]) and [Fol, Thm.7.2], under the assumptions being made on $X$, the approaches to measure theory and integration contained in [Bou-I, Bou-II] and from classical measure theory (see [Fol, Ch.1,§1.3] and [Fol, Ch.7], and the related literature referred to throughout this work) are equivalent.

12.2.1. Indentations. In this section we provide the instruments to construct a kernel function:

$$
K^{\mathrm{geom}}_{\varphi,a,s}:\mathrm{GL}_1(\mathbf A_F)\times\mathrm{GL}_1(\mathbf A_F)\to\mathbf C \tag{12.2.1.1}
$$

that "lifts" the integral kernel $k^{\mathrm{geom}}_{\varphi,a,s}$ of the continuous linear operator $A(\varphi)$ on $W^{s,2}_a\mathrm H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))$, for then deconstructing it into an $S$-local part and an error term, which we are both piece-wise going to interpret as operators (on other Hilbert spaces, each, respectively).

We begin by recording a construction from [Bou-II, Ch.VII,§2,n.4,Prop.8,INT VII.37], and we discuss some consequences and complements.

LEMMA 12.2.1.1. *Let $G$ be a second countable Hausdorff locally compact abelian group, $H\subset G$ a closed subgroup, $\mu_H$ a choice of Haar measure on $H$.*

*We denote by $\pi:G\to G/H$ the continuous quotient homomorphism. There exists a function $u_0:G\to\mathbf C$ satisfying the following conditions:*

*(1) $u_0$ is continuous, real-valued and nonnegative.*

*(2) Let $K$ be an arbitrary compact subset of $G$. Then the intersection of the support of $u_0$ with $\pi^{-1}(\pi(K))$ is compact.*

## PDF page 505

**12.2. LEBESGUE DIFFERENTIATION ALONG THE DIAGONAL** · **505**

*(3) For all $x\in G$, the integral:*

$$
\int_H u_0(h^{-1}x)\,\mathrm{d}\mu_H(h) \tag{12.2.1.2}
$$

*converges, and upon denoting $u^H_0$ its value function on $G$, we have that $u^H_0$ is continuous on $G$, invariant under the continuous left-translation action by $H$ on $G$, and identically $1$ as a function on $G/H$.*

*For every continuous function $u\in C(G/H)$, we have that for all $x\in G$, the integral*

$$
\int_H (u_0\cdot (u\circ\pi))(h^{-1}x)\,\mathrm{d}\mu_H(h) \tag{12.2.1.3}
$$

*converges, and its value is $u(\pi(x))$.*

PROOF. (1) : Since $G$ is second countable and $H\subset G$ is closed, $\pi$ is open and $G/H$ is Hausdorff locally compact, and hence second countable. As such, it is paracompact. We choose a locally finite countable open cover $\{U_k\}_{k\ge 0}$ of $G/H$, and consider the induced open cover $\{\pi^{-1}U_k\}_{k\ge 0}$ on $G$, also locally finite. We choose a partition of unity $\{\rho_k\}_{k\ge 0}$ on $G/H$ subordinate to $\{U_k\}_{k\ge 0}$, calling $S_k\subset U_k$ the compact support of $\rho_k$ for each integer $k\ge 0$.

For each integer $k\ge 0$, there exists, by [DE, Lemma 1.5.1], a continuous compactly supported function $\rho'_k$ on $G$ whose support $S'_k$ satisfies $S'_k\subset \pi^{-1}(U_k)$, and $S_k\subset \pi(S'_k)$ (this last containment follows from the proof of [DE, Lemma 1.5.1]).

The sum $f:=\sum_{k\ge 0}\rho'_k$ converges pointwise on $G$ to a continuous real-valued nonnegative function that is not identically zero on any orbit of the continuous left-translation action of $H$ on $G$. Indeed, since $\{U_k\}_{k\ge 0}$ is locally finite, for each $x\in G$ there exists an open neighborhood $U_x$ of $x$ in $G$ that intersects non-trivially at most a finite number of the $U_k$'s, say $U_{k_1},\ldots,U_{k_N}$, and hence for every $y\in U_x$ we have $\rho'_k(x)\ne 0$ only if $k\in\{k_1,\ldots,k_N\}$. Over $U_x$, the sum defining $f$ is therefore finite.

We consider $f^H$ the function on $G$ defined, for each $x\in G$, by the integral:

$$
f^H(x):=\int_H f(h^{-1}x)\,\mathrm{d}\mu_H(h). \tag{12.2.1.4}
$$

Let $K_0$ be an arbitrary compact subset of $G$. The intersection of the support $K$ of $f$ with $\pi^{-1}(\pi(K_0))$ is contained in $K\cap\bigcup_{1\le i\le N} \pi^{-1}(\pi(S'_{k_i}))$ where $k_1,\ldots,k_N$ are the finitely many integers such that the compact subset $\pi(K_0)$ of $G/H$ intersects $\pi(S'_k)$ non-trivially. Indeed, there exist only finitely many such integers, for $\pi(K_0)$ intersects $U_k$, and hence $\pi(S'_k)\subset U_k$, non-trivially for at most finitely many integers $k$.

Since $K\cap\bigcup_{1\le i\le N} \pi^{-1}(\pi(S'_{k_i}))\subset\bigcup_{1\le i\le N}S'_{k_i}$, a compact subset, we deduce that the intersection of the support of $f$ with $\pi^{-1}(\pi(K_0))$ is compact, for the arbitrary compact subset $K_0\subset G$. The assumptions of [Bou-II, Ch.VII,§2,n.1,Prop.1(a),(b),INT VII.27] (applied to $\chi=1$) are therefore satisfied by $f$, and the integral defining $f^H$ converges to a continuous function on $G$, invariant under the continuous left-translation action by $H$.

We define $u_0:=f/f^H$. The function $u_0$ satisfies (1), (2) and (3). Since, for any $u\in C(G/H)$, the continuous function $u\circ\pi$ is invariant under the continuous left-translation action of $H$ on $G$, then the integral in (12.2.1.4) indeed converges to a continuous function on $G$ by [Bou-II, Ch.VII,§2,n.1,Prop.1(a),(b),INT VII.27] (applied for $\chi=1$), and its value is $u(\pi(x))\int_H u_0(h^{-1}x)\,\mathrm{d}\mu_H(h)=u(\pi(x))$.

We further refer the reader to the proof of [Bou-II, Ch.VII,§2,n.4,Corollary,INT VII.38]. $\square$

Let $G$ be a second countable Hausdorff locally compact abelian group, $H\subset G$ a closed subgroup, $\mu_H$ a choice of Haar measure on $H$. We denote by $\pi:G\to G/H$ the continuous quotient homomorphism.

We denote by:

$$
\Phi_H:C_c(G)\to C_c(G/H) \tag{12.2.1.5}
$$

## PDF page 506

**506** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

the linear operator sending $u\in C_c(G)$ to $\Phi_H(u)(x):=\int_H u(h^{-1}x)\,\mathrm{d}\mu_H(h)$, a continuous function of $x\in G$, invariant under the continuous left-translation action by $H$ on $G$, inducing a unique continuous function denoted again by $\Phi_H(u)$ on $G/H$, whose support is, therefore, compact (being contained in the image under $\pi$ of $\pi^{-1}(\pi(K))$, for $K$ the support of $u$, and such image is $\pi(K)$, compact).

COROLLARY 12.2.1.2. *Let $G$ be a second countable Hausdorff locally compact abelian group, $H\subset G$ a closed subgroup, $\mu_H$ a choice of Haar measure on $H$. We denote by $\pi:G\to G/H$ the continuous quotient homomorphism.*

*Let $\lambda$ be a positive Radon measure on $G/H$.*

*(1) There exists a unique positive measure $\lambda'$ on $G$ satisfying the following normalization condition:*

$$
\int_{G/H}\Phi_H(u)(x)\,\mathrm{d}\lambda(x)=\int_G u(g)\,\mathrm{d}\lambda'(g) \tag{12.2.1.6}
$$

*for all $u\in C_c(G)$. $\lambda'$ is $H$-invariant.*

*(2) The linear operator $\Phi_H$ from (12.2.1.5) extends by continuity to a continuous surjective operator:*

$$
\Phi_H:L^1(G,\lambda')\to L^1(G/H,\lambda). \tag{12.2.1.7}
$$

*The assignment*

$$
\Psi_{u_0}:u\mapsto u_0\cdot (u\circ\pi) \tag{12.2.1.8}
$$

*for a choice of function $u_0$ as provided by Lemma 12.2.1.1, is an isometric right-inverse $\Psi_{u_0}:L^1(G/H,\lambda)\to L^1(G,\lambda')$ to $\Phi_H$.*

PROOF. (1) : This is [Bou-II, Ch.VII,§2,n.2,Prop.4,INT VII.31], applied to $X=G$, $\lambda'=\lambda^\sharp$, in which case the measure $\lambda'$ is indeed $H$-invariant. [Bou-II, Ch.VII,§2,n.2,Prop.4,INT VII.31] provides a measure $\lambda'$, i.e. a continuous linear form on $C_c(G)$, where $C_c(G)$ is equipped with the locally convex inductive limit topology induced by the inclusions $C(G,K)\subset C_c(G)$, as $K\subset G$ ranges over all non-empty compact subsets, and $C(G,K)$ is the linear subspace of continuous functions on $G$ compactly supported within $K$, endowed with the topology of uniform convergence.

$\lambda'$ is a positive functional on $C_c(G)$ (i.e. forgetting its continuity), and by [Fol, Prop.7.1] its positivity and linearity only imply its continuity on $C_c(G)$ with respect to its locally convex inductive limit topology, by [Bou-I, Ch.III,§1,n.3,(4),INT III.7] (see also [Bou-I, Ch.III,§1,n.5,Thm.1,INT III.12]). By [Fol, Thm.7.2], $\lambda'$ corresponds to a unique Radon measure on $G$ in the sense of classical measure theory (see [Fol, Ch.1,§1.3] and [Fol, Ch.7]), which we again denote by $\lambda'$.

By [Bou-I, Ch.III,§1,n.8,INT III.16], it is enough to show that there exists a real number $M\ge 0$ such that for any $u\in C_c(G)$, we have $|\lambda'(u)|\le M||u||_u$.

(2) : If $u\in C_c(G)$, then so is $|u|$, and since $|\Phi_H(u)|\le\Phi_H(|u|)$ as continuous functions on $G/H$, we deduce from (12.2.1.6) that $\Phi_H$ is continuous with respect to the normed topology on $C_c(G)$ induced by the $L^1(G,\lambda')$-norm on the source, and the normed topology on $C_c(G/H)$ induced by the $L^1(G/H,\lambda)$-norm on the target. This provides the continuous extension of $\Phi_H$ in (12.2.1.7).

The assignment of $\Psi_{u_0}$ on compactly supported continuous functions on $G/H$ is isometric with respect to the $L^1$-norm topologies on source and target by (12.2.1.6) and Lemma 12.2.1.1. It therefore extends by continuity to an isometric embedding $L^1(G/H,\lambda)\to L^1(G,\lambda')$, since $C_c(G/H)\subset L^1(G/H,\lambda)$ is norm-dense by [Fol, Prop.7.9]. The right-inverse condition holds because it holds on compactly supported continuous functions by Lemma 12.2.1.1. $\square$

DEFINITION 12.2.1.3. We let $G$ be a second countable Hausdorff locally compact abelian group, $H\subset G$ a closed subgroup, $\mu_H$ a choice of Haar measure on $H$. We define an $H$-indentation on $G$ to be a continuous real-valued function $u_0:G\to\mathbf R_{\ge 0}$ satisfying the conditions in Lemma 12.2.1.1.

## PDF page 507

**12.2. LEBESGUE DIFFERENTIATION ALONG THE DIAGONAL** · **507**

For any positive Radon measure $\lambda$ on $G/H$, we denote by $\Psi_{u_0}:L^1(G/H,\lambda)\to L^1(G,\lambda')$ the continuous right section to $\Phi_H$ provided by Corollary 12.2.1.2.

We recall the following general situation and related terminology:

REMARK 12.2.1.4. We let $X$ be a Hausdorff locally compact topological space, $G$ a Hausdorff locally compact abelian group. Assume consider a continuous action:

$$
\theta:G\times X\to X \tag{12.2.1.9}
$$

We assume that the action $\theta$ of $G$ on $X$ is proper, by which we mean, following [Bou-GT, Ch.III,§4,n.1,Def.1,p.250], that the continuous map:

$$G\times X\to X\times X$$

sending $(g,x)$ to $(x,\theta(g,x))$, is proper (see [Bou-GT, Ch.I,§10,n.1,Def.1,p.97]).

By [Bou-GT, Ch.III,§4,n.2,Prop.3,p.253], the quotient space $X/G$ is Hausdorff.

If the action $\theta$ of $G$ on $X$ is, in addition, free, then, by [Bou-GT, Ch.III,§4,n.4,Corollary,p.257] to [Bou-GT, Ch.III,§4,n.4,Prop.8,256], the quotient map:

$$
\pi:X\to X/G \tag{12.2.1.10}
$$

is open.

In this case, if $X$ is second countable, so is $X/G$.

We assume two Radon measures given, one, $\mu_X$, on $X$, another, a choice of Haar measure $\mu_G$ on $G$. We assume $\mu_X$ is $G$-invariant, and denote by $\bar\mu$ the unique Radon measure on $X/G$ induced by these choices, so that the following integral formula holds:

$$
\int_X\phi(x)\,\mathrm{d}\mu_X(x)=\int_{X/G}\left(\int_G\phi(\theta(g,x))\,\mathrm{d}\mu_G(g)\right)\mathrm{d}\bar\mu(\pi(x)). \tag{12.2.1.11}
$$

In the special case $X$ is itself a Hausdorff locally compact abelian group, and $G$ is a closed subgroup, with $\theta$ the action by continuous left-translation, the existence and uniqueness of $\bar\mu$, upon choosing $\mu_X$ to be a Haar measure on $X$, is by Theorem D.1.2.1. For the general case, we refer the reader to [Bou-II, Ch.VII,§2,n.2,Prop.4,INT VII.31].

Assume that there exists a non-empty connected subset $D\subset X$ with non-empty interior, such that

$$
\bigcup_{g\in G}\theta(g,D)=X, \tag{12.2.1.12}
$$

$$D\cap\theta(g,D)=\varnothing$$

the last condition being assumed to hold for every $g\in G$ with $g\ne 1$. Assume that for every $g\in G$, with $g\ne 1$, the intersection:

$$
\bar D\cap\theta(g,\bar D) \tag{12.2.1.13}
$$

has $\bar\mu$-measure zero.

We will be referring to such $D$ as a fundamental domain for the continuous $G$-action on $X$.

The above general situation and the respective terminology will be specialized shortly to the cases $X=\mathrm{GL}_1(\mathbf A_F)$, respectively $\mathrm{GL}_1(\mathbf A_{F,S})$, and $G=F^\times$, respectively $G=\mathcal O_{F,S}^\times$.

12.2.2. Regular points on the diagonal and indentations. We need the following "two-variable" complements around $H$-indentations on $G$.

SITUATION 12.2.2.1. Let $G$ be a second countable Hausdorff locally compact abelian group, $H\subset G$ a closed subgroup, $\mu_H$ a choice of Haar measure on $H$.

Assume $H$ is discrete, and $\mu_H$ is normalized so as to have $\mu_H(\{1\})=1$ (i.e. $\mu_H$ is the counting measure, by [DE, Prop.1.4.4(c)]).

## PDF page 508

**508** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

Let $\lambda$ be a positive Radon measure on $G/H$, and $\lambda'$ the unique positive Radon measure on $G$ provided by Corollary 12.2.1.2(1).

We denote by $\pi:G\to G/H$ the continuous quotient homomorphism. Assume there exists a fundamental domain $D$ for the continuous left-translation action by $H$ on $G$.

Assume that $\{U_k\}_{k\ge 0}$ is a $D'$-sequence for $G$ such that $U_k\subset D$, and $U_k$ is a relatively compact open symmetric unit-neighborhood for all integers $k\ge 0$. Then, upon defining $\bar U_k:=\pi(U_k)$ for each integer $k\ge 0$, $\{\bar U_k\}_{k\ge 0}$ is a $D'$-sequence for $G/H$.

We define smoothenings over $G\times G$ and $G/H\times G/H$ using the $D'$-sequences $\{U_k\times U_k\}_{k\ge 0}$ for $G\times G$ and $\{\bar U_k\times\bar U_k\}_{k\ge 0}$ for $G/H\times G/H$.

Let $\lambda$ be a positive Radon measure on $G/H$, and $\lambda'$ the unique positive Radon measure on $G$ provided by Corollary 12.2.1.2(1).

PROPOSITION 12.2.2.2. *Let $G$ be a second countable Hausdorff locally compact abelian group, $H\subset G$ a discrete subgroup. Assume $\mu_G$ is a choice of Haar measure on $G$, $\mu_H$ is the counting measure on $H$, and $\mu_{G/H}$ is the unique Haar measure on $G/H$ determined by $\mu_H$ and $\mu_G$ as per Theorem D.1.2.1.*

*Assume that $G,H$ satisfy the conditions in Situation 12.2.2.1.*

*Let $u_0$ be an $H$-indentation on $G$. Then $u_0\otimes u_0\in C(G)\otimes C(G)\subset C(G\times G)$, a continuous function on $G\times G$, satisfies the following properties:*

*(1) The integral:*

$$
\int_H u_0(h^{-1}x)u_0(h^{-1}y)\,\mathrm{d}\mu_H(h) \tag{12.2.2.1}
$$

*converges pointwise everywhere on $G\times G$. The limit function $u^\Delta_0(x,y)$ is defined everywhere, continuous on $G\times G$, real-valued and nonnegative, and invariant under the continuous diagonal action of $H$ on $G\times G$.*

*(2) For all $\mu_{G/H}$-measurable, locally $\mu_{G/H}$-integrable functions $u:G/H\times G/H\to\mathbf C$, the assignment:*

$$
\Psi^\Delta_{u_0}:u\mapsto u^\Delta_0\cdot (u\circ (\pi\times\pi)) \tag{12.2.2.2}
$$

*is valued in measurable complex-valued functions over $G\times G$.*

*If $\mu_{G/H}$-almost every point $(x,x)\in G/H\times G/H$ is regular for $u$, then $\widetilde u(x,x)$ is $\mu_{G/H}$-measurable, defined $\mu_{G/H}$-almost everywhere. If it is absolutely $\mu_{G/H}$-integrable as a function on $G/H$, then the functions $\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)$ and $\Psi^\Delta_{u_0}(\widetilde u)(x,h^{-1}x)$, defined for all $h\in H$, $\mu_G$-almost all $x\in G$, and $(\mu_H\otimes\mu_G)$-measurable as functions of $(x,h)\in G\times H$, satisfy the following condition: the following two-fold integrals*

$$
\int_D\int_H\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x),\quad \int_H\int_D\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)\,\mathrm{d}\mu_G(x)\,\mathrm{d}\mu_H(h) \tag{12.2.2.3}
$$

*are both absolutely convergent, and the following identities hold:*

$$
\int_{G/H}\widetilde u(x,x)\,\mathrm{d}\mu_{G/H}(x)=\int_D\int_H\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x) \tag{12.2.2.4}
$$

$$
=\int_H\int_D\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)\,\mathrm{d}\mu_G(x)\,\mathrm{d}\mu_H(h) \tag{12.2.2.5}
$$

$$
=\int_H\int_D\Psi^\Delta_{u_0}(\widetilde u)(x,h^{-1}x)\,\mathrm{d}\mu_G(x)\,\mathrm{d}\mu_H(h) \tag{12.2.2.6}
$$

$$
=\int_D\int_H\Psi^\Delta_{u_0}(\widetilde u)(x,h^{-1}x)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x). \tag{12.2.2.7}
$$

*(3) Let $\rho\in C_c(G/H\times G/H)$. Then:*

$$
\Psi^\Delta_{u_0}(\rho\cdot u)(x,y)=(\rho\circ (\pi\times\pi))\cdot\Psi^\Delta_{u_0}(u)(x,y) \tag{12.2.2.8}
$$

*for $(\mu_G\otimes\mu_G)$-almost every $(x,y)\in G\times G$.*

## PDF page 509

**12.2. LEBESGUE DIFFERENTIATION ALONG THE DIAGONAL** · **509**

*(4) We have, for $(\mu_G\otimes\mu_G)$-almost all $(x,y)\in G\times G$:*

$$
\Psi^\Delta_{u_0}(\widetilde u)(x,y)=\lim_{k\to +\infty}\frac{1}{\mu_G(U_k)^2}\int_{xU_k\times yU_k}\Psi^\Delta_{u_0}(u)(y_1,y_2)\,\mathrm{d}(\mu_G\otimes\mu_G)(y_1,y_2). \tag{12.2.2.9}
$$

*The point $(x,y)\in G\times G$ is regular for $\Psi^\Delta_{u_0}(u)$ if and only if $(\pi(x),\pi(y))\in G/H\times G/H$ is regular for $u$.*

REMARK 12.2.2.3. For a complex-valued function $f:X\to\mathbf C$ on a Hausdorff locally compact second countable topological space $X$, and a Radon measure $\mu$ on $X$, Lebesgue measurability for $f$ (upon endowing $X$ with the completion of the Borel $\sigma$-algebra, i.e. with the $\sigma$-algebra of $\mu^*$-measurable sets, promoting $\mu$ to a complete measure; see [Fol, Thm.1.11] and [Bou-I, Ch.IV,§5,n.1,Cor.1,INT IV.60]) and $\mu$-measurability in the sense of [Bou-I, Ch.IV,§5,n.1,Def.2,INT IV.60], are equivalent concepts. $\mu$-measurability of a map $f:X\to T$ for $T$ a Hausdorff locally compact topological space, is defined in [Bou-I, Ch.IV,§5,n.1,Def.1,INT IV.59], and will be used only for $f$ continuous, surjective and open, in which case it holds by [Bou-I, Ch.IV,§5,n.2,Cor.4,INT IV.62].

PROOF. (1) : Since $u_0$ is an $H$-indentation on $G$, then, upon calling $S$ the support of $u_0$ in $G$, for any compact subset $K\subset G$ we have, by Lemma 12.2.1.1(2), that the intersection $S\cap \pi^{-1}(\pi(K))$ is compact.

The function $u_1(x,y):=u_0(x)u_0(y)$ on $G\times G$ is real valued, nonnegative, and continuous. Moreover, its support is contained in $S\times S\subset G\times G$. Let $K$ be a compact subset of $G\times G$. There exists a compact subset $K'\subset G$ such that $K\subset K'\times K'$. Indeed, we define $K_1$, respectively $K_2$, to be the image of $K$ in $G$ under the first projection, respectively the second projection. Then $K\subset K_1\times K_2$, and upon defining $K':=K_1\cup K_2$, we have $K\subset K'\times K'$.

The intersection:

$$
(S\times S)\cap\{(x,y)\in G\times G:(hx,hy)\in K\text{ for some }h\in H\}=(S\times S)\cap\bigcup_{h\in H}(h,h).K \tag{12.2.2.10}
$$

is therefore compact, since the rightmost side in (12.2.2.10) is contained within:

$$
(S\times S)\cap(\pi^{-1}(\pi(K'))\times \pi^{-1}(\pi(K')))\subset (S\cap \pi^{-1}(\pi(K')))\times (S\cap \pi^{-1}(\pi(K'))) \tag{12.2.2.11}
$$

and since $S\cap \pi^{-1}(\pi(K'))$ is compact, so is the intersection in (12.2.2.10).

The integral in (12.2.2.1) therefore converges by [Bou-II, Ch.VII,§2,n.1,Prop.1(a),INT VII.27] for every $(x,y)\in G\times G$, defining the function $u^\Delta_0(x,y)$ everywhere over $G\times G$. By [Bou-II, Ch.VII,§2,n.1,Prop.1(b),INT VII.27], $u^\Delta_0$ is continuous over $G\times G$ and invariant under the continuous diagonal action of $H$ on $G\times G$. It is real valued and nonnegative, since $u_0$ is.

(2) : For every $(\mu_{G/H}\otimes\mu_{G/H})$-measurable complex-valued function $u:G/H\times G/H$, we have that the composition $u\circ (\pi\times\pi)$ is also $(\mu_G\otimes\mu_G)$measurable, as a function on $G\times G$, by [Bou-II, Ch.VII,§2,n.3,Prop.6(b),INT VII.34]. We note that $u$ may not be everywhere defined over $G/H\times G/H$.

By [Bou-II, Ch.VII,§2,n.3,Prop.6(a),INT VII.33], the pre-image under $\pi\times\pi$ of a $(\mu_{G/H}\otimes\mu_{G/H})$-negligible subset is $(\mu_G\otimes\mu_G)$-negligible, and hence $u\circ (\pi\times\pi)$ is defined $(\mu_G\otimes\mu_G)$-almost everywhere.

By the same token, since $\widetilde u(x,x)$ is $\mu_{G/H}$-measurable as a function of $x\in G/H$, which is the case by Theorem A.5.4.1(2), being $\{A_{\bar U_k\times\bar U_k}(u)(x,x)\}_{k\ge 0}$ a sequence of (uniformly) continuous functions on $G/H\times G/H$ by Theorem A.5.4.1(1), then $u(\pi(x),\pi(x))$ is $\mu_G$-measurable as a function on $G$.

Indeed, since $G$ is Hausdorff and $H\subset G$ is a closed subgroup, the diagonal maps $\delta_G:G\to G\times G$ and $\delta_{G/H}:G/H\to G/H\times G/H$ are homeomorphisms onto their closed images, and since $\widetilde u(x,x)=\widetilde u\circ \delta_{G/H}$ is $\mu_{G/H}$-measurable on $G/H$, its pre-composition with $\pi:G\to G/H$ is $\mu_G$-measurable on $G$ by [Bou-II, Ch.VII,§2,n.3,Prop.6(b),INT VII.34].

Pre-composition of $\widetilde u\circ \delta_{G/H}\circ \pi$ with $\delta_G^{-1}$ gives, set-theoretically at every point $(x',x')\in G\times G$ such that $(\pi(x'),\pi(x'))$ is a point of definition of $\widetilde u$, i.e. a regular point for $u$ on $G/H\times G/H$, $\widetilde u\circ (\pi\times\pi)$, and this latter function is $(\delta_G)_*\mu_G$-measurable since $\delta_G$ is a homeomorphism onto its image. Note that the function

## PDF page 510

**510** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

$\widetilde u\circ \delta_{G/H}\circ \pi$ is defined $\mu_G$-almost everywhere by [Bou-II, Ch.VII,§2,No.3,Prop.6(a),INT VII.33] (see also [Bou-I, Ch.V,§6,No.6,Cor.1(a),INT V.72]), i.e. the pre-image under $\pi$ of the set of points of $G/H$ at which $\widetilde u\circ \delta_{G/H}$ is undefined, a $\mu_{G/H}$-null set, is locally $\mu_G$-negligible in $G$, and since $G$ is second countable, it is $\mu_G$-negligible (see Lemma A.5.3.3).

We will be omitting mention of $\delta_G$ and $\delta_{G/H}$ from the notation.

Since $u^\Delta_0$ is continuous as a function on $G\times G$, it is $(\mu_G\otimes\mu_G)$-measurable and $u^\Delta_0(h^{-1}x,x)$ and $u^\Delta_0(x,h^{-1}x)$ are both $(\mu_G\otimes\mu_H)$-measurable as functions of $(x,h)\in D\times H$. Finite products of measurable functions are measurable, since finite intersections of measurable subsets are measurable.

The measurability assertions in (2) therefore all hold, and all the integrals in (12.2.2.3) and (12.2.2.4) make sense, allowed to possibly be divergent.

We now prove that (12.2.2.3) holds.

We have:

$$
\int_D\int_H\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x)=\int_D\int_H u^\Delta_0(h^{-1}x,x)\cdot\widetilde u(\pi(x),\pi(x))\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x) \tag{12.2.2.12}
$$

$$
=\int_D\int_{h\in H}\int_{h'\in H}u_0(h^{-1}(h')^{-1}x)u_0((h')^{-1}x)\widetilde u(\pi(x),\pi(x))\,\mathrm{d}\mu_H(h')\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x) \tag{12.2.2.13}
$$

$$
=\int_D\int_{(h,h')\in H\times H}u_0(h^{-1}(h')^{-1}x)u_0((h')^{-1}x)\widetilde u(\pi(x),\pi(x))\,\mathrm{d}\mu_{H\times H}(h,h')\,\mathrm{d}\mu_G(x) \tag{12.2.2.14}
$$

where $\mu_{H\times H}:=\mu_H\otimes\mu_H$ (note that we are choosing $\mu_{H\times H}$ to be $\mu_H\otimes\mu_H$, likewise as we are choosing $\mu_G\otimes\mu_G$ to be the Haar measure on $G\times G$, so as to also have $\mu_{G/H}\otimes\mu_{G/H}$ as the Haar measure on $G/H$ uniquely determined as per Theorem D.1.2.1. We require the latter two be the Haar measures on $G/H\times G/H$, respectively $G\times G$, so as to use the $D'$-sequences $\{\bar U_k\times\bar U_k\}_{k\ge 0}$, respectively $\{U_k\times U_k\}_{k\ge 0}$, to define smoothenings of locally $(\mu_{G/H}\otimes\mu_{G/H})$-integrable functions on $G/H\times G/H$, respectively locally $(\mu_G\otimes\mu_G)$-integrable functions on $G\times G$).

The innermost integral in (12.2.2.14) reads:

$$
\widetilde u(\pi(x),\pi(x))\int_{(h,h')\in H\times H}u_0(h^{-1}(h')^{-1}x)u_0((h')^{-1}x)\,\mathrm{d}\mu_{H\times H}(h,h') \tag{12.2.2.15}
$$

which turns, under the "shearing" change of variables $(h,h')\mapsto (h(h')^{-1},h')$, into:

$$
\widetilde u(\pi(x),\pi(x))\int_{(h,h')\in H\times H}u_0(h^{-1}x)u_0((h')^{-1}x)\,\mathrm{d}\mu_{H\times H}(h(h')^{-1},h')=\widetilde u(\pi(x),\pi(x)) \tag{12.2.2.16}
$$

where we are using $H$-invariance of the Haar measure $\mu_H$, and the identity $\int_H u_0(h^{-1}x)\,\mathrm{d}\mu_H(h)=1$, which holds since $u_0$ is an $H$-indentation on $G$ (see Lemma 12.2.1.1(3)). The identity in (12.2.2.16) holds for any $x\in G$ at which $\widetilde u(\pi(x),\pi(x))$ is defined, since $u_0$ is continuous. It follows that it holds $\mu_G$-almost everywhere on $G$.

We therefore deduce that the last integral in (12.2.2.14) equals:

$$
\int_D\widetilde u(\pi(x),\pi(x))\,\mathrm{d}\mu_G(x). \tag{12.2.2.17}
$$

By [Bou-II, Ch.VII,§2,n.3,Prop.5(c),INT VII.33], the integral in (12.2.2.17) equals $\int_{G/H}\widetilde u(x,x)\,\mathrm{d}\mu_{G/H}(x)$. Indeed, we call, using the notation of loc.cit., $\mathbf{f}:=1_D(x)\cdot |\widetilde u(\pi(x),\pi(x))|$, and observe that since $D$ is a fundamental domain, $\mathbf{f}^\flat=|\widetilde u|$, and formula [Bou-II, Ch.VII,§2,n.3,Prop.5(c),(12),INT VII.33] (which applies by [Bou-II, Ch.VII,§2,n.3,Prop.5(d),(12),INT VII.33]) implies that the following identity:

$$
\int_D\widetilde u(\pi(x),\pi(x))\,\mathrm{d}\mu_G(x)=\int_{G/H}\widetilde u(x,x)\,\mathrm{d}\mu_{G/H}(x) \tag{12.2.2.18}
$$

## PDF page 511

**12.2. LEBESGUE DIFFERENTIATION ALONG THE DIAGONAL** · **511**

holds. We deduce from (12.2.2.18) that the first identity in (12.2.2.4) holds.

We observe that we have, for every such $u$ and for all $h\in H$ and $\mu_G$-almost all $x\in G$:

$$
|\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)|=|u^\Delta_0(h^{-1}x,x)\cdot (\widetilde u(\pi(h^{-1}x),\pi(x))|=u^\Delta_0(h^{-1}x,x)\cdot |\widetilde u(\pi(h^{-1}x),\pi(x))|=\Psi^\Delta_{u_0}(|\widetilde u|)(h^{-1}x,x) \tag{12.2.2.19}
$$

since $u_0$, and hence both $u_0\otimes u_0$ and $u^\Delta_0$, are real-valued and nonnegative (the latter because $\mu_H$ is a positive Radon measure). By assumption, $|\widetilde u|$ is defined $\mu_{G/H}$-almost everywhere on the diagonal in $G/H\times G/H$, $\mu_{G/H}$-measurable and $\mu_{G/H}$-integrable over the diagonal in $G/H\times G/H$.

By the first identity in (12.2.2.4), we deduce that we have:

$$
\int_{G/H}|\widetilde u(x,x)|\,\mathrm{d}\mu_{G/H}(x)=\int_D\int_H\Psi^\Delta_{u_0}(|\widetilde u|)(h^{-1}x,x)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x)=\int_D\int_H|\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)|\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x) \tag{12.2.2.20}
$$

and hence the function $\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)$ of $(x,h)\in D\times H$ is $\mu_H\otimes\mu_G$ absolutely integrable over $D\times H$ by Tonelli's Theorem (see [Fol, Thm.2.37(a)]) applied to $f:=|\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)|$. By [Fol, Thm.7.27], which applies since $G$ is second countable, and hence so are $D$ and $H$, and $\mu_G$ and $\mu_H$ are Radon measures, hence $\sigma$-finite, we deduce that the identity:

$$
\int_D\int_H\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x)=\int_H\int_D\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)\,\mathrm{d}\mu_G(x)\,\mathrm{d}\mu_H(h) \tag{12.2.2.21}
$$

holds.

By invariance of $u^\Delta_0$ with respect to the diagonal action of $H$ on $G\times G$, we deduce that we have $\Psi^\Delta_{u_0}(\widetilde u)(h^{-1}x,x)=\Psi^\Delta_{u_0}(\widetilde u)(x,h^{-1}x)$ for all $h\in H$ and $\mu_G$-almost all $x\in G$, and hence the remaining identities in (12.2.2.4) follow from (12.2.2.21).

(3) : Let $\rho\in C_c(G/H\times G/H)$. Then $\rho\circ (\pi\times\pi)$ is a continuous function on $G\times G$, invariant under the continuous left-translation action of $H\times H$ on $G\times G$. For $u:G/H\times G/H\to\mathbf C$ a $(\mu_{G/H}\otimes\mu_{G/H})$-measurable and locally $(\mu_{G/H}\otimes\mu_{G/H})$-integrable function, $\rho\cdot u$ is also $(\mu_{G/H}\otimes\mu_{G/H})$-measurable and locally $(\mu_{G/H}\otimes\mu_{G/H})$-integrable function. We have:

$$\Psi^\Delta_{u_0}(\rho\cdot u)=u^\Delta_0\cdot ((\rho\cdot u)\circ (\pi\times \pi))=(\rho\circ (\pi\times\pi))\cdot\Psi^\Delta_{u_0}(u)$$

$(\mu_G\times\mu_G)$-almost everywhere.

(4) : Since $u^\Delta_0$ is continuous, then for all $(x,y)\in G\times G$ which is regular for $u\circ (\pi\times\pi)$ (see Corollary A.5.4.3):

$$
\lim_{k\to +\infty}\frac{1}{\mu_G(U_k)^2}\int_{xU_k\times yU_k}u^\Delta_0(y_1,y_2)\cdot (u(\pi(y_1),\pi(y_2)))\,\mathrm{d}(\mu_G\otimes\mu_G)(y_1,y_2) \tag{12.2.2.22}
$$

exists and is finite, and by Corollary A.5.4.3 we have that the value of the limit in (12.2.2.22) is:

$$
u^\Delta_0(x,y)\lim_{k\to +\infty}\frac{1}{\mu_G(U_k)^2}\int_{xU_k\times yU_k}u(\pi(y_1),\pi(y_2))\,\mathrm{d}(\mu_G\otimes\mu_G)(y_1,y_2) \tag{12.2.2.23}
$$

and the integral in (12.2.2.23) reads:

$$
\int_{xU_k\times yU_k}u(\pi(y_1),\pi(y_2))\,\mathrm{d}(\mu_G\otimes\mu_G)(y_1,y_2)=\int_{\pi(x)\bar U_k\times \pi(y)\bar U_k}u(\pi(y_1),\pi(y_2))\,\mathrm{d}(\mu_{G/H}\otimes\mu_{G/H})(\pi(y_1),\pi(y_2)) \tag{12.2.2.24}
$$

and since $U_k\subset D$ for every $k\ge 0$ by assumption, another application of [Bou-II, Ch.VII,§2,n.3,Prop.5(c),(12),INT VII.33] gives $\mu_G(U_k)=\mu_{G/H}(\bar U_k)$, and hence:

$$
\lim_{k\to +\infty}\frac{1}{\mu_G(U_k)^2}\int_{xU_k\times yU_k}u(\pi(y_1),\pi(y_2))\,\mathrm{d}(\mu_G\otimes\mu_G)(y_1,y_2)=\widetilde u(\pi(x),\pi(y)). \tag{12.2.2.25}
$$

## PDF page 512

**512** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

We deduce that $(x,y)\in G\times G$ is regular for $\Psi^\Delta_{u_0}(u)$ if and only if $(\pi(x),\pi(y))$ is regular for $u$ on $G/H\times G/H$.

Since the pre-image under $\pi\times\pi$ of a $(\mu_{G/H}\otimes\mu_{G/H})$-null set is a $(\mu_G\otimes\mu_G)$-null set, since it is locally $(\mu_G\otimes\mu_G)$-negligible by [Bou-II, Ch.VII,§2,No.3,Prop.6(a),INT VII.33] (see also [Bou-I, Ch.V,§6,No.6,Cor.1(a),INT V.72]), and hence negligible by Lemma A.5.3.3, since $G$ is second countable, we deduce that (12.2.2.9) holds $(\mu_G\otimes\mu_G)$-almost everywhere. $\square$

PROPOSITION 12.2.2.4. *Let $G$ be a second countable Hausdorff locally compact abelian group, $H\subset G$ a discrete subgroup, $\mu_H$ the counting measure on $H$, $\mu_G$ a choice of Haar measure on $G$, $\mu_{G/H}$ the unique Haar measure on $G/H$ determined by the choices of $\mu_H$ and $\mu_G$ as per Theorem D.1.2.1.*

*Assume that $G,H$ satisfy the conditions in Situation 12.2.2.1.*

*Let $G_k\subset G$ be an exhaustive $\mathbf N$-indexed filtration of $G$ by open subgroups (i.e. $G_k\subset G$ is an open, hence closed, subgroup, such that $G_k\subset G_{k+1}$ for every integer $k\ge 0$, and satisfying $\bigcup_{k\ge 0} G_k=G$).*

*For each integer $k\ge 0$, we define $H_k:=H\cap G_k$ the induced filtration on $H$.*

*Assume:*

*(1) there exists a fundamental domain $D$ for the continuous action of $H$ on $G$.*

*(2) $D\subset G_0$.*

*(3) $D$ is a fundamental domain within $G_k$ of the continuous action of $H_k$ on $G_k$.*

*(4) For every integer $k\ge 0$, $G_{k+1}/G_k$ is free of rank $1$.*

*We denote by $\alpha_k$ the indicator function of $G_k$ in $G$, and by $\beta_k$ the indicator function of the clopen subset $G-G_k$.*

*Let $u:G/H\times G/H\to\mathbf C$ be a measurable function, locally $(\mu_{G/H}\otimes\mu_{G/H})$-integrable, such that $\mu_{G/H}$-almost every point $(x,x)\in G/H\times G/H$ is regular for $u$, and $\widetilde u(x,x)$ is absolutely $\mu_{G/H}$-integrable.*

*Then, there exists an $H$-indentation $u_0$ on $G$ such that $\alpha_k\cdot u_0$ is an $H_k$-indentation on $G_k$ for every $k\ge 0$, and, writing:*

$$
u_k(x,y):=\Psi^\Delta_{u_0}(\widetilde u)(x,y)\beta_k(y),\quad (x,y)\in G\times G \tag{12.2.2.26}
$$

*we have:*

$$
\lim_{k\to +\infty}\int_D\int_H u_k(x,h^{-1}x)\,\mathrm{d}\mu_H(h)\,\mathrm{d}\mu_G(x)=0. \tag{12.2.2.27}
$$

PROOF. Note that since $G_k\subset G$ is an open subgroup, it is closed by [DE, Lemma 1.1.7(c)]. In particular, $G/G_k$, and hence $G_{k+1}/G_k$, is a discrete group with respect to the quotient topology.

We note that the induced group homomorphism:

$$
H_{k+1}/H_k\to G_{k+1}/G_k \tag{12.2.2.28}
$$

is continuous upon endowing $H_{k+1}/H_k$ with the quotient topology. Since $H\subset G$ is closed, $H_k\subset G_k$ is closed, and hence so is $H_k\subset H_{k+1}$. Since $G_k\subset G_{k+1}$ is open, so is $H_k\subset H_{k+1}$, since each $H_k$ is endowed with the subspace topology inherited from $G$.

In particular, $H_{k+1}/H_k$ is also discrete, and since $H_{k+1}\cap G_k=H_k$, then $H_{k+1}/H_k$ free, being a subgroup of a free abelian group of finite rank. It is therefore either trivial or of rank $1$, in which case the homomorphism in (12.2.2.28) is an isomorphism.

Let $g\in G_{k+1}$ be of the form $h\cdot x$ for unique $x\in D$ and $h\in H_{k+1}$. Since $D\subset G_k$, the homomorphism in (12.2.2.28) is surjective, and hence an isomorphism.

We now consider the continuous homomorphisms:

$$
G_k/H_k\to G/H \tag{12.2.2.29}
$$

for each integer $k\ge 0$, all injective since $H\cap G_k=H_k$, and open since $G_k\subset G$ is an open subgroup, and hence $G_k\cdot H\subset G$ is open by [DE, Lemma 1.1.3(e)].

## PDF page 513

12.2. LEBESGUE DIFFERENTIATION ALONG THE DIAGONAL    513

The cokernel of the injective continuous open group homomorphism from (12.2.2.29) is discrete when
endowed with the quotient topology, and it trivial, since $D\subset G_k$, and hence $G=D\cdot H\subset G_k\cdot H$.

The quotient group:

$$
G/G_k
\tag{12.2.2.30}
$$

is discrete and free. Indeed, it is the direct limit topological group (see [**DE**, Ch.1,§1.8,p.29]; see also [**DE**,
Prop.1.8.6]) of the open and closed subgroups $G_m/G_k$ for $m\ge k$: open and closed since the pre-image of
$G_m/G_k$ in $G$ is $G_m$, since $G_k\subset G_m$ for every integer $m\ge k$, and $G_m\subset G$ is open and closed. The transition
maps $G_m/G_k\to G_{m+1}/G_k$ are injective, their source is free of rank $m-k$, and their cokernel is free of rank
1, and hence $G_{m+1}/G_k$ splits as the product of $G_m/G_k$ by the free group $G_{m+1}/G_m$ of rank 1.

Upon therefore choosing a $\mathbf{Z}$-basis $\{\xi_k,\ldots,\xi_{m+k}\}$ for $G_m/G_k$, and an element $\xi_{m+k+1}$ of $G_{m+1}$ that
is a $\mathbf{Z}$-basis for $G_{m+1}/G_m$, then the image of $\{\xi_k,\ldots,\xi_{m+k+1}\}$ is a $\mathbf{Z}$-basis for $G_{m+1}/G_k$, and hence
$\bigcup_{m\ge k}\{\xi_k,\ldots,\xi_{m+k}\}$ is a $\mathbf{Z}$-basis for $G/G_k$.

Let $u_1:G_0\to\mathbf{C}$ be an $H_0$-indentation on $G_0$.

We denote by $\varepsilon_k$ the function on $\xi_k^{\mathbf{Z}}$ defined to be 1 on $\xi_k^0$ and zero elsewhere, we define $u_0:=u_1\otimes\bigotimes_{k\ge 1}\varepsilon_k$.

$u_0$ is a complex-valued function on $G$, continuous, since it is the tensor product of a continuous function on $G_0$
and a continuous function on $\prod_{k\ge 1}\xi_k^{\mathbf{Z}}$, pulled back to $G$ along the isomorphism of Hausdorff locally compact
abelian groups $G\simeq G_0\times\prod_{k\ge 1}\xi_k^{\mathbf{Z}}$.

$G_0$ as an open subgroup of $G$ is isomorphic to $G_0\times 1$ under such isomorphism, and hence $u_0$ is realized as
the extension by zero of $u_1$ to $G$.

$u_0$ is real-valued and nonnegative, since $u_1$ is. Let $K\subset G$ be an arbitrary compact subset. Then, upon
denoting by $\pi:G\to G/H$ the continuous quotient homomorphism, and by $S$ the support of $u_0$, we deduce
that the intersection $S\cap\pi^{-1}(\pi(K))$ is compact, since it is contained in the intersection $S\cap\pi^{-1}(\pi(K\cap G_0))$,
and $K\cap G_0$ is compact, being $G_0\subset G$ closed.

Moreover, we have, for every $x\in G$:

$$
\int_H u_0(h^{-1}x)\,\mathrm{d}\mu_H(h)
=\int_{H/H_0}\bigotimes_{k\ge 1}\varepsilon_k((h')^{-1}\overline{x})\int_{H_0}u_1(h^{-1}x)\,\mathrm{d}\mu_{H_0}(h)\,\mathrm{d}\mu_{H/H_0}(h')
\tag{12.2.2.31}
$$

where $\overline{x}$ is the image of $x$ in $G/G_0$. We have:

$$
\int_{H/H_0}\bigotimes_{k\ge 1}\varepsilon_k((h')^{-1}\overline{x})\,\mathrm{d}\mu_{H/H_0}(h')=1,
\qquad
\int_{H_0}u_1(h^{-1}x)\,\mathrm{d}\mu_{H_0}(h)=1
$$

and hence the integral in (12.2.2.31) equals 1.

The function $u_0$ is therefore an $H$-indentation on $G$, and by its design the function $\alpha_k\cdot u_0$ is an $H_k$-indentation on $G_k$ for every integer $k\ge 0$.

The function $f(x,h):=\Psi^{\Delta}_{u_0}(\widetilde{u})(x,h^{-1}x)$ of $(x,h)\in D\times H$ is absolutely $(\mu_G\otimes\mu_H)$-integrable by Proposition
12.2.2.2(2).

We observe that $f(x,h)\beta_k(h^{-1}x)=f(x,h)\cdot 1_{S_k(x)}(h)$ for $S_k(x)\subset H$ the subset, for each $x\in D$, of those
$h\in H$ such that $h^{-1}x\in G-G_k$, then we deduce that $f_k(x,h):=f(x,h)\cdot 1_{S_k(x)}(h)$ tends to zero pointwise
$(\mu_G\otimes\mu_H)$-almost everywhere on $D\times H$.

Indeed, for each fixed $x\in D$ and $h\in H$, the point $h^{-1}x$ is contained in at most finitely many of the
subsets $G-G_k$, since $\bigcup_{k\ge 0}G_k=G$ and $G_k\subset G_{k+1}$. Indeed, there exists $k\ge 0$ large enough such that
$h^{-1}x\in G_k$, in which case $h^{-1}x$ is contained in $G_m$ for every integer $m\ge k$, and hence $h^{-1}x\notin G-G_m$ for
every $m\ge k$, i.e. $1_{S_m(x)}(h)=0$ for all $m\ge k$. This shows that $f_m(x,h)=0$ for all $m\ge k$, where $k$ depends
on the point $(x,h)$, i.e. $f_k\to 0$ pointwise on $D\times H$, and hence pointwise $(\mu_G\otimes\mu_H)$-almost everywhere on
$D\times H$.

Since $|f_k|\le|f|$ for every integer $k\ge 0$, then, by Dominated Convergence, (12.2.2.26) holds. $\square$

## PDF page 514

514    CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE

**12.3. Putting the pieces together: global to $S$-local deconstruction of the geometric kernel**

$^{1}$

**12.4. $S$-local trace calculation**

In this section we compute the part of the trace formula that is delegated to the $S$-local function spaces
discussed. The calculations are analogous to calculations performed by Connes (see [**Co**, §VII,Thm.4,p.31])
and reprised by R. Meyer (see [**Me1**, §3]). The calculation presented below exhibits small variations on the
same theme.

Most importantly, the role of the $S$-adelic Fourier transform, whose job is to turn the integral calculation
of interest into a simpler one coming down to a volume calculation on the $S$-idele class group $J_{F,S}$, was
identified by Connes in his 1998 paper (see [**Co**, §VII,Thm.4,p.31]).

**12.4.1. $S$-local trace on the Paley-Wiener Levels.**

Theorem 12.4.1.1 (*S*-local Trace calculation). *Let $F$ be a number field, $S$ a finite set of places containing
all the Archimedean places.*

*Let $\varphi\in\mathcal{D}(C_F)$. Assume $\mathrm{Pic}(\mathcal{O}_{F,S})=1$, and that $S$ contains all the ramified places of $F$. Assume that $\varphi$
is $\widehat{\mathcal{O}}^{\times}_{F,\Sigma_F-S}$-invariant.*

*Then:*

$$
\begin{align}
\frac{1}{\overline{\mu}_{S,1}(J^{1}_{F,S})}
\int_{J_{F,S}}k^{\mathrm{PW}}_{S,\varphi,\lambda,\lambda'}(x,x)\,\mathrm{d}\overline{\mu}_S(x)
&=\sum_{v\in S_\infty,\ v\ \mathrm{real}}\frac{1}{2}
\int'_{F_v^{\times}}\frac{\varphi(g_v)|g|_v^{1/2}}{|1-g_v|}\,\mathrm{d}\mu_v(g_v)
\tag{12.4.1.1}\\
&\quad+\sum_{v\in S_\infty,\ v\ \mathrm{complex}}\frac{1}{2\pi}
\int'_{F_v^{\times}}\frac{\varphi(g_v)|g|_v^{1/2}}{|1-g_v|}\,\mathrm{d}\mu_v(g_v)
\tag{12.4.1.2}\\
&\quad+\sum_{v\in S_f}\frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^{\times})}
\int'_{F_v^{\times}}\frac{\varphi(g_v)|g|_v^{1/2}}{|1-g_v|_v}\,\mathrm{d}\mu_v(g_v)
+\varphi(1)\log(\lambda\lambda')+o(1)
\tag{12.4.1.3}
\end{align}
$$

*where $q_v:=|\pi_v|_v^{-1}$, for $v\in S_f$ and $\pi_v$ any choice of uniformizer at $v$ of the non-Archimedean local field $F_v$,
and as $\lambda,\lambda'\to+\infty$.*

Note how the volumes of all the local unit groups feature at the denominators in the formula from
(12.4.1.4), as they should, them being stabilizers, featuring as inertias of the quotient stacks arising as the
periodic and fixed orbital supports of the Schauder bases constructed in Chapter 7, and responsible for the
local traces in Theorem 7.4.2.1 and Theorem 7.4.3.2.

The measures $\mu_v$ for $v$ real, $\frac{1}{2\pi}\mu_v$, and $\frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^{\times})}\mu_v$ for $v$ non-Archimedean, happen to be exactly the
canonical Haar measures on the modulated groups $F_v^{\times}$ (see Remark B.4.4.2).

Note also that $\overline{\mu}_{S,1}(J^{1}_{F,S})^{-1}\cdot\overline{\mu}_S$ is the canonical measure on the $\mathbf{R}_{>0}$-modulated group $J_{F,S}$.

Proof. We recall that for $\lambda,\varepsilon>0$ two real numbers, we defined smooth $(\lambda,\varepsilon)$-cutoff functions $\rho(x)$ in
Definition 9.3.3.1.$^{2}$

We rename as $\varphi$ the unique smooth compactly supported function on $J_{F,S}$ obtained by composing $\varphi$ with
the isomorphism $C_{F,S}\to C_F$ (an isomorphism because, by assumption, $\mathrm{Pic}(\mathcal{O}_{F,S})=1$) and descending the

$^{1}$Include section.

$^{2}$Extend Definition 9.3.3.1 so as to allow cutoffs whose support is over $(0,\lambda]$ and not only over $[1/\lambda,\lambda]$. Return here and change
the choice of smooth $(\lambda,\varepsilon)$-cutoff into a smoothening of $1_{[1/\lambda'',\lambda]}$ with $\lambda''$ not tied to $\lambda$. Then study the convergence of the
integral in (12.4.1.23), with $\log|w|_{F,S}$ replaced by $\log\max\{\frac{|w|_{F,S}}{\lambda'},\frac{1}{\lambda''}\}$, as $\lambda',\lambda''\to+\infty$.

## PDF page 515

**12.4. S-LOCAL TRACE CALCULATION** · **515**

composition to $J_{F,S}$ by $\widehat{\mathcal{O}}^{\times}_{F,\Sigma_F-S}$-invariance. We assume, without loss of generality, that $\varphi$ is $\chi|_{C^1_F}$-homogeneous.
Its action by convolution on $W^{s,2}(C_F)$ and its closed subspace $W^{s,2}_{1/2}\mathrm{H}_{0,\mathrm{cont}}(F^{\times}, \mathcal{S}_0(\mathbf{A}_F))$ and its own closed invariant subspaces, factors through each $\chi|_{C^1_F}$-isotype, respectively.

Acting by convolution on the invariant Paley-Wiener level

$$
W^{s,2}\mathrm{PW}^{\mathrm{inv}}_{S,\lambda'}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf{A}_{F,S}))
$$

and composing the resulting convolution action by the truncation operator $M_{\rho_{\lambda-}}$ (where, recall $^3$, $\rho_{\lambda-}$ is notation intended to recall that $\rho$ is supported over $(0,\lambda]$), we obtain a nuclear operator. We compute its trace below.

Since $\rho$ is a smooth $(\lambda,\varepsilon)$-cutoff on $C_F$, and hence on $J_{F,S}$, then the operator $R_{\rho}A(\varphi)$ on

$$
W^{s,2}_{1/2}\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}^{\times}_{F,S}, \mathcal{S}_0(\mathbf{A}_{F,S}))
$$

factors through the image under the multiplication operator by $|\cdot|^{1/2}_{F,S}$ (within $\mathcal{S}_{(0,+\infty)}(J_{F,S})\times \mathcal{S}_{(-\infty,1)}(J_{F,S})$) of the image under the $S$-local $\theta$-function operator $\Phi_{F,S}$, of $\mathcal{S}_{00}(\mathbf{A}_{F,S})$.

Note that this is, in turn, a copy, linearly and topologically, of $|\cdot|^{1/2}_{F,S}\mathcal{S}_{\mathrm{E}}(J_{F,S})$, by Proposition 5.3.4.4$^4$).

By Lemma C.3.2.2, it is enough to compute the trace of $R_{\rho}A(\varphi)$ on

$$
E:=|\cdot|^{1/2}_{F,S}\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}^{\times}_{F,S}, \mathcal{S}_{00}(\mathbf{A}_{F,S})).
$$

This, we do as follows, following the arguments first presented in [**Co**, §VII,Thm.4,p.31] and revisited in [**Me1**, §3.4,p.19].

We choose $\widetilde{\varphi}\in\mathcal{D}(\mathrm{GL}_1(\mathbf{A}_{F,S}))$ such that, as continuous functions of $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$, invariant under the continuous left-translation action of $\mathcal{O}^{\times}_{F,S}$, we have

$$
\sum_{\xi\in\mathcal{O}^{\times}_{F,S}}\widetilde{\varphi}(\xi g)=\varphi(g). \tag{12.4.1.4}
$$

The existence of $\widetilde{\varphi}$ is ensured by discreteness of $\mathcal{O}^{\times}_{F,S}$ in $\mathrm{GL}_1(\mathbf{A}_{F,S})$ and compactness of the support of $\widetilde{\varphi}$ (see, for example, the proof of Lemma 4.2.1.5(2)).

The composition of $R_{\rho}$ and $A(\varphi)$ on $E$ can thus be analyzed by studying the composition of the following operator on $\mathcal{S}_{00}(\mathbf{A}_{F,S})$:

$$
A_{\widetilde{\varphi}}: f\mapsto \int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}\widetilde{\varphi}(g)(|g^{-1}x|^{1/2}_{F,S}f(g^{-1}x))\,\mathrm{d}\mu_S(g)
$$

which is valued in $E$, followed by $R_{\rho}$.

Indeed, $R_{\rho}A_{\widetilde{\varphi}}$ factors through $R_{\rho}A(\varphi)$, and the trace of the latter can be computed using the recipe from Proposition 12.2.2.2 from §12.2.2 and the integral kernel of the former. The main difficulty of the calculation being performed in this argument, is computing the integral kernel of $R_{\rho}A_{\widetilde{\varphi}}$. This, we now do as follows.

We begin by observing that the operator:

$$
A_{\widetilde{\varphi}}:\mathcal{S}_{00}(\mathbf{A}_{F,S})\to E
$$

has a Schwartz kernel which can be described explicitly. Our goal is three-fold:

(I) write down a candidate for the Schwartz kernel of $A_{\widetilde{\varphi}}$ and then be show that it is indeed the Schwartz kernel of $A_{\widetilde{\varphi}}$.

(II) Write down a candidate for the Schwartz kernel of $R_{\rho}A_{\widetilde{\varphi}}$ and then show that it is indeed the Schwartz kernel of $R_{\rho}A_{\widetilde{\varphi}}$.

$^3$See previous footnote.

$^4$Return here after the Proposition is updated.

## PDF page 516

**516** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

(III) Use the recipe from Proposition 12.2.2.2 from §12.2.2 to compute the trace of $R_{\rho}A(\varphi)$, and deduce the formula from (12.4.1.4) from it, by identifying the integral kernel of $R_{\rho}A(\varphi)$ with $k^{\mathrm{PW}}_{S,\varphi,\lambda,\lambda'}$.

The first two points will be carried out using the integral in the sense of Pettis, and topological properties of the Hausdorff locally convex topological $\mathbf{C}$-vector spaces $\mathcal{S}_{00}(\mathbf{A}_{F,S})$ and $E$. The third and last will use the $S$-adelic Fourier transform on the source, to compute the integral of the smoothening of the resulting integral kernel along the diagonal.

**Step I:** We denote, for each $g\in\mathrm{GL}_1(\mathbf{A}_{F,S})$ and $x\in\mathbf{A}_{F,S}$, by

$$
\delta_{y=g^{-1}x}:\mathcal{S}(\mathbf{A}_{F,S})\to\mathbf{C}
$$

the continuous linear functional defined by sending $f\in\mathcal{S}(\mathbf{A}_{F,S})$ (as a function of $y\in\mathbf{A}_{F,S}$) to $f(g^{-1}x)$.

We now integrate the continuous function $g\mapsto\delta_{y=g^{-1}x}$ to obtain

$$
K:=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{-1/2}_{F,S}\widetilde{\varphi}(g)\delta_{y=g^{-1}x}\,\mathrm{d}\mu_S(g) \tag{12.4.1.5}
$$

and since $\widetilde{\varphi}$ is continuous (in fact, smooth) and compactly supported, then by Theorem C.4.3.5 the integral converges in the sense of Pettis (i.e. it is valued in $\mathcal{S}(\mathbf{A}_{F,S})'_{\beta}$, which, note, is complete, hence quasi-complete, so the Theorem applies).

We rename $\delta_{y=g^{-1}x}$ as $\delta(y-g^{-1}x)$ to ease the notation, and note that, as $x\in\mathbf{A}_{F,S}$ varies, this is a continuous function of $(g,x)\in\mathrm{GL}_1(\mathbf{A}_{F,S})\times\mathbf{A}_{F,S}$ values in $\mathcal{S}(\mathbf{A}_{F,S})'_{\beta}$.

The integral from (12.4.1.5) is a continuous function $\mathbf{A}_{F,S}\to\mathcal{S}(\mathbf{A}_{F,S})'_{\beta}$, and in fact an element of $\mathcal{S}(\mathbf{A}_{F,S},\mathcal{S}(\mathbf{A}_{F,S})'_{\beta})$, which is in turn linearly and topologically isomorphic, by Theorem C.2.4.19, to

$$
\mathcal{S}(\mathbf{A}_{F,S})\widehat{\otimes}_{\pi}\mathcal{S}(\mathbf{A}_{F,S})'_{\beta}\simeq\mathscr{L}_{\beta}(\mathcal{S}(\mathbf{A}_{F,S})). \tag{12.4.1.6}
$$

Under the composition linear topological isomorphism $\mathcal{S}(\mathbf{A}_{F,S},\mathcal{S}(\mathbf{A}_{F,S})'_{\beta})\simeq\mathscr{L}_{\beta}(\mathcal{S}(\mathbf{A}_{F,S}))$, $K$ is sent to a continuous linear endomorphism, which we now compute. We have, for any $f\in\mathcal{S}(\mathbf{A}_{F,S})$:

$$
(Kf)(x)=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{-1/2}_{F,S}\widetilde{\varphi}(g)\langle f,\delta(y-g^{-1}x)\rangle_{\mathcal{S}(\mathbf{A}_{F,S}),\mathcal{S}(\mathbf{A}_{F,S})'}\,\mathrm{d}\mu_S(g)=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{-1/2}_{F,S}\widetilde{\varphi}(g)f(g^{-1}x)\,\mathrm{d}\mu_S(g). \tag{12.4.1.7}
$$

We deduce that (the image of) $K$ as an element of $\mathcal{S}_{00}(\mathbf{A}_{F,S})\widehat{\otimes}_{\pi}\mathcal{S}_{00}(\mathbf{A}_{F,S})'_{\beta}$ is the Schwartz kernel of $A_{\widetilde{\varphi}}$. Note that $K$ is contained in the linear and topological subspace

$$
\mathcal{S}_{00}(\mathbf{A}_{F,S})\widehat{\otimes}_{\pi}\mathrm{H}_{0,\mathrm{cont}}(\mathcal{O}^{\times}_{F,S},\mathcal{S}_{00}(\mathbf{A}_{F,S}))'_{\beta}.
$$

This carries out (I).

**Step II:** We now identify the Schwartz kernel of the operator $R_{\rho}A_{\widetilde{\varphi}}$. Recall that this is the composition of three operators:

- $\widehat{P}_{\rho,\lambda'}:\mathcal{S}(\mathbf{A}_{F,S})\to\mathcal{S}(\mathbf{A}_{F,S})$, which is defined as the $S$-adelic Fourier transform, multiplied by the choice of smooth $(\lambda',\varepsilon)$-cutoff $\rho$ given by a choice of $\varepsilon$-smoothening of the indicator function of the subset

$$
\{x\in\mathbf{A}_{F,S}:|x|_{F,S}\le\lambda'\}
$$

further followed by the $S$-adelic Fourier transform again, composed by the linear topological automorphism induced by negation (i.e. multiplication by $-1$) on $\mathbf{A}_{F,S}$.

- The operator $A_{\widetilde{\varphi}}$.

- $P_{\rho,\lambda}:\mathcal{S}(\mathbf{A}_{F,S})\to\mathcal{S}_{00}(\mathbf{A}_{F,S})$ given by multiplication by the choice of smooth $(\lambda,\varepsilon)$-cutoff $\rho$ given by a choice of $\varepsilon$-smoothening of the indicator function of the subset

$$
\{x\in\mathbf{A}_{F,S}:|x|_{F,S}\le\lambda\}.
$$

## PDF page 517

**12.4. S-LOCAL TRACE CALCULATION** · **517**

Equivalently, $R_{\rho}A_{\widetilde{\varphi}}$ is the operator

$$
R_{\rho}A_{\widetilde{\varphi}}:=P_{\rho,\lambda}\circ A_{\widetilde{\varphi}}\circ\widehat{P}_{\rho,\lambda'}.
$$

We compute

$$
(A_{\widetilde{\varphi}}\circ\widehat{P}_{\rho,\lambda'})(f)=A_{\widetilde{\varphi}}\circ\mathcal{F}^{-1}_S(\rho_{\lambda',-}(\cdot)\widehat{f}(\cdot)) \tag{12.4.1.8}
$$

$$
=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{-1/2}_{F,S}\widetilde{\varphi}(g)\int_{\mathbf{A}_{F,S}}\rho_{\lambda',-}(x)\widehat{f}(x)\psi_{S,\mathrm{std}}(xg^{-1}y)\,\mathrm{d}\nu_S(x)\,\mathrm{d}\mu_S(g) \tag{12.4.1.9}
$$

$$
=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{-1/2}_{F,S}\widetilde{\varphi}(g)\langle\delta(u-g^{-1}y),\mathcal{F}^{-1}_{S,x}(\rho_{\lambda',-}(x)\widehat{f}(x))(u)\rangle_{\mathcal{S}(\mathbf{A}_{F,S})',\mathcal{S}(\mathbf{A}_{F,S})}\,\mathrm{d}\mu_S(g). \tag{12.4.1.10}
$$

We now look into the operator sending $f\in\mathcal{S}(\mathbf{A}_{F,S})$ to $\widehat{P}_{\rho,\lambda'}(f)=\mathcal{F}^{-1}_S(\rho_{\lambda',-}\cdot\widehat{f})$, where $\mathcal{F}^{-1}_S$ is the inverse Fourier transform. By the Convolution Theorem, the Schwartz kernel of $\widehat{P}_{\rho,\lambda'}$ is

$$
k_{\rho,\lambda'}(x,y)=\widehat{\rho_{\lambda',-}}(x-y)
$$

as a function of $(x,y)\in\mathbf{A}_{F,S}$ To see this, we compute

$$
\int_{\mathbf{A}_{F,S}}k_{\rho,\lambda'}(x,y)f(y)\,\mathrm{d}\nu_S(y)=\int_{\mathbf{A}_{F,S}}\widehat{\rho_{\lambda',-}}(x-y)f(y)\,\mathrm{d}\nu_S(y)=\mathcal{F}^{-1}_S(\rho_{\lambda',-}\widehat{f}).
$$

To compute the kernel of $P_{\rho,\lambda}\circ A_{\widetilde{\varphi}}\circ\widehat{P}_{\rho,\lambda'}$ (noting that $P_{\rho,\lambda}$ is the multiplication operator by the chosen smooth $(\lambda,\varepsilon)$-cutoff $\rho_{\lambda,-}(x)$) we compute the distributional convolution of $K$ and $k_{\rho,\lambda'}$, which is in turn computed using the Fourier transform.

We obtain

$$
k^{\mathrm{PW}}_{S,\varphi,\lambda,\lambda'}(x,y)=\rho_{\lambda,-}(x)\int_{\mathbf{A}_{F,S}}K(x,z)k_{\rho,\lambda'}(z,y)\,\mathrm{d}\nu_S(z).
$$

This finishes carrying out **Step II**.

**Step III:** Using the Hardy-Littlewood Maximal Theorem from Theorem A.5.3.7 and the fact that $k^{\mathrm{PW}}_{S,\varphi,\lambda,\lambda'}$ is the integral kernel of a nuclear operator, we rename as $k^{\mathrm{PW}}_{S,\varphi,\lambda,\lambda'}$ the smoothening of $k^{\mathrm{PW}}_{S,\varphi,\lambda,\lambda'}$ along the diagonal, and use Parseval's Formula to compute, for each $\xi\in\mathcal{O}^{\times}_{F,S}$, the integral

$$
\int_{E_{S,0}}k^{\mathrm{PW}}_{S,\varphi,\lambda,\lambda'}(x,\xi x)\,\mathrm{d}\nu_S(x) \tag{12.4.1.11}
$$

and observe that it equals

$$
\int_{E_{S,0}}\rho_{\lambda,-}(x)\int_{\mathbf{A}_{F,S}}\int_{\mathbf{A}_{F,S}}K(x+z,\xi x)\overline{\psi_{S,\mathrm{std}}(zu)}\,\mathrm{d}\nu_S(z)\int_{\mathbf{A}_{F,S}}k_{\rho,\lambda'}(x+z,x)\overline{\psi_{S,\mathrm{std}}(zu)}\,\mathrm{d}\nu_S(z)\,\mathrm{d}\nu_S(u)\,\mathrm{d}\nu_S(x). \tag{12.4.1.12}
$$

We have

$$
\int_{\mathbf{A}_{F,S}}K(x+z,\xi x)\overline{\psi_{S,\mathrm{std}}(zu)}\,\mathrm{d}\nu_S(z)=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{-1/2}_{F,S}\widetilde{\varphi}(g)\int_{\mathbf{A}_{F,S}}\delta(x+z-g^{-1}\xi x)\overline{\psi_{S,\mathrm{std}}(zu)}\,\mathrm{d}\nu_S(z)\,\mathrm{d}\mu_S(g) \tag{12.4.1.13}
$$

$$
=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{-1/2}_{F,S}\widetilde{\varphi}(g)\overline{\psi_{S,\mathrm{std}}((g^{-1}\xi-1)xu)}\,\mathrm{d}\mu_S(g) \tag{12.4.1.14}
$$

and

$$
\int_{\mathbf{A}_{F,S}}k_{\rho,\lambda'}(x+z)\overline{\psi_{S,\mathrm{std}}(zu)}\,\mathrm{d}\nu_S(z)=\rho_{\lambda',-}(u). \tag{12.4.1.15}
$$

## PDF page 518

**518** · **CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE**

We now further analyze the integral

$$
\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{-1/2}_{F,S}\widetilde{\varphi}(g)\overline{\psi_{S,\mathrm{std}}((g^{-1}\xi-1)xu)}\,\mathrm{d}\mu_S(g)=\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|g|^{1/2}_{F,S}\widetilde{\varphi}(g^{-1})\overline{\psi_{S,\mathrm{std}}((g\xi-1)xu)}\,\mathrm{d}\mu_S(g) \tag{12.4.1.16}
$$

where we used invariance of the $S$-local multiplicative Tamagawa measure $\mu_S$ under inversion.

We note that we have

$$
\mu_S=c_S|\cdot|^{-1}_{F,S}\nu_S
$$

as Radon measures on $\mathbf{A}_{F,S}$. The positive real number $c_S>0$ is given by:

$$
c_S:=\prod_{v\in S_f}\frac{N(\mathfrak{p}_v)}{N(\mathfrak{p}_v)-1}. \tag{12.4.1.17}
$$

We call $z:=g\xi-1$, and hence $g=\xi^{-1}(1+z)$.

The integral from (12.4.1.16) reads as follows:

$$
c_S\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}|\xi^{-1}(1+z)|^{-1/2}_{F,S}\widetilde{\varphi}(\xi(1+z)^{-1})\overline{\psi_{S,\mathrm{std}}(zxu)}\,\mathrm{d}\nu_S(z) \tag{12.4.1.18}
$$

We call $\eta(x)=|x|^{1/2}_{F,S}\widetilde{\varphi}(x^{-1})$, $x\in\mathrm{GL}_1(\mathbf{A}_{F,S})$, and the integral in (12.4.1.18) reads:

$$
c_S\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}\left\{\frac{\eta(\xi^{-1}(1+z))}{|\xi^{-1}(1+z)|_{F,S}}\right\}\overline{\psi_{S,\mathrm{std}}(zxu)}\,\mathrm{d}\nu_S(z). \tag{12.4.1.19}
$$

We define:

$$
\eta_{\xi}(z):=\frac{\eta(\xi^{-1}(1+z))}{|\xi^{-1}(1+z)|_{F,S}} \tag{12.4.1.20}
$$

and rewrite (12.4.1.19) as:

$$
c_S\int_{\mathrm{GL}_1(\mathbf{A}_{F,S})}\eta_{\xi}(z)\overline{\psi_{S,\mathrm{std}}(zxu)}\,\mathrm{d}\nu_S(z)=c_S\widehat{\eta_{\xi}(xu)}. \tag{12.4.1.21}
$$

In light of (12.4.1.12), the integral from (12.4.1.11) equals:

$$
c_S\int_{x\in E_{S,0},|x|_{F,S}\in(0,\lambda],|u|_{F,S}\le\lambda'}\widehat{\eta_{\xi}(xu)}\,\mathrm{d}\nu_S(x)\,\mathrm{d}\nu_S(u). \tag{12.4.1.22}
$$

We now perform the change of variables $w=xu$ and obtain

$$
\mathrm{d}\nu_S(x)\otimes\mathrm{d}\nu_S(u)=\frac{\mathrm{d}\nu_S(x)}{|x|_{F,S}}\otimes\mathrm{d}\nu_S(w)
$$

which gives that (12.4.1.22) in turn equals:

$$
c_S\int_{|w|_{F,S}\le\lambda\lambda'}\int_{x\in E_{S,0},\frac{|w|_{F,S}}{\lambda'}\le|x|_{F,S}\le\lambda}\widehat{\eta_{\xi}(w)}\,\mathrm{d}\nu_S(w)\frac{\mathrm{d}\nu_S(x)}{|x|_{F,S}}=\int_{|w|_{F,S}\le\lambda\lambda'}\int_{x\in E_{S,0},\frac{|w|_{F,S}}{\lambda'}\le|x|_{F,S}\le\lambda}\widehat{\eta_{\xi}(w)}\,\mathrm{d}\nu_S(w)\,\mathrm{d}\mu_S(x) \tag{12.4.1.23}
$$

$$
=\int_{|w|_{F,S}\le\lambda\lambda'}\widehat{\eta_{\xi}(w)}\left\{\overline{\mu}_{S,1}(J^1_{F,S})(\log(\lambda\lambda')-\log|w|_{F,S})\right\}\,\mathrm{d}\nu_S(w). \tag{12.4.1.24}
$$

## PDF page 519

12.5. TRACE FORMULA: THE MAIN THEOREM OF THIS WORK    519

The calculation from [**Co**, §VII,Thm.4,p.31] now applies, and, using Lemma B.4.4.3, Lemma B.4.4.5 and
Lemma B.4.3.2, gives that the sum over $\xi\in\mathcal{O}_{F,S}^{\times}$ of last integral from (12.4.1.23) equals:

$$
\begin{align}
\overline{\mu}_{S,1}(J^{1}_{F,S})\varphi(1)\log(\lambda\lambda')
&\;+\;\overline{\mu}_{S,1}(J^{1}_{F,S})\sum_{v\in S_{\infty},\ v\ \mathrm{real}}
\frac{1}{2}\int'_{F_{v}^{\times},\alpha_{v,0}}
\frac{|g|_{v}^{1/2}\varphi(g^{-1})}{|1-g|_{v}}\,\mathrm{d}\mu_{v}(g)
\tag{12.4.1.25}\\
&\;+\;\overline{\mu}_{S,1}(J^{1}_{F,S})\sum_{v\in S_{\infty},\ v\ \mathrm{complex}}
\frac{1}{2\pi}\int'_{F_{v},\alpha_{v,0}}
\frac{|g|_{v}^{1/2}\varphi(g^{-1})}{|1-g|_{v}}\,\mathrm{d}\mu_{v}(g)
\tag{12.4.1.26}\\
&\;+\;\overline{\mu}_{S,1}(J^{1}_{F,S})\sum_{v\in S_{f}}
\frac{\log(q_{v})}{\mu_{v}(\mathcal{O}_{F_{v}}^{\times})}
\int'_{F_{v}^{\times},\alpha_{v,0}}
\frac{|g|_{v}^{1/2}\varphi(g^{-1})}{|1-g|_{v}}\,\mathrm{d}\mu_{v}(g)
\tag{12.4.1.27}\\
&\;+\;o(1)
\tag{12.4.1.28}
\end{align}
$$

as $\lambda,\lambda'\to+\infty$ as $\varepsilon\lambda=o(1)$ and $\varepsilon\lambda'=o(1)$.

We now note that the three finite sums in (12.4.1.25) are equal to the corresponding finite sums with $\varphi(g)$
in place of $\varphi(g^{-1})$, which proves that (12.4.1.4) holds. $\square$

**12.5. Trace formula: the Main Theorem of this work**

In this section we perform the main trace calculation, i.e. we compute the trace of the nuclear operator:

$$
P^{\mathrm{geom}}_{\rho,a}\circ A(\varphi)
$$

for any test function $\varphi\in\mathcal{D}(C_{F})$ satisfying $\varphi(1)=0$, in the special case the parameter $a$ is chosen to be
$a=1/2$, and as $\rho$ is a $(\Lambda,\varepsilon)$-cutoff in the sense of Definition 9.3.3.1, as $\Lambda\to+\infty$ while having $\varepsilon\Lambda=o(1)$.

This is also where the necessity of the choice $a=1/2$ is explained.

**12.5.1. Trace Formula: the statement.** The following is the main Theorem of this work. Throughout
the remainder of this Chapter, we will be collecting the fruits of the work done so far, and prove it.

Theorem 12.5.1.1 (Trace Formula). *Let $F$ be a number field. Let $\varphi\in\mathcal{D}(C_{F})$ be a test function satisfying
$\varphi(C_{F}^{1})=0$.*

*Then, the following identity holds:*

$$
\begin{align}
&\sum_{v\in S_{\infty},\ v\ \mathrm{real}}\frac{1}{2}\int'_{F_{v}^{\times}}
\frac{\varphi(g_{v})|g|_{v}^{1/2}}{|1-g_{v}|}\,\mathrm{d}\mu_{v}(g_{v})
\;+\;\sum_{v\in S_{\infty},\ v\ \mathrm{complex}}\frac{1}{2\pi}\int'_{F_{v}^{\times}}
\frac{\varphi(g_{v})|g|_{v}^{1/2}}{|1-g_{v}|}\,\mathrm{d}\mu_{v}(g_{v})
\tag{12.5.1.1}\\
&\;+\;\sum_{v\in\Sigma_{F,f}}\frac{\log(q_{v})}{\mu_{v}(\mathcal{O}_{F_{v}}^{\times})}
\int'_{F_{v}^{\times}}
\frac{\varphi(g_{v})|g|_{v}^{1/2}}{|1-g_{v}|_{v}}\,\mathrm{d}\mu_{v}(g_{v})
\tag{12.5.1.2}\\
&\;=\;M(\varphi)\big(|\cdot|_{F}^{1/2}\big)+M(\varphi)\big(|\cdot|_{F}^{-1/2}\big)
-\sum_{c,I}N(c)M(\varphi)\Big(c|\cdot|_{F}^{-1/2}\Big)
\tag{12.5.1.3}
\end{align}
$$

*where $q_{v}:=|\pi_{v}|_{v}^{-1}$, for $v\in\Sigma_{F,f}$ and $\pi_{v}$ any choice of uniformizer at $v$ of the non-Archimedean local field $F_{v}$,
and*

$$
M(\varphi)(c):=\int_{C_{F}}\varphi(g)c(g)\,\mathrm{d}\overline{\mu}(g)
$$

*is the Mellin transform of the test function $\varphi$, and $c\in\Omega(C_{F})$ varies over the zeros of the Hecke $L$-function
$c\mapsto L(c)$ contained in the interior of the relative vertical strip*

$$
\Omega(C_{F})_{I}=\{c\in\Omega(C_{F}):\sigma(c)\in 1/2+I\}.
$$

## PDF page 520

520    CHAPTER 12. TRACE FORMULA: GEOMETRIC SIDE

*The nonnegative integer $N(c)$ is the multiplicity of the zero $c$ of the Hecke $L$-function.*

Proof. We let $S$ be a finite set of places containing all the Archimedean places, the places of $F$ that
ramify over $\mathbf{Q}$, the places at which the character $\chi\in\widehat{C_{F}}$ is ramified, and such that $\mathrm{Pic}(\mathcal{O}_{F,S})=1$. We further
assume $S$ is large enough so as to arrange that the support $K$ of $\varphi$ satisfies $|K|_{F}\subset(1/T,T)$ with $T<N(\mathfrak{p}_{v})$
for every finite place $v\notin S$, with $\mathfrak{p}_{v}$ the unique prime ideal of $\mathcal{O}_{F}$ associated to $v$. Further assume that $S$ is so
large that $\varphi$ is invariant under the left-translation action on $\mathcal{D}(C_{F})$ of the image of $\prod_{v\notin S}\mathcal{O}_{F_{v}}^{\times}\subset\mathrm{GL}_{1}(\mathbf{A}_{F})$.

We compute the integral with respect to the global Haar measure $\overline{\mu}$ of the smoothened geometric kernel
$k:=\widetilde{k}^{\mathrm{geom}}_{\varphi,1/2,I,s}$ along the diagonal, denoted $k(x,x)$. By (11.3.1.4), this reads:

$$
\int_{C_{F}}k_{S}(x,x)\,\mathrm{d}\overline{\mu}(x)
+\sum_{p\nmid S}\int_{C_{F}}k_{p}(x,x)\,\mathrm{d}\overline{\mu}(x)
=\int_{C_{F}}k(x,x)\,\mathrm{d}\overline{\mu}(x)
$$

and by Theorem 11.3.2.1, each $\int_{C_{F}}k_{p}(x,x)\,\mathrm{d}\overline{\mu}(x)=0$ for all prime numbers $p$ that are not the prime residue
characteristic of any finite place contained in $S$.

By Theorem 12.4.1.1, we further have that $\int_{C_{F}}k_{S}(x,x)\,\mathrm{d}\overline{\mu}(x)$ equals the left side of (12.5.1.1) upon
subtracting $M(\varphi)\big(|\cdot|_{F}^{1/2}\big)+M(\varphi)\big(|\cdot|_{F}^{-1/2}\big)$.

For $I=[-\alpha,\alpha]$, we further have:

$$
\int_{C_{F}}k(x,x)\,\mathrm{d}\overline{\mu}(x)
=-\sum_{c,I}N(c)M(\varphi)\Big(c|\cdot|_{F}^{-1/2}\Big)
\tag{12.5.1.4}
$$

by design of the global geometric kernel (see Definition 10.4.3.7) and by Theorem 10.4.2.8.

Upon combining (12.5.1.4) with the foregoing, we deduce that the identity in (12.5.1.1) holds. $\square$
