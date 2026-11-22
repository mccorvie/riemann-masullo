## PDF page 587

APPENDIX B

**Preparations from Analytic Number Theory**

In this Appendix we collect some results from analytic number theory and cover them in the generality of all Hecke $L$-functions of an arbitrary number field.

We review classical facts on the growth of “finite” Hecke $L$-functions (i.e., without $\Gamma$-factors) over vertical strips, classical zero-free regions$^1$ for Hecke $L$-functions, and convergence of partial Euler products over the 1-line (i.e. the vertical line $\{\mathrm{Re}(s)=1\}$). We also discuss Weil’s own idelic formulation of the Explicit Formulas, incorporating Connes’ observations on the local Fourier transform in relation to Weil’s principal values.

| | |
|---|---:|
| B.1. Convexity bound on $L_f(s,\chi)$ | 588 |
| B.1.1. Growth order of $L_f(s,\chi)$ over the critical strip | 588 |
| B.1.1.1. Phragmen-Lindelöf and convexity bound on $L_f(\sigma+it,\chi)$. | 588 |
| B.2. Asymptotic Cauchy Integral Formula | 591 |
| B.2.1. Complements on the Mellin Transform | 592 |
| B.2.1.1. Schwartz functions with exponential and semi-exponential decay. | 592 |
| B.2.1.2. Asymptotic Expansions and Mellin Inversion. | 595 |
| B.2.2. Asymptotic Cauchy Integral Formula | 600 |
| B.2.2.1. Cauchy Integrals. | 600 |
| B.3. Asymptotic Residue Theorem | 604 |
| B.3.1. Slow growth near the poles | 604 |
| B.3.1.1. Polar locations and vertical growth. | 604 |
| B.3.2. The Asymptotic Residue Theorem | 605 |
| B.3.2.1. Residues over asymptotic contours. | 605 |
| B.4. Explicit Formulas for Hecke $L$-functions | 606 |
| B.4.1. Complements on Poisson Summation and Cauchy Integrals | 606 |
| B.4.1.1. Slow decay in the presence of isolated jump singularities | 607 |
| B.4.1.2. Cauchy Integrals of $\Phi(s)L'_v(\chi,s)/L_v(\chi,s)$ and weighted Dirac combs | 610 |
| B.4.2. Explicit formulas from the Asymptotic Residue Theorem | 614 |
| B.4.2.1. Logarithmic derivative of completed $L(s,\chi)$ and the Asymptotic Residue Formula. | 614 |
| B.4.2.2. Non-Archimedean local factors | 615 |
| B.4.2.3. Archimedean Local Factors | 615 |
| B.4.2.4. Explicit Formulas for Hecke $L$-functions | 616 |
| B.4.3. Fourier transform of $\log\lvert\cdot\rvert_v$ | 617 |
| B.4.3.1. Calculation of the additive local Fourier transform of $\log\lvert\cdot\rvert_v$ | 617 |
| B.4.4. Idelic Explicit Formulas | 619 |
| B.4.4.1. Weil’s Principal Values from the Explicit Formulas via additive local Fourier transform | 619 |
| B.4.4.2. Change of local additive character. | 621 |

$^{1}$perhaps omit this mention if in the end the discussion of zero-free regions is removed if not needed

587

## PDF page 588

588  CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY

| | |
|---|---:|
| B.4.4.3. Calculation of Weil’s Principal Values. | 622 |
| B.4.4.4. Reformulation of Weil’s Explicit Formulas | 623 |
| B.5. Recurrence and equidistribution | 626 |
| B.5.1. Preparations | 626 |
| B.5.2. Kronecker-Weyl | 627 |
| B.5.2.1. The classical Kronecker-Weyl Theorem | 627 |
| B.5.3. Strong recurrence of non-Archimedean Euler factors | 632 |
| B.5.3.1. Strong recurrence | 632 |
| B.5.3.2. Strong recurrence of reciprocal partial Euler products on open strips containing $i\mathbf{R}$ | 632 |
| B.5.3.3. Preparations on recurrence | 633 |
| B.5.3.4. Strong recurrence of reciprocal finite Euler products | 634 |
| B.6. Classical zero-free regions for Hecke $L$-functions | 636 |
| B.6.1. Zero-free regions for Hecke $L$-functions and estimates on $L'_f(s,\chi)/L_f(s,\chi)$ | 636 |
| B.6.1.1. Classical zero-free region for $L_f(s,\chi)$. | 636 |
| B.6.1.2. Estimates for $L'_f(s,\chi)/L_f(s,\chi)$. | 636 |
| B.6.1.3. Polynomial growth of the reciprocal finite Hecke $L$-function on the 1-line | 640 |
| B.7. Reciprocals and Partial Euler products on the 1-line | 643 |
| B.7.1. The Dirichlet polynomials of $L'_f(s,\chi)/L_f(s,\chi)$ on the 1-line | 643 |
| B.7.1.1. Logarithmic derivatives of finite Hecke $L$-functions. | 643 |
| B.7.1.2. A version of Perron’s Formula from Titchmarsh | 644 |
| B.7.1.3. Convergence and oscillation of the Dirichlet polynomials of $L'_f(s,\chi)/L_f(s,\chi)$ | 645 |
| B.7.2. Euler products on the 1-line. | 648 |
| B.7.2.1. Mode of convergence of partial Euler products on subsets of the 1-line | 649 |
| B.7.2.2. Uniform convergence away from the singularity | 651 |
| B.7.2.3. Partial Euler products on the 1-line | 652 |
| B.7.2.4. Convergence of partial Euler products on the 1-line away from the singularity | 653 |

**B.1. Convexity bound on $L_f(s,\chi)$**

In this section we record classical facts about growth bounds for Hecke $L$-functions and their derivatives.

**B.1.1. Growth order of $L_f(s,\chi)$ over the critical strip.** Recall that $L_f(s,\chi)$ is defined as

$$
L_f(s,\chi):=\prod_{\mathfrak{p}\subset\mathcal{O}_F}(1-\chi(\mathfrak{p})N(\mathfrak{p})^{-s})^{-1}
$$

for $\mathrm{Re}(s)>1$, where the product is indexed by the prime ideals of $\mathcal{O}_F$ (noting that $\chi(\mathfrak{p}):=0$ if $\chi$ is ramified at $v_{\mathfrak{p}}$). and is absolutely convergent for $\mathrm{Re}(s)>1$, uniformly on $\mathrm{Re}(s)\ge 1+\varepsilon$ for each $\varepsilon>0$.

The function $L_f(s,\chi)$ has a Dirichlet series expansion

$$
L_f(s,\chi)=\sum_{0\ne I\subset\mathcal{O}_F}\frac{\chi(I)}{N(I)^s}
$$

which is absolutely convergent for $\mathrm{Re}(s)>1$, uniformly on $\mathrm{Re}(s)\ge 1+\varepsilon$ for each $\varepsilon>0$, where $\chi(I):=0$ if $I$ is not coprime to the conductor of $\chi$.

B.1.1.1. *Phragmen-Lindelöf and convexity bound on $L_f(\sigma+it,\chi)$.* In this subsection we record the arguments to establish the classical polynomial growth bound on $L_f(1/2+it,\chi)$ for arbitrary continuous

## PDF page 589

B.1. CONVEXITY BOUND ON $L_f(s,\chi)$ · 589

characters $\chi\in\widehat{C_F}$ (i.e. $L(1/2+it,\chi)=O_{\varepsilon}(\lvert t\rvert^{1/4+\varepsilon})$ for every $\varepsilon>0$), the bound

$$
L_f(1+it,\chi)=O_{\varepsilon}(\lvert t\rvert^{\varepsilon})
$$

for every $\varepsilon>0$, and deduce the classical convexity bound $L_f(s,\chi)$ for $s\in\mathbf{C}_{[1/2,1]}$ from the Phragmen-Lindelöf Theorem.

The results in this subsection can be sharpened and have been so in the existing literature (see, for instance, [MVe, Thm. 5.1] for $\pi=1$). We will be requiring them only in the form and strength discussed below, which is classical and obtained by following the methods in [T2, Ch. V, §5.1].

We recall from [T1, Ch. 9, §9.41] that for $f(s)$ a meromorphic function on a half-plane $\mathbf{C}_{>a}$ whose poles, if any, are all contained within a horizontal vertically bounded strip within the complex $s$-plane, if $f$ is of finite order within $\mathbf{C}_{>a}$ (see [T1, Ch. 9, §9.4]) then we may define the function $\mu(\sigma)$ for $\sigma>a$ as the infimum of the real numbers $\xi\in\mathbf{R}_{\ge 0}$ such that

$$
f(\sigma+it)=O_{\sigma}(\lvert t\rvert^{\xi})
$$

as $\lvert t\rvert\to\infty$. The function $\mu$ is continuous and convex downwards as a consequence of the Phragmen-Lindelöf Theorem, as we’ll soon review. Its value is zero if $f$ is bounded on $\mathrm{Re}(s)=\sigma$.

In particular, if $f$ is an absolutely convergent Dirichlet series over $\mathbf{C}_{>b}$ with $b>a$ then $\mu(\sigma)=0$ for every $\sigma>b$, and hence $\mu(b+\varepsilon)=0$ for every $\varepsilon>0$ since any Dirichlet series which is absolutely convergent is also bounded over closed half-planes of absolute convergence. It follows that we have $\mu(b)=0$ by continuity. We refer the reader to [T1, Ch. 9, §9.41], where the continuity and downward convexity properties of $\mu(\sigma)$ are deduced from the Phragmen-Lindelöf Theorem. Since in [T1, Ch. 9, §9.41] such properties are only proved in the case $f$ is holomorphic over $\mathbf{C}_{>0}$, we include a discussion on the function $\mu$ and its properties below.

LEMMA B.1.1.1. *Let $a,b\in\mathbf{R}$ be real numbers, $a<b$, $f:\mathbf{C}_{>a}\to\mathbf{C}$ a meromorphic function. Assume:*

*(1) The poles of $f$ are simple and finitely many.*

*(2) There exists a real number $\xi>0$ such that*

(B.1.1.1)
$$
f(\sigma+it)\ll\lvert t\rvert^{\xi}
$$

*as $\lvert t\rvert\to+\infty$, uniformly with respect to $\sigma>a$.*

*Then for every $\sigma_1<\sigma_2\in(a,+\infty)$ the function*

(B.1.1.2)
$$
\mu(\sigma):=\inf\{k\in\mathbf{R}_{\ge 0}:f(\sigma+it)\ll\lvert t\rvert^k\text{ as }\lvert t\rvert\to\infty\}<\infty
$$

*satisfies*

(B.1.1.3)
$$
\mu(\sigma)\le t\mu(\sigma_2)+(1-t)\mu(\sigma_1)
$$

*for every $t\in[0,1]$ and $\sigma:=t\sigma_2+(1-t)\sigma_1\in[\sigma_1,\sigma_2]$. Moreover, $\mu$ is continuous as a function $(a,+\infty)\to\mathbf{R}_{\ge 0}$ and for all $\varepsilon>0$ we have $f(\sigma+it)=O_{\varepsilon,\sigma_1,\sigma_2}(\lvert t\rvert^{\mu(\sigma)+\varepsilon})$ as $\lvert t\rvert\to\infty$ uniformly in $\sigma\in[\sigma_1,\sigma_2]$.*

PROOF. Let $s_1,\dots,s_N$ be the poles of $f$. We consider the function

(B.1.1.4)
$$
g(s):=\prod_{1\le k\le N}(s-s_k)f(s)
$$

that is a holomorphic function over $\mathbf{C}_{>a}$ by assumption (1). We call $\mu_g$ the $\mu$-function of $g$, which is defined (and finite) by assumption (2).

We have $\mu_g(\sigma)=\mu(\sigma)+N$ for all $\sigma>a$. Indeed, we have $\mu_g(\sigma)\le\mu(\sigma)+N$ by definition, and since $\prod_{1\le k\le N}(s-s_k)$ is nowhere vanishing for all ordinates of large enough absolute value, and bounded above uniformly with respect to all such ordinates by a nonzero positive real number, the reverse inequality also holds.

## PDF page 590

590  CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY

Let $\varepsilon>0$, and choose arbitrary $\sigma_1,\sigma_2>a$ with $\sigma_1<\sigma_2$. Then as $\lvert t\rvert\to\infty$,

$$
\lvert g(\sigma_1+it)\rvert\ll\lvert t\rvert^{N+\mu(\sigma_1)+\varepsilon},\quad \lvert g(\sigma_2+it)\rvert\ll\lvert t\rvert^{N+\mu(\sigma_2)+\varepsilon}.
$$

By [T1, Ch. V, §5.65, pp. 180-1] (which applies since (B.1.1.1) implies that for all $\varepsilon>0$, $f(\sigma+it)=O(e^{\varepsilon\lvert t\rvert})$ as $\lvert t\rvert\to\infty$ uniformly $\sigma>a$), we deduce

$$
\lvert g(\sigma+it)\rvert\ll\lvert t\rvert^{k_{\varepsilon}(\sigma)}
$$

uniformly for all $\sigma\in[\sigma_1,\sigma_2]$ as $\lvert t\rvert\to\infty$, where

$$
k_{\varepsilon}(\sigma):=\frac{(\sigma_2-\sigma)(\mu_g(\sigma_1)+\varepsilon)+(\sigma-\sigma_1)(\mu_g(\sigma_2)+\varepsilon)}{\sigma_2-\sigma_1}=\frac{(\sigma_2-\sigma)(\mu(\sigma_1)+\varepsilon)+(\sigma-\sigma_1)(\mu(\sigma_2)+\varepsilon)}{\sigma_2-\sigma_1}+N+\varepsilon
$$

from which we deduce $\mu_g(\sigma)\le k_{\varepsilon}(\sigma)$ for all $\sigma\in[\sigma_1,\sigma_2]$. Since $\varepsilon>0$ is arbitrary, we may let $\varepsilon\to 0^+$ to obtain:

(B.1.1.5)
$$
\mu(\sigma)+N=\mu_g(\sigma)\le\lim_{\varepsilon\to 0^+}k_{\varepsilon}(\sigma)=\frac{(\sigma_2-\sigma)\mu(\sigma_1)+(\sigma-\sigma_1)\mu(\sigma_2)}{\sigma_2-\sigma_1}+N
$$

which gives

(B.1.1.6)
$$
\mu(\sigma)\le\frac{(\sigma_2-\sigma)\mu(\sigma_1)+(\sigma-\sigma_1)\mu(\sigma_2)}{\sigma_2-\sigma_1}.
$$

Upon calling $t:=(\sigma-\sigma_1)/(\sigma_2-\sigma_1)$ in (B.1.1.6), we see that (B.1.1.3) holds. Continuity of $\mu$ follows from (B.1.1.3) by [T1, Ch. V, §5.31].

$\square$

The following Lemma is [IK, Ch. 5, §5.1, Lemma 5.2, p. 97].

LEMMA B.1.1.2. *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. The finite Hecke $L$-function $L_f(s,\chi)$ is $O(\lvert t\rvert^{M_{\chi}})$ for some $M_{\chi}>0$ as $\lvert t\rvert\to\infty$ uniformly in $\sigma\in[a,b]$ for any fixed $a<b$.*

In light of Lemma B.1.1.2, the function $\mu$ is defined for every Hecke $L$-function. Moreover, since each $L_f(s,\chi)$ is defined by an absolutely convergent Dirichlet series over $\mathbf{C}_{>1}$ uniformly over $\mathrm{Re}(s)\ge 1+\varepsilon$, it satisfies $\mu(\sigma)=0$ for every $\sigma>1$ and hence $\mu(1)=0$ by continuity (see Lemma B.1.1.1 with $a<1$).

Recall that the function $\gamma(\chi,s)$ defined in (3.2.1.3) is a product of $\Gamma$-functions of the form

(B.1.1.7)
$$
L(\lvert\cdot\rvert_v^s):=\pi^{-s/2}\Gamma(s/2),\; L(\mathrm{sgn}\lvert\cdot\rvert_v^s)=\pi^{-(s+1)/2}\Gamma\left(\frac{s+1}{2}\right)
$$

for $v$ real and $\chi_v=1$, respectively $\chi_v=\mathrm{sgn}$, and

(B.1.1.8)
$$
L(\chi_v\lvert\cdot\rvert_v^s):=(2\pi)^{-(s+\frac{\lvert n\rvert}{2})}\Gamma\left(s+\frac{\lvert n\rvert}{2}\right)
$$

for $v$ complex and $\chi_v\lvert\cdot\rvert_v^s=\chi_{n,s}$, the continuous quasi-character character of $\mathbf{C}^{\times}$ defined as $(r,\theta)\mapsto r^s e^{in\theta}$. On $\mathbf{C}_{>0}$ the function $\gamma(\chi,s)$ is holomorphic and nowhere vanishing.

In light of Proposition 3.2.1.3 and (3.2.1.8)-(3.2.1.10), the finite Hecke $L$-function $L_f(s,\chi)$ extends to a meromorphic function on the complex $s$-plane and satisfies the functional equation

(B.1.1.9)
$$
L_f(s,\chi)=W(s,\chi)L_f(1-s,\chi^{-1}).
$$

where for $a,b\in\mathbf{R}$ with $a<b$ fixed arbitrary real numbers we have

(B.1.1.10)
$$
\lvert W(s,\chi)\rvert\ll_{a,b}\lvert t\rvert^{[F:\mathbf{Q}](\frac12-\sigma)}
$$

uniformly as $s=\sigma+it$ satisfies $\lvert t\rvert\to+\infty$ with $\sigma\in[a,b]$.

Up to a constant multiplier $W(\chi)$ of absolute value 1 (see [Neu, Ch. VII, Thm. 8.5]), the function $W(s,\chi)$ is equal to

(B.1.1.11)
$$
\lvert d_F\rvert^{\frac12-s}\frac{N(\mathfrak{f}_{\overline{\chi}})^{\frac{1-s}{2}}}{N(\mathfrak{f}_{\chi})^{\frac{s}{2}}}\frac{\gamma(\overline{\chi},1-s)}{\gamma(\chi,s)}
$$

## PDF page 591

**B.2. ASYMPTOTIC CAUCHY INTEGRAL FORMULA** · **591**

that is entire and with no zeros (see [Neu, Ch. VII, Prop. 4.4]). The estimate in (B.1.1.10) is obtained from the product structure of $W(s,\chi)$.

Proposition B.1.1.3 (Convexity Bound). *Let $F$ be a number field, $\chi$ a continuous character on $C_F$. For every $\varepsilon>0$, upon writing $\sigma:=\mathrm{Re}(s)$, we have uniformly in $\sigma\in[0,1]$:*$^2$

$$
L_f(s,\chi)\ll |t|^{[F:\mathbf{Q}]\frac{1-\sigma}{2}+\varepsilon} \tag{B.1.1.12}
$$

*as $|t|\to+\infty$, where the implied constant depends on $\chi$ and on $F$ but not on $\varepsilon$ nor $\sigma$.*

Proof. For $\sigma:=\mathrm{Re}(s)$, we have, for $\sigma<0$, $L_f(1-s,\chi^{-1})$ is given by an absolutely and locally uniformly convergent Dirichlet series, by the very design of the finite Hecke $L$-function from (3.2.1.7). In particular, $L_f(1-s,\chi^{-1})$ is bounded for $\sigma\le -\delta$ for any real number $\delta>0$. By the functional equation (see (B.1.1.9)) and Stirling's Approximation, giving (B.1.1.10), we have

$$
|L_f(s,\chi)|\sim |W(s,\chi)|\ll |t|^{[F:\mathbf{Q}]\left(\frac12-\sigma\right)}
$$

as $|t|\to+\infty$ while $s$ remains within a fixed and horizontally bounded vertical strip.

It follows that we have

$$
\mu(\sigma)\le [F:\mathbf{Q}]\left(\frac12-\sigma\right) \tag{B.1.1.13}
$$

for $\sigma<0$.

For any real number $\delta>0$, $L_f(s,\chi)$ is bounded for $\sigma\ge 1+\delta$, and hence $\mu(\sigma)=0$ for $\sigma>1$. By downward convexity of $\mu$ (see Lemma B.1.1.1), we deduce

$$
\mu(\sigma)\le (1-\sigma)\mu(0)+\sigma\mu(1)=[F:\mathbf{Q}]\left(\frac{1-\sigma}{2}\right). \tag{B.1.1.14}
$$

We deduce via the uniform growth bound at the end of Lemma B.1.1.1 that for every $\varepsilon>0$ we have that (B.1.1.12) holds, with an implied constant that depends only on $\chi$ and $F$. $\square$

Remark B.1.1.4 (Polynomial growth of the holomorphic derivatives). We note that from the functional equation

$$
L_f(s,\chi)=W(s,\chi)L_f(1-s,\chi^{-1})
$$

from (B.1.1.9), the holomorphic derivative $\partial_s^k L_f(s,\chi)$ of order $k\ge 0$ also grows polynomially on all vertical lines in $\mathbf{C}$.$^3$

Indeed, we have:

$$
\partial_s^k L_f(s,\chi)=\sum_{0\le m\le k}\binom{k}{m}(\partial_s^m W(s,\chi))(\partial_s^{k-m}L_f(1-s,\chi^{-1})) \tag{B.1.1.15}
$$

as meromorphic functions on $\mathbf{C}$. For $s\in\mathbf{C}_{>1}$, $\partial_s^k L_f(s,\chi)$ is an absolutely convergent Dirichlet series, and as such it is bounded on vertical lines within the half-plane $\mathbf{C}_{>1}$. For $s\in\mathbf{C}_{<0}$, we use (B.1.1.15) and boundedness on vertical lines of each $\partial_s^{k-m}L_f(1-s,\chi^{-1})$ to reduce to showing that $\partial_s^m W(s,\chi)$ grows polynomially over the complex $s$-plane$^4$ for all integers $m\ge 0$. This is indeed the case by Proposition 3.3.1.5 applied to $S=S_\infty$.

**B.2. Asymptotic Cauchy Integral Formula**

In this section we record arguments enabling the computation of the values of certain line integrals by contour integration, when the meromorphic functions involved are products of a slowly increasing meromorphic

$^2$Need to treat $\sigma\in[-1,2]$ for use in Theorem B.6.1.7.

$^3$Need to address uniform control with $\sigma\in[a,b]$ if needed elsewhere.

$^4$Is this really supposed to be about vertical strips of bounded width? With uniformity in $\sigma$?

## PDF page 592

**592** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

function and the Mellin transform of a Schwartz function supported over $\mathbf{R}_{>0}$ and which decays faster than any positive power of $e^{-|\log(t)|}$ as $|\log(t)|\to+\infty$.

**B.2.1. Complements on the Mellin Transform.** Recall the definition of the Hardy space $H^p(\mathbf{C}_{<a})$ of the half-plane $\mathbf{C}_{<a}=\{s\in\mathbf{C}:\mathrm{Re}(s)<a\}$, for each real number $p>0$: the space of holomorphic functions $\Phi(s)$ on $\mathbf{C}_{<a}$ such that

$$
\|\Phi\|_{H^p(\mathbf{C}_{<a})}:=\sup_{\sigma<a}\|\Phi(\sigma+iy)\|_{L^p(\mathbf{R},\mathrm{d}y)}<\infty.
$$

The assignment $\Phi\mapsto\|\Phi\|_{H^p(\mathbf{C}_{<a})}$ makes $H^p(\mathbf{C}_{<a})$ a complex Banach space for $p\ge 1$ (as can be deduced$^5$ from [Nik, Thm. 2.2.2(2)]), and in the case $p=2$ to a complex Hilbert space.

From [Dur, Cor. to Thm. 11.1], we note that for all $p>0$, the boundary function

$$
f_\Phi(y):=\lim_{\sigma\to a^-}\Phi(\sigma+iy)
$$

for each $\Phi\in H^p(\mathbf{C}_{<a})$ exists for almost all $y\in\mathbf{R}$, and it is an element of $L^p(\mathbf{R},\mathrm{d}y)$.

By [Dur, Cor. to Thm. 11.2, p. 190] we further have that the assignment $\Phi\mapsto f_\Phi$ is an isometric embedding of complex Banach spaces for $p\ge 1$:

$$
H^p(\mathbf{C}_{<a})\to L^p(\mathbf{R},\mathrm{d}y)
$$

since it is norm-preserving in this $p$-range. It is not surjective, and its image can be described (see$^6$ [Nik, Thm. 2.2.2(2)]).

It is a consequence of the defining conditions on the holomorphic functions on $\mathbf{C}_{<a}$ in the class $H^p(\mathbf{C}_{<a})$, for $p\ge 1$, that the following formulas hold: for every $a'\le a$ and every $z\in\mathbf{C}$ with $\mathrm{Re}(z)\ne a'$, we have

$$
\frac{1}{2\pi i}\int_{a'-i\infty}^{a'+i\infty}\frac{\Phi(s)}{s-z}\,\mathrm{d}s=\Phi(z)
$$

if $\mathrm{Re}(z)<a'$ and:

$$
\frac{1}{2\pi i}\int_{a'-i\infty}^{a'+i\infty}\frac{\Phi(s)}{s-z}\,\mathrm{d}s=0
$$

if $\mathrm{Re}(z)>a'$. This is [Dur, Ch.11, Thm.11.8].

In this section we provide formulas similar to those above, when the holomorphic function $\Phi(s)$ is not in the class $H^p(\mathbf{C}_{<a})$, but rather it satisfies certain decay properties towards infinity uniformly only on vertical strips$^7$ and not necessarily over the half-plane $\mathbf{C}_{<a}$. Such analogs will involve integrating over the vertical lines bounding a fixed vertical strips.

We will also be needing an asymptotic version of Cauchy's Residue Theorem, valid under the same assumptions on $\Phi(s)$ as above. The holomorphic functions $\Phi(s)$ we will be considering are Mellin transforms of Schwartz functions on the real line whose support is contained within $\mathbf{R}_{>0}$, which satisfy decay conditions towards both $\infty$ and $0$.

B.2.1.1. *Schwartz functions with exponential and semi-exponential decay.* We recall that a function $\phi:\mathbf{R}\to\mathbf{C}$ is Schwartz if and only if $\phi\in C^\infty(\mathbf{R})$ and

$$
\|\phi\|_{m,N}:=\sup_{x\in\mathbf{R}}(1+|x|^N)\,|\partial_x^m\phi(x)|<\infty
$$

for all integers $N,m\ge 0$.

The space of all Schwartz functions on $\mathbf{R}$ is denoted by $\mathcal{S}(\mathbf{R})$, topologized by the family of seminorm $\{\|\cdot\|_{m,N}\}_{m,N\ge 0}$. The locally convex space $\mathcal{S}(\mathbf{R}_{>0})$ of Schwartz-Bruhat functions on the real abelian Lie group

$^5$How? Give clearer reference. Maybe discuss passing from $\mathbf{C}_{<a}$ to $\mathbf{D}$ with $\sigma=y$ going over to concentric circles.

$^6$Need to explain how reference applies, including passing from $\mathbf{C}_{<a}$ to $\mathbf{D}$

$^7$Do you mean on $\{\sigma\le a-\varepsilon\}$? Clarify if issue is being bounded away from $\sigma=a$.

## PDF page 593

**B.2. ASYMPTOTIC CAUCHY INTEGRAL FORMULA** · **593**

$\mathbf{R}_{>0}$ is isomorphic to $\mathcal{S}(\mathbf{R})$ under the exponential map $\exp:\mathbf{R}\to\mathbf{R}_{>0}$, with the topology generated by the family of seminorms resulting from the exponential change of variables. Namely, for $\phi\in C^\infty(\mathbf{R}_{>0})$ the rapid decay condition is defined by

$$
\|\phi\|_{m,N}:=\sup_{t\in\mathbf{R}_{>0}}(1+|\log(t)|^N)\,|(t\partial_t)^m\phi(t)|<\infty
$$

for all $m,N\ge 0$.

We now define a subspace of $\mathcal{S}(\mathbf{R}_{>0})$ comprised of those functions that decay very rapidly towards both $\infty$ and $0$.

Definition B.2.1.1 (Schwartz-Bruhat functions on $\mathbf{R}_{>0}$ with (semi-)exponential decay). Let $\phi\in\mathcal{S}(\mathbf{R}_{>0})$ be a Schwartz-Bruhat function. Say $\phi$ has:

(1) *forward semi-exponential decay* if $\phi$ and its derivatives decay faster than any positive power of $t^{-1}$ as $t\to+\infty$. We denote by $\mathcal{S}_{\mathrm{SE}}(\mathbf{R}_{>0})$ the space of $\phi$'s with foward semi-exponential decay. Likewise say $\phi$ has *backward semi-exponential decay* if $\phi$ and its derivatives decay faster than any positive power of $t$ as $t\to 0^+$. We denote by $\check{\mathcal{S}}_{\mathrm{SE}}(\mathbf{R}_{>0})$ the space of $\phi$'s with backward semi-exponential decay.

(2) *exponential decay* if $\phi$ and its derivatives decay faster than any positive power $e^{-|\log(t)|}$, as $|\log(t)|\to+\infty$. We denote by $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ the $\mathbf{C}$-linear space of Schwartz-Bruhat functions of exponential decay.

Remark B.2.1.2. The role of applying $\partial_t$ in the preceding definition can be replaced by applying $t\partial_t$; the latter has the merit of being invariant and negating under inversion on $t$. It is elementary to check that membership in $\mathcal{S}_{\mathrm{SE}}(\mathbf{R}_{>0})$ is equivalent to the requirement $t^a\phi\in\mathcal{S}(\mathbf{R}_{>0})$ for all $a\ge 0$, and via the exponential isomorphism $\mathbf{R}\simeq\mathbf{R}_{>0}$ this corresponds to functions $f\in\mathcal{S}(\mathbf{R})$ such that $f^{(j)}\in O(e^{-x})$ as $x\to+\infty$ for all $j\ge 0$.

We will often abbreviate "forward exponential decay" into "exponential decay", when no confusion is expected to arise.$^8$

Remark B.2.1.3. The notion of "polynomial growth" over $\mathbf{R}_{>0}$ is defined via the usual concept for functions on the real line upon performing the exponential change of variables $t=e^x$: a function $f:\mathbf{R}_{>0}\to\mathbf{C}$ has at most polynomial growth over $\mathbf{R}_{>0}$ if for every integer $N\ge 0$ there exists a real number $C_N>0$ such that $|f(t)|\le C_N|\log(t)|^N$.

Lemma B.2.1.4. *Let $\phi\in\mathcal{S}(\mathbf{R}_{>0})$ be a Schwartz-Bruhat function. We define $\check{\phi}$ the function on $\mathbf{R}_{>0}$ assigned by:*

$$
\check{\phi}(t):=\phi(1/t) \tag{B.2.1.1}
$$

*for $t\in\mathbf{R}_{>0}$ (so $\phi\in \mathcal{S}_{\mathrm{E}}(\mathbf{R})$ if and only if $\check{\phi}\in \mathcal{S}_{\mathrm{E}}(\mathbf{R})$),*

*(1) If $\phi\in\check{\mathcal{S}}_{\mathrm{SE}}(\mathbf{R}_{>0})$ then the extension of $\phi$ to $\mathbf{R}$ by zero for $t\in(-\infty,0]$ is Schwartz over $\mathbf{R}$.*

*(2) The involution $\phi\mapsto\check{\phi}$ is a linear topological automorphism of $\mathcal{S}(\mathbf{R}_{>0})$ respecting the linear subspace $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$, and identifying $\mathcal{S}_{\mathrm{SE}}(\mathbf{R}_{>0})$ with $\check{\mathcal{S}}_{\mathrm{SE}}(\mathbf{R}_{>0})$.*

*(3) The extension by zero of any function in $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$ to the real line is Schwartz.*

*(4) The operator $t\partial_t$ on $\mathcal{S}(\mathbf{R}_{>0})$ preserves $\mathcal{S}_{\mathrm{SE}}(\mathbf{R}_{>0})$, $\check{\mathcal{S}}_{\mathrm{SE}}(\mathbf{R}_{>0})$, and $\mathcal{S}_{\mathrm{E}}(\mathbf{R}_{>0})$.*

Proof. (1) : We need to check smoothness at $t=0$ of $\partial_t^N\phi$ for every integer $N\ge 0$. We know that $\partial_t^N\phi$ exists and is smooth over $\mathbf{R}^\times$. It is therefore enough to check that it is continuous at $t=0$: that says $\partial_t^N\phi\to 0$ as $t\to 0^+$ for each $N$. For $t=e^x$ we have $\partial_t=e^{-x}\partial_x$, so we are given that $f(x):=\phi(e^x)\in\mathcal{S}(\mathbf{R})$ and its derivatives all have decay more rapid than $e^{-M|x|}$ as $x\to-\infty$ for each $M>0$ and we want to show

$^8$Can such abuse of terminology be avoided, as it will cause confusion, and then remove this sentence?

## PDF page 594

**594** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

$(e^{-x}\partial_x)^N f\to 0$ as $x\to-\infty$. Via the product rule, $(e^{-x}\partial_x)^N=e^{-Nx}(\sum_{j=1}^N a_{j,N}\partial_x^{i} j)$ for some constants $a_{j,N}$, the desired decay as $x\to-\infty$ clearly holds.

(2) and (3) follow from the definitions and from (1).

(4) : If $\phi\in \mathcal{S}_{\mathrm{SE}}(\mathbf{R}_{>0})$ then for any real number $A>0$, we have $t^A\phi\in\mathcal{S}(\mathbf{R}_{>0})$. It follows that $(t\partial_t)(t^A\phi)\in\mathcal{S}(\mathbf{R}_{>0})$. But $(t\partial_t)(t^A\phi)=At^A\phi+t^A(t\partial_t)\phi\in\mathcal{S}(\mathbf{R}_{>0})$, which gives $t^A(t\partial_t)\phi\in\mathcal{S}(\mathbf{R}_{>0})$. It follows that $(t\partial_t)\phi$ has semi-exponential decay. The same assertion holds for backward semi-exponential decay (by passing to $1/t$) and exponential decay in place of semi-exponential decay. $\square$

Let $\phi:\mathbf{R}_{>0}\to\mathbf{C}$ be a measurable function, and $s\in\mathbf{C}$. We define the Mellin transform $M(\phi)$ by

$$
M(\phi)(s):=\int_{\mathbf{R}_{>0}}\phi(t)t^s\,\frac{\mathrm{d}t}{t} \tag{B.2.1.2}
$$

for $s\in\mathbf{C}$ when the integrand is absolutely integrable over $\mathbf{R}_{>0}$.

We will be discussing the regularity properties of $M(\phi)(s)$ when $\phi$ is a Schwartz function on the real line with semi-exponential decay, respectively exponential decay.

Proposition B.2.1.5. *Let $\phi$ be a Schwartz-Bruhat function on $\mathbf{R}_{>0}$ with forward semi-exponential decay. Let $a,b$ be real numbers with $0<a<b$.*

*The Mellin transform $M(\phi)$ defined by*

$$
\Phi(s):=\int_{\mathbf{R}_{>0}}\phi(t)t^s\,\frac{\mathrm{d}t}{t} \tag{B.2.1.3}
$$

*is absolutely convergent for all $s\in\mathbf{C}_{>0}$ and:*

*(1) $\Phi$ is holomorphic over the half-plane $\mathbf{C}_{>0}$.*

*(2) For every integer $N\ge 1$, there exists a real number $C_{N,a,b}$ depending only on $N,a,b,\phi$ (but not $y$) such that for every $a\le\sigma\le b$ and every $y\ne 0$, we have:*

$$
|\Phi(\sigma+iy)|\le C_{N,a,b}|y|^{-N}. \tag{B.2.1.4}
$$

*In particular, as a function of $y\in\mathbf{R}$ and uniformly in $\sigma\in[a,b]$ the value $\Phi(\sigma+iy)$ decays faster than any positive power of $|y|^{-1}$ as $|y|\to+\infty$.*

*(3) For every real number $p\ge 1$, for every integer $N>1$, there exists a real number $B_{N,a,b}>0$ depending also on $\phi$ such that for every $a\le\sigma\le b$, we have the inequality:*

$$
\|\Phi(\sigma+iy)\|_{L^p(\mathbf{R},\mathrm{d}y)}\le\left\{B_{N,a,b}^p+C_{N,a,b}^p\int_{|y|\ge 1/2}\frac{1}{|y|^{pN}}\,\mathrm{d}y\right\}^{1/p}. \tag{B.2.1.5}
$$

To prove this, we need the following:

Lemma B.2.1.6. *Let $\phi\in C^\infty(\mathbf{R}_{>0})$ be a smooth function. For every integer $N\ge 1$, we have:*

$$
((t\partial_t)^N\phi)(e^x)=\partial_x^N(\phi(e^x)) \tag{B.2.1.6}
$$

*as smooth functions of $x\in\mathbf{R}$.*

Proof. The identity in (B.2.1.6) for $N=1$ is the Chain Rule, and for $N>1$ it holds by induction. $\square$

Proof of Proposition B.2.1.5. The absolute integrability for $M(\phi)(s)$ with all $s\in\mathbf{C}_{>0}$ is clear near $t=0$ since $\mathrm{Re}(s)>0$, and near $t=\infty$ it follows from the forward semi-exponential decay hypothesis on $\phi$.

(1) : For holomorphicity on $\mathbf{C}_{>0}$ we want to use differentiation under the integral sign and so must analyze integrability near $0$ and near $\infty$ after applying $\mathrm{d}/\mathrm{d}s$ to the integrand. For $\int_0^1$ the $s$-differentiated integrand is absolutely integrable since $\phi(t)$ decays faster than $|\log(t)|^{-m}$ for all $m\ge 0$ as $t\to 0^+$. For $\int_1^\infty$, the forward semi-exponential decay hypothesis on $\phi$ does the job (even allowing all $s\in\mathbf{C}$, not just $s\in\mathbf{C}_{>0}$).

## PDF page 595

**B.2. ASYMPTOTIC CAUCHY INTEGRAL FORMULA** · **595**

(2) : We have, by (B.2.1.6) from Lemma B.2.1.6, for every integer $N\ge 1$:

$$
((t\partial_t)^N\phi)(e^x)=\partial_x^N(\phi(e^x))
$$

as smooth functions of $x\in\mathbf{R}$.

For every integer $N\ge 1$, every $\sigma>0$, and every $y\ne 0$, we have:

$$
\Phi(\sigma+iy)=\int_{\mathbf{R}}\phi(e^x)e^{(\sigma+iy)x}\,\mathrm{d}x=\frac{(-1)^N}{(\sigma+iy)^N}\int_{-\infty}^{+\infty}\partial_x^N(\phi(e^x))e^{(\sigma+iy)x}\,\mathrm{d}x. \tag{B.2.1.7}
$$

To see this, we observe that (B.2.1.7) holds for $N=1$ by integration by parts, noting that the integral converges since $\partial_x(\phi(e^x))=(t\partial_t\phi)(e^x)$ is Schwartz on the real line and decays faster than any positive power of $e^{-x}$ as $x\to+\infty$ by the forward semi-exponential decay hypothesis. Then one inducts on $N\ge 1$.

For all $0<a\le\sigma\le b$ we deduce

$$
|\Phi(\sigma+iy)|\le\frac{1}{(\sigma^2+y^2)^{N/2}}\int_{-\infty}^{+\infty}|\partial_x^N(\phi(e^x))|e^{\sigma x}\,\mathrm{d}x \tag{B.2.1.8}
$$

and upon defining

$$
C_{N,a,b}:=\int_0^{+\infty}|\partial_x^N(\phi(e^x))|e^{bx}\,\mathrm{d}x+\int_{-\infty}^0|\partial_x^N(\phi(e^x))|e^{ax}\,\mathrm{d}x \tag{B.2.1.9}
$$

(finite since $\partial_x^N(\phi(e^x))$ decays faster than all $e^{-mx}$ as $x\to\infty$ (with $m\ge 0$) and is bounded as $x\to-\infty$) that for all $y\ne 0$ and all $0<a\le\sigma\le b$ we have

$$
|\Phi(\sigma+iy)|\le C_{N,a,b}|y|^{-N}. \tag{B.2.1.10}
$$

(3) : We have, for every $y\in\mathbf{R}$ (allowing $y=0$) and every $a\le\sigma\le b$:

$$
|\Phi(\sigma+iy)|\le\|\phi(e^x)e^{bx}\|_{L^1([0,+\infty),\mathrm{d}x)}+\|\phi(e^x)e^{ax}\|_{L^1((-\infty,0],\mathrm{d}x)} \tag{B.2.1.11}
$$

and hence, upon calling $B_{N,a,b}$ the right side of (B.2.1.11), we deduce from (B.2.1.11) and (B.2.1.10) the inequality

$$
|\Phi(\sigma+iy)|\le B_{N,a,b}\cdot\mathrm{1}_{|y|<1/2}(y)+\frac{C_{N,a,b}}{|y|^N}\cdot\mathrm{1}_{|y|\ge 1/2}(y) \tag{B.2.1.12}
$$

for all $a\le\sigma\le b$. We deduce from (B.2.1.12) that for every $p\ge 1$, upon choosing $N>1$:

$$
\|\Phi(\sigma+iy)\|_{L^p(\mathbf{R},\mathrm{d}y)}\le\left\{B_{N,a,b}^p+C_{N,a,b}^p\int_{|y|\ge 1/2}\frac{1}{|y|^{pN}}\,\mathrm{d}y\right\}^{1/p} \tag{B.2.1.13}
$$

for all $a\le\sigma\le b$. $\square$

B.2.1.2. *Asymptotic Expansions and Mellin Inversion.* The following result encodes meromorphic continuation of $M(\phi)$ to a wider strip in terms of asymptotic expansion conditions on $\phi$.$^9$

Theorem B.2.1.7 (Asymptotic Expansions and Mellin Inversion - I). *Pick $a\in\mathbf{R}_{>0}$ and $b\in\mathbf{R}_{>0}\cup\{+\infty\}$ with $a<b$. Pick $\phi\in C^\infty(\mathbf{R}_{>0})$ such that $t^\sigma\cdot\phi\in\mathcal{S}(\mathbf{R}_{>0})$ for every $\sigma\in(a,b)$ (so the integral $M(\phi)(s)$ is absolutely convergent and holomorphic in $s$ on $\mathbf{C}_{(a,b)}$).*

*Let $\Sigma\subset\mathbf{C}$ be a finite set of points with an associated finite multiplicity $m_\alpha\ge 1$ for each $\alpha\in\Sigma$. Let $A<0$ be a real number such that $-\Sigma\subset\mathbf{C}_{(A,a]}$.*

*(1) Assume:*

*(a) $M(\phi)(s)$ from (B.2.1.2) admits a meromorphic continuation $f$ over $\mathbf{C}_{(A,b)}$ with a pole at $s=-\alpha$ of order $m_\alpha$ for each $\alpha\in\Sigma$ and no other poles,*

$^9$Originally there were references given to [HL, §2], but this seems useless since the referenced items include no proofs!

## PDF page 596

**596** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

*(b) $\varepsilon>0$ is a real number such that $A+\varepsilon<0$ and $f$ has no pole over $\mathbf{C}_{(A,A+\varepsilon]}$,*

*(c) there exists $\beta>1$ such that $|s|^\beta|f(s)|$ is bounded over $\mathbf{C}_{[A+\varepsilon/2,B]}$ for some real number $B\in(a,b)$.*

*Then for some $c_{\alpha,k}\in\mathbf{C}$ for $1\le k\le m_\alpha$ with $c_{\alpha,m_\alpha}\ne 0$ for all $\alpha$, as $t\to 0^+$ we have*

$$
\phi(t)-\sum_{\alpha\in\Sigma}\sum_{1\le k\le m_\alpha}c_{\alpha,k}t^\alpha(\log(t))^{k-1}=O_\varepsilon(t^{-A-\varepsilon}). \tag{B.2.1.14}
$$

*(2) Assume for each $\alpha\in\Sigma$ there exist $c_{\alpha,k}\in\mathbf{C}$ for $1\le k\le m_\alpha$ with $c_{\alpha,m_\alpha}\ne 0$ for all $\alpha$ such that as $t\to 0^+$,*

$$
\phi(t)-\sum_{\alpha\in\Sigma}\sum_{1\le k\le m_\alpha}c_{\alpha,k}t^\alpha(\log(t))^{k-1}=O(t^{-A}). \tag{B.2.1.15}
$$

*Then $M(\phi)(s)$ admits a meromorphic function over $\mathbf{C}_{(A,b)}$ with a pole at $s=-\alpha$ of order $m_\alpha$.*

*[Figure, redrawn from the PDF, p. 596:]*

```latex
\begin{tikzpicture}[x=1.5cm,y=1.2cm,>=stealth,mid/.style={decoration={markings,mark=at position 0.55 with {\arrow[scale=1.4]{>}}},postaction={decorate}},midv/.style={decoration={markings,mark=at position 0.66 with {\arrow[scale=1.4]{>}}},postaction={decorate}}]
\draw[<->] (-1,0) -- (2.6,0);
\draw[<->] (0.8,-1.9) -- (0.8,1.9);
\draw[mid] (0, 1.5) -- (2, 1.5);
\draw[midv] (0, -1.5) -- (0, 1.5);
\draw[mid] (0, -1.5) -- (2, -1.5);
\draw[midv] (2, -1.5) -- (2, 1.5);
\fill (0,1.5) circle (1.5pt) node[left] {$A+\varepsilon+iT$};
\fill (2,1.5) circle (1.5pt) node[right] {$\beta+iT$};
\fill (0,0) circle (1.5pt) node[above left] {$A+\varepsilon$};
\fill (2,0) circle (1.5pt) node[above right] {$\beta$};
\fill (0,-1.5) circle (1.5pt) node[left] {$A+\varepsilon-iT'$};
\fill (2,-1.5) circle (1.5pt) node[right] {$\beta-iT'$};
\fill (0.8,0) circle (1.5pt) node[above left] {$0$};
\end{tikzpicture}
```

FIGURE 1. A contour with upward vertical sides in $\sigma=A+\varepsilon<0$ and $\sigma=\beta>1$

Proof. (1) : Consider integration along the contour in Figure 1. Applying the Residue Theorem, we can use (a) and (c) (with $\beta>0$) to see that the contributions along the top and bottom sides decay to $0$ as $T,T'\to\infty$, yielding

$$
\frac{1}{2\pi i}\int_{B-i\infty}^{B+i\infty}f(s)t^{-s}\,\mathrm{d}s=\sum_{\alpha\in\Sigma}\mathrm{Res}_{s=-\alpha}(f(s)t^{-s})+\frac{1}{2\pi i}\int_{A+\varepsilon-i\infty}^{A+\varepsilon+i\infty}f(s)t^{-s}\,\mathrm{d}s \tag{B.2.1.16}
$$

with the vertical integrals on both sides absolutely convergent since $\beta>1$ in (c). The left integral as a function of $t$ is $\phi(t)$ by Fourier inversion (using the change of variables $t=e^x$), and the right integral is $O_\varepsilon(t^{-A-\varepsilon})$ as $t\to 0^+$.

Letting $a_k(f,-\alpha)$ be the coefficient of $(s+\alpha)^{-k}$ in the Laurent series expansion of $f(s)$ at $s=-\alpha$ (so this is nonzero when $k=m_\alpha$), we compute

$$
\mathrm{Res}_{s=-\alpha}(f(s)t^{-s})=\sum_{1\le k\le m_\alpha}a_k(f,-\alpha)\frac{(-1)^{k-1}}{(k-1)!}t^\alpha(\log(t))^{k-1}.
$$

Defining

$$
c_{\alpha,k}:=a_k(f,-\alpha)\frac{(-1)^{k-1}}{(k-1)!},
$$

we obtain (B.2.1.14).

(2) : We write

$$
\psi(t):=\phi(t)-\mathrm{1}_{(0,1]}(t)\sum_{\alpha\in\Sigma}\sum_{1\le k\le m_\alpha}c_{\alpha,k}t^\alpha(\log(t))^{k-1} \tag{B.2.1.17}
$$

## PDF page 597

**B.2. ASYMPTOTIC CAUCHY INTEGRAL FORMULA** · **597**

for $t>0$ and note that $\psi$ is smooth away from $t=1$. If (B.2.1.15) holds then the integral

$$
\int_0^\infty t^s\psi(t)\,\frac{\mathrm{d}t}{t} \tag{B.2.1.18}
$$

converges absolutely and uniformly on the compact subsets of the vertical strip $\mathbf{C}_{(A,b)}$ (so it is holomorphic on that strip).

For $z\in\mathbf{C}_{>0}$ and any integer $k\ge 0$, it is elementary to verify that

$$
\int_0^1 t^z(\log t)^k\,\frac{\mathrm{d}t}{t}=\int_{-\infty}^0 e^{zx}x^k\,\mathrm{d}x=\frac{(-1)^k\,k!}{z^{k+1}}
$$

(the final equality using induction on $k$ via either $z$-differentiation under the integral sign or integration by parts). Thus, for $\mathrm{Re}(s)>-\mathrm{Re}(\Sigma)$, so $\mathrm{Re}(s+\alpha)>0$ for all $\alpha\in\Sigma$, the value of the integral in (B.2.1.18) is

$$
g(s):=M(\phi)(s)-\sum_{\alpha\in\Sigma}\sum_{1\le k\le m_\alpha}\frac{c_{\alpha,k}(-1)^{k-1}\,(k-1)!}{(s+\alpha)^k}
$$

but $g(s)=M(\psi)(s)$ is holomorphic over $\mathbf{C}_{(A,b)}$, so we get a meromorphic continuation of $M(\phi)$ over that same strip with poles exactly at $-\Sigma$ with pole-order $m_\alpha$ at $-\alpha$ for each $\alpha\in\Sigma$. $\square$

For any integer $m\ge 0$, define

$$
C_0^m(\mathbf{R}_{>0}):=\{f\in C^m(\mathbf{R}_{>0}):\partial_x^k(f(e^x))\in C_0(\mathbf{R})\ \text{for all}\ 0\le k\le m\} \tag{B.2.1.19}
$$

a Banach space equipped with the norm $f\mapsto\|f\|_m:=\sum_{0\le k\le m}\|(t\partial_t)^k f\|_u$ (a sum of sup-norms over $\mathbf{R}_{>0}$).

These arise in the following result that is a partial converse to Theorem B.2.1.7.

Proposition B.2.1.8 (Asymptotic Expansions and Mellin Inversion - II). *Pick $a\in\mathbf{R}_{>0}$, $b\in\mathbf{R}_{>0}\cup\{\infty\}$ with $a<b$. Let $N>2$ be a real number. Let $f:\mathbf{C}_{(a,b)}\to\mathbf{C}$ be a holomorphic function such that $|s|^N|f(s)|$ is bounded on each closed strip of bounded width contained inside $\mathbf{C}_{(a,b)}$.*

*Then for any integer $0\le m<N-1$ there exists $\phi\in C^m(\mathbf{R}_{>0})$ such that $t^\sigma\cdot\phi\in C_0^m(\mathbf{R}_{>0})\cap L^2(\mathbf{R}_{>0},\mathrm{d}t/t)$ for all $\sigma\in(a,b)$ and the integral defining $M(\phi)(s)$ is absolutely convergent over $\mathbf{C}_{(a,b)}$ and equal to $f(s)$.*

Proof. Since $N>1$, we deduce that $f|_{\sigma+i\mathbf{R}}\in L^2(\mathbf{R},\mathrm{d}x)\cap L^1(\mathbf{R},\mathrm{d}x)$ for every $\sigma\in(a,b)$. It follows that we have $|s|^k|f(s)|^2$ is integrable on every vertical line of $\mathbf{C}_{(a,b)}$ for $0\le k\le N$.

For every $\sigma\in(a,b)$, on $\mathbf{R}_{>0}$ the Fourier transform $\phi_\sigma(x):=\frac{1}{2\pi i}\int_{-\infty}^{+\infty}f(\sigma+i\tau)x^{-i\tau}\,\mathrm{d}\tau$ of $f|_{\sigma+i\mathbf{R}}$ (which indeed is given by the integral $\frac{1}{2\pi i}\int_{-\infty}^{+\infty}f(\sigma+i\tau)x^{-i\tau}\,\mathrm{d}\tau$, by absolute integrability of $f$ on $\sigma+i\mathbf{R}$) therefore satisfies $\phi_\sigma\in C_0^m(\mathbf{R}_{>0})$ for all integers $0\le m<N-1$ via $x$-differentiation under the integral sign and the Riemann-Lebesgue Lemma. Each $\phi_\sigma$ is itself square-integrable by Plancherel's Theorem (see [Fol, Thm. 8.29]). By using the Cauchy integral formula for $f(s)x^{-s}$ on rectangles with vertical edges along $\mathrm{Re}(s)=\sigma,\sigma'\in(a,b)$ and heights $T,-T'$ with $T,T'\to\infty$, the decay $f(s)=O(|s|^{-N})$ ensures $x^{-\sigma}\phi_\sigma(x)=x^{-\sigma'}\phi_{\sigma'}(x)$ for all $x>0$; call this $\phi(x)$.

We claim $\phi_\sigma$ is absolutely $(\mathrm{d}t/t)$-integrable over $\mathbf{R}_{>0}$ for all $\sigma\in(a,b)$. Granting this for now, for all $\sigma\in(a,b)$ the inverse Fourier transform of $\phi_\sigma$ is given by $\int_{\mathbf{R}_{>0}}\phi_\sigma(t)t^{ix}\,\frac{\mathrm{d}t}{t}$ as a function of $x\in\mathbf{R}$, and this function belongs to $C_0(\mathbf{R})$. Thus, we have

$$
M(\phi)(\sigma+ix):=\int_{\mathbf{R}_{>0}}\phi(t)t^{\sigma+ix}\,\frac{\mathrm{d}t}{t}=\int_{\mathbf{R}_{>0}}\phi_\sigma(t)t^{ix}\,\frac{\mathrm{d}t}{t}=f(\sigma+ix)
$$

for all $x\in\mathbf{R}$, where the integrand defining $M(\phi)$ is absolutely integrable and the final equality initially holds initially only for $\mathrm{d}x$-almost all $x$ but then holds for all $x$ since both sides are continuous in $x$. This yields that over $\mathbf{C}_{(a,b)}$ the Mellin transform $M(\phi)$ is an absolutely convergent integral that coincides with the holomorphic $f$.

## PDF page 598

**598** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

It remains to show $\int_{\mathbf{R}_{>0}}|\phi_\sigma(t)|\,\mathrm{d}t/t<\infty$ for all $\sigma\in(a,b)$. Since $f$ is holomorphic over $\mathbf{C}_{(a,b)}$, Lemma D.3.1.1 applies $f$ and each of the finitely many integers $0\le m\le N$ to give that each holomorphic derivative $\partial_s^k f$ on $\mathbf{C}_{(a,b)}$ satisfies

$$
|s^m\partial_s^k f(s)|\le A_{k,J} \tag{B.2.1.20}
$$

on $\mathbf{C}_J$ for each closed bounded subinterval $J\subset(a,b)$, for some constant $A_{k,J}$ (which also depends on $f$). In particular, since we can use $m=2$ (as $N\ge 2$), we see that each $\partial_s^k f$ is absolutely integrable on each vertical line in $\mathbf{C}_{(a,b)}$.

We claim

$$
\frac{1}{2\pi i}\int_{-\infty}^{+\infty}(\partial_s^2 f)(\sigma+i\tau)t^{-i\tau}\,\mathrm{d}\tau=(\log(t))^2\phi_\sigma(t) \tag{B.2.1.21}
$$

as functions of $t\in\mathbf{R}_{>0}$. To see this, we proceed as follows. As holomorphic functions of $s\in\mathbf{C}_{(a,b)}$ we have

$$
\partial_s(f(s)t^{-s})=(\partial_s f)t^{-s}-(\log(t))f(s)t^{-s}
$$

with $s^2\partial_s f$ and $s^2 f(s)$ bounded on each $\mathbf{C}_J$, and $t^{-s}$ is clearly bounded on each $\mathbf{C}_J$. Integrating over $[\sigma-iT,\sigma+iT]$ for any $T>0$ then gives

$$
\frac{1}{2\pi i}\int_{\sigma-iT}^{\sigma+iT}(\partial_s f)(s)t^{-s}\,\mathrm{d}s=\log(t)\frac{1}{2\pi i}\int_{\sigma-iT}^{\sigma+iT}f(s)t^{-s}\,\mathrm{d}s+\frac{1}{2\pi i}\left\{(\partial_s f)(\sigma+iT)t^{-\sigma-iT}-(\partial_s f)(\sigma-iT)t^{-\sigma+iT}\right\}, \tag{B.2.1.22}
$$

and then letting $T$ tends to $+\infty$ yields

$$
\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}(\partial_s f)(s)t^{-s}\,\mathrm{d}s=\log(t)\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}f(s)t^{-s}\,\mathrm{d}s. \tag{B.2.1.23}
$$

As a consequence of Lemma D.3.1.1 and as observed above, we may replace $f$ with $\partial_s f$ and so obtain:

$$
\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}(\partial_s^2 f)(s)t^{-s}\,\mathrm{d}s=\log(t)^2\frac{1}{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}f(s)t^{-s}\,\mathrm{d}s=\log(t)^2 t^{-\sigma}\phi_\sigma(t). \tag{B.2.1.24}
$$

Multiplying both sides by $t^\sigma$ then gives (B.2.1.21).

From (B.2.1.21), upon breaking up the integration over $\mathbf{R}$ into integration over $[-1,1]$ and its complement, multiplying and dividing the integrand by $(\sigma+i\tau)^2$ in the latter integral (over that complement) yields

$$
|(\log(t))^2\phi_\sigma(t)|\le\frac{1}{2\pi}\int_{-1}^1|\partial_s^2 f(\sigma+i\tau)|\,\mathrm{d}\tau+\frac{A_{2,\{\sigma\}}}{2\pi}\int_{|\tau|>1}\frac{1}{\sigma^2+\tau^2}\,\mathrm{d}\tau \tag{B.2.1.25}
$$

for all $t\in\mathbf{R}_{>0}$. Thanks to this constant upper bound (depending on $\sigma$), the desired absolute $(\mathrm{d}t/t)$-integrability of $\phi_\sigma$ over $\mathbf{R}_{>0}$ reduces to that of $1/\log(t)^2$ is over $[2,+\infty)$ and $(0,1/2]$, and those are readily verified. $\square$

Proposition B.2.1.9. *Let $\phi$ be a Schwartz-Bruhat function on $\mathbf{R}_{>0}$ with exponential decay. Let $\Phi$ denote the Mellin transform $M(\phi)$, i.e. the complex valued function of $s\in\mathbf{C}$:*

$$
\Phi(s):=\int_{\mathbf{R}_{>0}}\phi(t)t^s\,\frac{\mathrm{d}t}{t}. \tag{B.2.1.26}
$$

*Let $a,b$ be arbitrary real numbers with $a<b$. Then:*

*(1) $\Phi$ is entire.*

*(2) For every integer $N\ge 1$, there exists a real number $C_{N,a,b}$ depending only on $N,a,b$, and $\phi$ such that for every $a\le\sigma\le b$ and every $y\ne 0$, we have:*

$$
|\Phi(\sigma+iy)|\le C_{N,a,b}|y|^{-N}. \tag{B.2.1.27}
$$

*In particular, as a function of $y\in\mathbf{R}$, for each $\sigma\in\mathbf{R}$, $\Phi(\sigma+iy)$ decays faster than any positive power of $|y|^{-1}$ as $|y|\to+\infty$.*

## PDF page 599

**B.2. ASYMPTOTIC CAUCHY INTEGRAL FORMULA** · **599**

*(3) For every real number $p\ge 1$ and any integer $N>1$, we have the inequality:*

$$
\|\Phi(\sigma+iy)\|_{L^p(\mathbf{R},\mathrm{d}y)}\le\left\{\|\phi(t)e^{(\max\{|a|,|b|\}+N)|\log(t)|}\|_{L^1(\mathbf{R}_{>0},\frac{\mathrm{d}t}{t})}^p+C_{N,a,b}^p\int_{|y|\ge 1/2}\frac{1}{|y|^{pN}}\,\mathrm{d}y\right\}^{1/p}. \tag{B.2.1.28}
$$

*(4) If $\phi$ is supported over $\mathbf{R}_{>1}$, then $C_{N,a,b}$ from (B.2.1.26) depends only on $N,b$, and $\phi$ but not on $a$, and $\Phi\in H^p(\mathbf{C}_{<b})$ for every real number $p\ge 1$.*

Proof. (1) : We write $t=e^x$ and obtain

$$
\Phi(s)=\int_{-\infty}^{+\infty}\phi(e^x)e^{xs}\,\mathrm{d}x. \tag{B.2.1.29}
$$

We have for every real number $A>0$ and $|\sigma|\le A$ that

$$
\int_{-\infty}^{+\infty}|\phi(e^x)||e^{\sigma x}|\,\mathrm{d}x\le\int_{-\infty}^{+\infty}|\phi(e^x)|e^{|Ax|}\,\mathrm{d}x \tag{B.2.1.30}
$$

since $e^{\sigma x}\le e^{|Ax|}$ for all $x\in\mathbf{R}$. The integral on the right side in (B.2.1.30) converges since $\phi(e^x)\in\mathcal{S}(\mathbf{R})$ decays faster than $e^{-N|x|}$ for any $N>A$ as $|x|\to+\infty$. It follows that the integral defining $\Phi(s)$ in (B.2.1.29) converges absolutely and uniformly over the vertical strip $\mathbf{C}_{(-A,A)}$. Since this holds for every $A>0$, $\Phi$ is entire.

(2) : We have, as in the proof of Proposition B.2.1.5(2) (see (B.2.1.7)), for every integer $N\ge 1$ and every $y\ne 0$:

$$
\Phi(\sigma+iy)=\frac{(-1)^N}{(\sigma+iy)^N}\int_{-\infty}^{+\infty}\partial_x^N(\phi(e^x))e^{(\sigma+iy)x}\,\mathrm{d}x. \tag{B.2.1.31}
$$

Since $|e^{(\sigma+iy)x}|=e^{\sigma x}\le e^{\max\{|a|,|b|\}\cdot|x|}$ for all $x\in\mathbf{R}$ and all $a\le\sigma\le b$, we deduce the inequality, for $y\ne 0$ and all $a\le\sigma\le b$:

$$
|\Phi(\sigma+iy)|\le\frac{1}{(\sigma^2+y^2)^{N/2}}\int_{-\infty}^{+\infty}|\partial_x^N(\phi(e^x))|e^{\max\{|a|,|b|\}\cdot|x|}\,\mathrm{d}x \tag{B.2.1.32}
$$

$$
\le\frac{1}{|y|^N}\int_{-\infty}^{+\infty}|\partial_x^N(\phi(e^x))|e^{\max\{|a|,|b|\}\cdot|x|}\,\mathrm{d}x. \tag{B.2.1.33}
$$

Upon defining

$$
C_{N,a,b}:=\int_{-\infty}^{+\infty}|\partial_x^N(\phi(e^x))|e^{(\max\{|a|,|b|\})|x|}\,\mathrm{d}x \tag{B.2.1.34}
$$

which indeed converges by Lemma B.2.1.4(4), we deduce that we have, for all $y\ne 0$ and all $a\le\sigma\le b$:

$$
|\Phi(\sigma+iy)|\le C_{N,a,b}|y|^{-N}. \tag{B.2.1.35}
$$

(3) : We have, for every $y\in\mathbf{R}$:

$$
|\Phi(\sigma+iy)|\le\|\phi(e^x)e^{\max\{|a|,|b|\}\cdot|x|}\|_{L^1(\mathbf{R},\mathrm{d}x)} \tag{B.2.1.36}
$$

and hence from (B.2.1.36) and (B.2.1.34):

$$
|\Phi(\sigma+iy)|\le\|\phi(e^x)e^{\max\{|a|,|b|\}\cdot|x|}\|_{L^1(\mathbf{R},\mathrm{d}x)}\cdot\mathrm{1}_{|y|<1/2}(y)+\frac{C_{N,a,b}}{|y|^N}\cdot\mathrm{1}_{|y|\ge 1/2}(y). \tag{B.2.1.37}
$$

We deduce from (B.2.1.37) that for every $p\ge 1$, upon choosing $N>1$:

$$
\|\Phi(\sigma+iy)\|_{L^p(\mathbf{R},\mathrm{d}y)}\le\left\{\|\phi(e^x)e^{\max\{|a|,|b|\}\cdot|x|}\|_{L^1(\mathbf{R},\mathrm{d}x)}^p+C_{N,a,b}^p\int_{|y|\ge 1/2}\frac{1}{|y|^{pN}}\,\mathrm{d}y\right\}^{1/p}. \tag{B.2.1.38}
$$

## PDF page 600

**600** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

This proves that (B.2.1.28) holds.

(4) : If $\phi$ is supported over $\mathbf{R}_{>1}$, then the majorant $|\partial_x^N(\phi(e^x))|e^{\max\{|a|,|b|\}\cdot|x|}$ for $|\partial_x^N(\phi(e^x))e^{sx}|$ can be replaced with the sharper majorant $|\partial_x^N(\phi(e^x))|e^{|b|\cdot|x|}$, which does not depend on $a$.

We deduce that we have $\Phi\in H^p(\mathbf{C}_{<b})$ for every real number $p\ge 1$. $\square$

Corollary B.2.1.10. *Let $\phi\in\mathcal{S}(\mathbf{R}_{>0})$ be a Schwartz-Bruhat function with exponential decay. Then:*

*(1) For every integer $n\ge 0$, the functions $M(\phi)(n-s)$ and $M(s+n)$ are entire and satisfy the inequality from (B.2.1.28) on each vertical strip $\mathbf{C}_{[a,b]}$. In particular, they are bounded on vertical strips of bounded width.*

*(2) Let $f:\mathbf{C}_{(a,b)}\to\mathbf{C}$, for $a<b$ fixed real numbers, be a meromorphic function with finitely many poles contained in $\mathbf{C}_{(a,b)}$. Assume that there exist real numbers $A,B>0$ such that for $a<\sigma<b$ we have*

$$
|f(\sigma+iy)|\le A|y|^B \tag{B.2.1.39}
$$

*for all $|y|\gg 0$ (largeness uniform in such $\sigma$). Then for every integer $n\ge 1$, the meromorphic functions $f(s)M(\phi)(s+n)$ and $f(s)M(\phi)(-s+n)$ satisfy the inequality from (B.2.1.26) for all large enough $|y|>0$.*

Proof. (1) : We have $M(\phi)(-s)=M(\check{\phi})(s)$, and since $\phi$ is Schwartz with exponential decay, so is $\check{\phi}$. Proposition B.2.1.9(1) and (2) therefore apply and gives (1) for $n=0$.

We have $M(\phi)(s+n)=M(t^n\phi)(s)$, and since $\phi$ is Schwartz with exponential decay, so is $t^n\phi$ for every integer $n\in\mathbf{Z}$. We may therefore assume $n=0$ and the foregoing applies.

(2) : By (1) and (B.2.1.26), the inequality in (B.2.1.27) holds for $f(s)\Phi(s)$ so long as (B.2.1.39) does, and hence both hold for all large enough $|y|\gg 0$. $\square$

**B.2.2. Asymptotic Cauchy Integral Formula.** We begin by studying the Cauchy Integral Formula applied to the special case of holomorphic functions $\Phi$ over an open bounded vertical strip such that $\Phi(s)$ decays rapidly as $|s|\to\infty$ uniformly on the vertical strip.

B.2.2.1. *Cauchy Integrals.* We introduce a class of holomorphic functions that comprises the Mellin transforms of all Schwartz functions with exponential decay.

Definition B.2.2.1. Let $a<b$ be real numbers. Let $\Phi:\mathbf{C}_{(a,b)}\to\mathbf{C}$ be a holomorphic function. We say that $\Phi$ is uniformly Schwartz over the vertical strip $\mathbf{C}_{(a,b)}$ if and only if for every $\varepsilon>0$ such that $a+\varepsilon<b-\varepsilon$, and for every integer $N\ge 1$, there exists a real number $C_{N,\varepsilon}>0$ such that for all sufficiently large $|y|$ uniformly over all $a+\varepsilon\le\sigma\le b-\varepsilon$ we have

$$
|\Phi(\sigma+iy)|\le\frac{C_{N,\varepsilon}}{|y|^N} \tag{B.2.2.1}
$$

(so in particular $\Phi$ is bounded on each $\mathbf{C}_{(a+\varepsilon,b-\varepsilon)}$).

If $\Phi$ is entire, we say it is Schwartz on vertical strips if and only if for every bounded open interval $(a,b)\subset\mathbf{R}$ it is uniformly Schwartz over the vertical strip $\mathbf{C}_{(a,b)}$. If $\Phi:\mathbf{C}_{<b}\to\mathbf{C}$ is holomorphic, we say it is Schwartz on the half-plane $\mathbf{C}_{<b}$ if and only if for every $\varepsilon>0$ and for every integer $N\ge 1$, $\Phi(\sigma+iy)$ satisfies condition (B.2.2.1) for all large enough $|y|$ uniformly over all $\sigma\le b-\varepsilon$.

The "justification" of this terminology is that by Lemma D.3.1.1 each of the derivatives $\partial_y^j(\Phi(\sigma+iy)$ satisfy the same uniform decay estimates as $|y|\to\infty$ when $\sigma$ varies in a compact interval. In other words, the Schwartz decay properties along each vertical line have uniform constants and uniform largeness conditions on $|y|$ as $\sigma$ varies in a compact interval.

Example B.2.2.2. If $\phi\in\mathcal{S}(\mathbf{R}_{>0})$ is a Schwartz-Bruhat with exponential decay, then $\Phi:=M(\phi)$ is Schwartz on vertical strips by Proposition B.2.1.9(2). Indeed, for any non-empty vertical strip of the form $\mathbf{C}_{(a,b)}$, we may any real number $\varepsilon>0$ and let $C_{N,\varepsilon}:=C_{N,a-\varepsilon,b+\varepsilon}$. By Proposition B.2.1.9(2), the condition in (B.2.2.1) is satisfied by the restriction of $\Phi$ to $\mathbf{C}_{(a,b)}$.

## PDF page 601

**B.2. ASYMPTOTIC CAUCHY INTEGRAL FORMULA** · **601**

By Proposition B.2.1.5(1,2), Schwartz-Bruhat functions $\phi$ of exponential or semi-exponential decay over $\mathbf{R}_{>0}$ provide examples of holomorphic functions $\Phi(s):=M(\phi)(s)$ on either $\mathbf{C}$, $\mathbf{C}_{>0}$ or $\mathbf{C}_{<0}$ that are uniformly Schwartz over the open vertical strips of bounded width contained within such domains in $\mathbf{C}$.

We record here the following general estimate for the Mellin transform of smooth functions on $\mathbf{R}_{>0}$ that are Schwartz-Bruhat, but neither exponentially nor semi-exponentially decaying. It is a uniform version of the Riemann-Lebesgue Lemma, and provides examples of holomorphic functions over a vertical strip $\mathbf{C}_{(a,b)}$ of bounded width that are uniformly Schwartz on all open vertical sub-strips.

Proposition B.2.2.3 (Uniform Riemann-Lebesgue - I). *Let $a,b\in\mathbf{R}$ be two real numbers, with $a<b$. Let $\phi\in\mathcal{S}(\mathbf{R}_{>0})$ be a Schwartz-Bruhat function.*

*Assume that we have, for any $\sigma\in[a,b]$, $t^\sigma\phi\in\mathcal{S}(\mathbf{R}_{>0})$.*

*Then:*

*(1) The Mellin transform $M(\phi)(s)$ is a continuous function over $\mathbf{C}_{[a,b]}$ whose restriction to every vertical line in $\mathbf{C}_{[a,b]}$ is Schwartz, and it is holomorphic over $\mathbf{C}_{(a,b)}$.*

*(2) For any integer $N\ge 1$, there exists a real number $C_{N,a,b}>0$ such that for any $a\le\sigma\le b$, we have:*

$$
|M(\phi)(s)|\le\frac{C_{N,a,b}}{|y|^N} \tag{B.2.2.2}
$$

*as $|y|\to+\infty$, uniformly in such $\sigma$. In particular, $M(\phi)$ is uniformly Schwartz over all open vertical strips contained within $\mathbf{C}_{[a,b]}$.*

Proof. We first claim $(t\partial_t)^N\phi$ satisfies the same assumptions as $\phi$ for every integer $N\ge 1$. We have, for every $\sigma\in[a,b]$:

$$
(t\partial_t)(t^\sigma\phi)=\sigma\cdot t^\sigma\phi+t^\sigma(t\partial_t)\phi
$$

and since $(t\partial_t)(t^\sigma\phi)$ is Schwartz-Bruhat, as is $t^\sigma\phi$ (and hence $\sigma\cdot t^\sigma\phi$) by the assumptions on $\phi$, we deduce that $t^\sigma(t\partial_t)\phi$ is Schwartz-Bruhat over $\mathbf{R}_{>0}$ for all $\sigma\in[a,b]$.

We have, as in the proof of Proposition B.2.1.5(2) (see (B.2.1.7)), for every integer $N\ge 1$, every $y\ne 0$, and every $\sigma\in[a,b]$ that

$$
\Phi(\sigma+iy)=\frac{(-1)^N}{(\sigma+iy)^N}\int_{-\infty}^{+\infty}\partial_x^N(\phi(e^x))e^{(\sigma+iy)x}\,\mathrm{d}x \tag{B.2.2.3}
$$

where the integral on the right side of (B.2.2.3) converges by Lemma B.2.1.6 and the foregoing since $t^\sigma(t\partial_t)^N\phi\in\mathcal{S}(\mathbf{R}_{>0})$ for every integer $N\ge 1$.

This proves that $\Phi(s)$ is holomorphic over $\mathbf{C}_{(a,b)}$, Schwartz on every vertical line of $\mathbf{C}_{[a,b]}$ since $t^\sigma\phi$ is Schwartz-Bruhat for every $\sigma\in[a,b]$ and the restriction of the Mellin transform to each such vertical line $\mathrm{Re}(s)=\sigma$ is the (inverse) Fourier transform of $t^\sigma\phi$ on $\mathbf{R}_{>0}$.

The absolute value of the integral in (B.2.2.3) is bounded above by $C_{N,a,b}:=\|\partial_x^N(\phi(e^x))\max(e^{ax},e^{bx})\|_{L^1(\mathbf{R},\mathrm{d}x)}$, and hence the estimate in (B.2.2.2) holds by (B.2.2.3). $\square$

The following is an asymptotic version of Cauchy's Integral Formula.

Theorem B.2.2.4 (Asymptotic Cauchy Integral Formula). *Let $a,b$ be real numbers, $a<b$, and $\Phi:\mathbf{C}_{(a,b)}\to\mathbf{C}$ holomorphic. Assume that $\Phi$ is uniformly Schwartz on the vertical strip $\mathbf{C}_{(a,b)}$. Let $\varepsilon>0$ be a real number such that $a+\varepsilon<b-\varepsilon$.*

*Let $N\ge 0$ be an integer.*

*(1) For every $z\in\mathbf{C}$,*

$$
-\frac{N!}{2\pi i}\int_{a+\varepsilon-i\infty}^{a+\varepsilon+i\infty}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s+\frac{N!}{2\pi i}\int_{b-\varepsilon-i\infty}^{b-\varepsilon+i\infty}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s=\Phi^{(N)}(z) \tag{B.2.2.4}
$$

## PDF page 602

**602** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

*if $z\in\mathbf{C}_{(a+\varepsilon,b-\varepsilon)}$ and*

$$
-\frac{N!}{2\pi i}\int_{a+\varepsilon-i\infty}^{a+\varepsilon+i\infty}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s+\frac{N!}{2\pi i}\int_{b-\varepsilon-i\infty}^{b-\varepsilon+i\infty}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s=0 \tag{B.2.2.5}
$$

*if $z\notin\mathbf{C}_{[a+\varepsilon,b-\varepsilon]}$, with all integrals absolutely convergent.*

*(2) If $\Phi:\mathbf{C}_{<b}\to\mathbf{C}$ is holomorphic and Schwartz on the half-plane $\mathbf{C}_{<b}$, then for every $\varepsilon>0$ we have:*

$$
\frac{N!}{2\pi i}\int_{b-\varepsilon-i\infty}^{b-\varepsilon+i\infty}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s=\Phi^{(N)}(z) \tag{B.2.2.6}
$$

*if $\mathrm{Re}(z)<b-\varepsilon$ and*

$$
\frac{N!}{2\pi i}\int_{b-\varepsilon-i\infty}^{b-\varepsilon+i\infty}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s=0 \tag{B.2.2.7}
$$

*if $\mathrm{Re}(z)>b-\varepsilon$, with all integrals absolutely convergent.*

Proof. (1) : We first claim

$$
\lim_{|T|\to+\infty}\int_{a+\varepsilon}^{b-\varepsilon}|\Phi(\sigma+iT)|\,\mathrm{d}\sigma=0. \tag{B.2.2.8}
$$

For each integer $M\ge 1$ and for all large enough $|T|\gg 0$, there exists a constant $C_{M,\varepsilon}>0$ such that $|\Phi(\sigma+iT)|\le C_{M,\varepsilon}|T|^{-M}$ for all $a+\varepsilon\le\sigma\le b-\varepsilon$. It follows that we have:

$$
\int_{a+\varepsilon}^{b-\varepsilon}|\Phi(\sigma+iT)|\,\mathrm{d}\sigma\le C_{M,\varepsilon}\int_{a+\varepsilon}^{b-\varepsilon}\frac{1}{|T|^M}\,\mathrm{d}\sigma\le C_{M,\varepsilon}(b-a)|T|^{-M}. \tag{B.2.2.9}
$$

*[Figure, redrawn from the PDF, p. 602:]*

```latex
\begin{tikzpicture}[x=1.5cm,y=1.2cm,>=stealth,mid/.style={decoration={markings,mark=at position 0.55 with {\arrow[scale=1.4]{>}}},postaction={decorate}},midv/.style={decoration={markings,mark=at position 0.66 with {\arrow[scale=1.4]{>}}},postaction={decorate}}]
\draw[<->] (-1,0) -- (2.6,0);
\draw[<->] (0.8,-1.9) -- (0.8,1.9);
\draw[mid] (2, 1.5) -- (0, 1.5);
\draw[midv] (0, 1.5) -- (0, -1.5);
\draw[mid] (0, -1.5) -- (2, -1.5);
\draw[midv] (2, -1.5) -- (2, 1.5);
\fill (0,1.5) circle (1.5pt) node[left] {$a+\varepsilon+iT$};
\fill (2,1.5) circle (1.5pt) node[right] {$b-\varepsilon+iT$};
\fill (0,0) circle (1.5pt) node[above left] {$a+\varepsilon$};
\fill (2,0) circle (1.5pt) node[above right] {$b-\varepsilon$};
\fill (0,-1.5) circle (1.5pt) node[left] {$a+\varepsilon-iT$};
\fill (2,-1.5) circle (1.5pt) node[right] {$b-\varepsilon-iT$};
\end{tikzpicture}
```

FIGURE 2. A contour $\Gamma_T$ with counterclockwise orientation (it may or may not enclose $0$)

We call $\Gamma_T$ the contour as in Figure 2. Thus, if $\mathrm{Re}(z)\in(a+\varepsilon,b-\varepsilon)$ and $|T|>\mathrm{Im}(z)$ then

$$
\Phi^{(N)}(z)=\frac{N!}{2\pi i}\int_{\Gamma_T}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s, \tag{B.2.2.10}
$$

and if $\mathrm{Re}(z)\notin[a+\varepsilon,b-\varepsilon]$ then

$$
\frac{N!}{2\pi i}\int_{\Gamma_T}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s=0. \tag{B.2.2.11}
$$

Upon letting $T\to+\infty$, we obtain assertion (1) upon noting the absolute convergence of the integrals in (1) follows from the bound $|\Phi(\sigma+iy)|\le C_{1,\varepsilon}|y|^{-1}$ for $\sigma=a+\varepsilon,b-\varepsilon$ and sufficiently large $|y|$.

## PDF page 603

**B.2. ASYMPTOTIC CAUCHY INTEGRAL FORMULA** · **603**

(2) : The absolute convergence of the integrals is seen as in the proof of (1). Since $a+\varepsilon<\mathrm{Re}(z)$, the function $(s-z)^{-1}$ is smooth and square-integrable over $a+\varepsilon-i\mathbf{R}$, and by the Cauchy-Schwartz inequality we obtain:$^{10}$

$$
\left|\int_{a+\varepsilon-i\infty}^{a+\varepsilon+i\infty}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s\right|\le\|\Phi(a+\varepsilon+it)\|_{L^2(\mathbf{R},\mathrm{d}t)}\left\{\int_{-\infty}^\infty\frac{1}{|a+\varepsilon+it-z|^{2(N+1)}}\,\mathrm{d}t\right\}^{1/2} \tag{B.2.2.12}
$$

$$
\le\|\Phi\|_{H^2(\mathbf{C}_{<b-\varepsilon})}\left\{\int_{-\infty}^\infty\frac{1}{|a+\varepsilon+it-z|^{2(N+1)}}\,\mathrm{d}t\right\}^{1/2}.
$$

By the argument as in (1), we may move the line of integration $(a+\varepsilon-i\infty,a+\varepsilon+i\infty)$ as leftwards as we please leaving the left side of (B.2.2.12) unchanged. Thus, from (B.2.2.12) and elementary estimates (after multiplying $t$ by $a+\varepsilon$), we have

$$
\lim_{a\to-\infty}\int_{a+\varepsilon-i\infty}^{a+\varepsilon+i\infty}\frac{\Phi(s)}{(s-z)^{N+1}}\,\mathrm{d}s=0, \tag{B.2.2.13}
$$

so (B.2.2.4) and (B.2.2.5) hold by arguing as in (1). $\square$

Remark B.2.2.5. For $\Phi$ entire and Schwartz on vertical strips, we may define

$$
\phi(t):=\int_{-i\infty}^{+i\infty}\Phi(s)t^{-s}\,\mathrm{d}s.
$$

on $\mathbf{R}_{>0}$. The integral is absolutely convergent in light of (B.2.1.27), and (by the Dominated Convergence Theorem) $\phi$ is continuous as a function of $t\in\mathbf{R}_{>0}$.

The function $f(u)=\int_{-\infty}^{+\infty}\Phi(ix)e^{-ixu}\,\mathrm{d}x$ is Schwartz since $\Phi$ is Schwartz on vertical lines, and it is in particular smooth. It follows that $\phi(t)=f(\log(t))$ is smooth over $\mathbf{R}_{>0}$ and we may extend it by zero over $\mathbf{R}$ preserving smoothness since the derivative of $\phi$ on $\mathbf{R}_{>0}$ of any order decays to $0$ as $t\to 0^+$.

In some cases, $\Phi$ is not only the Mellin transform of a smooth function $\phi$ on $\mathbf{R}$ supported over $\mathbf{R}_{\ge 0}$ and such that $\phi(e^x)$ is Schwartz, but it is the Mellin transform of a Schwartz function on $\mathbf{R}_{>0}$ with exponential decay. The entire functions $\Phi$ such that (B.2.1.27) holds with a constant $C_{N,a,b}$ which does not depend on $a,b$, but only on $N\ge 1$, are the Mellin transform of a smooth compactly supported function over $\mathbf{R}$ by [Horm, Ch.VII, Thm.7.3.1] (the Paley-Wiener-Schwartz Theorem).$^{11}$

In the proof of the Asymptotic Cauchy Integral Formula, we can choose the top and bottom edges of the rectangles wherever we wish sufficiently high up and low down, so it isn't necessary to require the uniformly Schwartz decay property across the entirety of the strips $a+\varepsilon\le\sigma\le b-\varepsilon$ for all sufficiently small $\varepsilon>0$. We only need the uniform vertical Schwartz decay "near" the vertical edges $\sigma=a,b$ and a sufficient supply of horizontal segments arbitrarily high up and low down on which there is such decay:

Corollary B.2.2.6. *For real numbers $a<b$, let $\Phi:\mathbf{C}_{(a,b)}\to\mathbf{C}$ be a holomorphic function that is uniformly Schwartz on $\mathbf{C}_{(a,a')}$ and on $\mathbf{C}_{(b',b)}$ for some $a<a'<b'<b$. Pick $a''\in(a,a')$ and $b''\in(b',b)$.*

*Assume there is a sequence of real numbers $\{T_k\}_{k\in\mathbf{Z}}$ with $T_k<T_{k+1}$ and $|T_k|\to+\infty$ as $|k|\to+\infty$ such that for each integer $M\ge 1$ we have*

$$
|\Phi(\sigma+iT_k)|=O_{M,\varepsilon}(|T_k|^{-M}) \tag{B.2.2.14}
$$

*uniformly in $\sigma\in[a'',b'']$ as $|k|\to+\infty$.*

*The assertions in Theorem B.2.2.4(1) hold for $\Phi$.*

$^{10}$Why is the $H^2$-norm of $\Phi$ at the end finite? Maybe use Cauchy Integral Formula to replace that with $L^2$-norm of $\Phi(b-\varepsilon+it)$ that is independent of $a$?

$^{11}$This latter theorem seems to involve a different type of upper bound, so must either rewrite for accuracy or remove it; if not needed, I recommend to remove.

## PDF page 604

**604** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

PROOF. The uniformly Schwartz hypothesis on $\Phi$ does not address behavior in the strip $\{a'\le \sigma \le b'\}$, but the proof of Theorem B.2.2.4(1) doesn't need precise control in that entire region as one goes far up and far down: we can carry out the method of the proof by choosing the rectangular contours to have top and bottom sides at the heights $t=T_k$ for sufficiently positive and sufficiently negative $k$ since (B.2.2.14) provides the required decay of integrals along the top and bottom of the rectangle. $\square$

**B.3. Asymptotic Residue Theorem**

In this section we discuss a consequence of Cauchy's Residue Theorem under a Schwartz condition uniform on upper and lower halves of a vertical strip, combined with a condition on the distribution of the poles of the meromorphic function across the vertical strip.

**B.3.1. Slow growth near the poles.** We discuss a growth condition for meromorphic functions on vertical strips, near their poles, to identify a class of such functions that, when multiplied by an entire function that is Schwartz on vertical strips, decays on bounded horizontal segments whose ordinate tends to $\pm\infty$.

B.3.1.1. *Polar locations and vertical growth.* We introduce a condition on the location of the poles of a meromorphic function $f$ in a vertical strip that will combine correctly with the Schwartz condition uniformly on vertical strips introduced in Definition B.2.2.1 for a holomorphic function $\Phi$, leading to an asymptotic version of Cauchy's Residue Theorem for $\Phi(s)f(s)$.

DEFINITION B.3.1.1. Let $a<b$ be real numbers. Let $f:\mathbf{C}_{(a,b)}\to\mathbf{C}$ be a meromorphic function. We say that $f$ has *slow growth near its poles* if and only if:

(1) there exists a real number $\alpha>0$ such that for each integer $k$ there exists a real number $T_k$, satisfying the following properties:

(a) $|T_{\pm(k+1)}|\ge |T_{\pm k}|$.

(b) $\lim_{|k|\to+\infty}|T_k|=+\infty$.

(c) $T_k=O(|k|^{\alpha})$ as $|k|\to+\infty$.

and $f$ is holomorphic over a small enough horizontal strip containing the horizontal line $\mathbf{R}+iT_k$ in its interior,

(2) there exists a real number $\beta>0$ and a real number $A_{a,b,\beta}>0$, neither depending on $\sigma$, such that for every integer $k\in\mathbf{Z}$ and $a<\sigma<b$,

$$
|f(\sigma+iT_k)|\le A_{a,b}|k|^{\beta}, \tag{B.3.1.1}
$$

(3) there exist real numbers $\varepsilon_1,\varepsilon_2>0$ such that $0<\varepsilon_1<\varepsilon_2<(b-a)/2$ and such that $f(a+\varepsilon_1+it)$ and $f(b-\varepsilon_2+it)$ are continuous functions of $t\in\mathbf{R}$ growing at most polynomially as $|t|\to+\infty$. In particular, no pole of $f$ is contained within the vertical lines $a+\varepsilon_1+i\mathbf{R}$ and $b-\varepsilon_2+i\mathbf{R}$.

We refer to the sequence $\{T_k\}_{k\in\mathbf{Z}}$ as a sequence that *witnesses the slow growth of $f$ near its poles.*

We now show that if $f:\mathbf{C}_{(a,b)}\to\mathbf{C}$ is meromorphic and with slow growth near its poles, and if $\Phi:\mathbf{C}_{(a-\varepsilon,b+\varepsilon)}\to\mathbf{C}$ is holomorphic and uniformly Schwartz on the vertical strip $\mathbf{C}_{(a-\varepsilon,b+\varepsilon)}$ for some $\varepsilon>0$ then line integrals of $\Phi(s)f(s)$ over horizontal segments contained within $\mathbf{C}_{(a,b)}$ vanish asymptotically along the ordinates $\{T_k\}_{k\in\mathbf{Z}}$ as $|k|\to\infty$.

LEMMA B.3.1.2. *Let $a<b$ be real numbers, $f:\mathbf{C}_{(a,b)}\to\mathbf{C}$ a meromorphic function with slow growth near its poles within $\mathbf{C}_{(a,b)}$. Let $\varepsilon>0$ be a real number and $\Phi:\mathbf{C}_{(a-\varepsilon,b+\varepsilon)}\to\mathbf{C}$ a holomorphic function, uniformly Schwartz over the vertical strip $\mathbf{C}_{(a-\varepsilon,b+\varepsilon)}$. Then for $\{T_k\}_{k\in\mathbf{Z},|k|\ge 2}\subset\mathbf{R}$ witnessing the slow growth condition*

## PDF page 605

**B.3. ASYMPTOTIC RESIDUE THEOREM** · **605**

*on $f$ near its poles, we have:*

$$
\lim_{|k|\to+\infty}\int_{a-iT_k}^{b-iT_k}|f(s)\Phi(s)|\,|\mathrm{d}s|=0=\lim_{|k|\to+\infty}\int_{a+iT_k}^{b+iT_k}|f(s)\Phi(s)|\,|\mathrm{d}s|. \tag{B.3.1.2}
$$

PROOF. Let $N\ge 1$ be a fixed integer. Then there exists a real number $C_{N,\varepsilon}>0$, such that for all large enough $|k|$, we have $|\Phi(\sigma+iT_k)|\le C_{N,\varepsilon}|T_k|^{-N}$, for all $\sigma\in[a,b]$. We may choose $N$ such that $N\gamma>\delta$, and we have that there exists a real number $A>0$ such that:

$$
|f(\sigma+iT_k)\Phi(\sigma+iT_k)|\le A_{a,b}\cdot C_{N,\varepsilon}|k|^{\delta}T_k^{-N}\le A\cdot A_{a,b}\cdot C_{N,\varepsilon}|k|^{\delta}|k|^{-N\gamma}
$$

for all large enough $|k|$.

We therefore have:

$$
\lim_{|k|\to+\infty}\int_{a\pm iT_k}^{b\pm iT_k}|f(s)\Phi(s)|\,|\mathrm{d}s|\le\lim_{|k|\to+\infty}A\cdot A_{a,b}\cdot C_{N,\varepsilon}(b-a)|k|^{\delta-N\gamma}=0. \tag{B.3.1.3}
$$

$\square$

**B.3.2. The Asymptotic Residue Theorem.** We now discuss a consequence of Cauchy's Residue Theore, for those meromorphic functions of the form $f(s)\Phi(s)$ with $f$ meromorphic and having slow growth around its poles over a vertical strip $\mathbf{C}_{(a,b)}$ (see Definition B.3.1.1) and $\Phi$ holomorphic over a larger open vertical strip containing $\mathbf{C}_{[a,b]}$ and uniformly Schwartz on that open strip.

B.3.2.1. *Residues over asymptotic contours.* Consider a vertical strip $\mathbf{C}_{(a,b)}$ with real $a<b$, a meromorphic function $f:\mathbf{C}_{(a,b)}\to\mathbf{C}$ with slow growth near its poles, and a holomorphic function $\Phi$ on $\mathbf{C}_{(a-\varepsilon,b+\varepsilon)}$ that is uniformly Schwartz.

*[Figure, redrawn from the PDF, p. 605:]*

```latex
\begin{tikzpicture}[x=1.5cm,y=1.2cm,>=stealth,mid/.style={decoration={markings,mark=at position 0.55 with {\arrow[scale=1.4]{>}}},postaction={decorate}},midv/.style={decoration={markings,mark=at position 0.66 with {\arrow[scale=1.4]{>}}},postaction={decorate}}]
\draw[<->] (-1,0) -- (2.6,0);
\draw[<->] (0.8,-1.9) -- (0.8,1.9);
\draw[mid] (2, 1.5) -- (0, 1.5);
\draw[midv] (0, 1.5) -- (0, -1.5);
\draw[mid] (0, -1.5) -- (2, -1.5);
\draw[midv] (2, -1.5) -- (2, 1.5);
\fill (0,1.5) circle (1.5pt) node[left] {$a+\varepsilon_1+iT$};
\fill (2,1.5) circle (1.5pt) node[right] {$b-\varepsilon_2+iT$};
\fill (0,0) circle (1.5pt) node[above left] {$a+\varepsilon_1$};
\fill (2,0) circle (1.5pt) node[above right] {$b-\varepsilon_2$};
\fill (0,-1.5) circle (1.5pt) node[left] {$a+\varepsilon_1-iT$};
\fill (2,-1.5) circle (1.5pt) node[right] {$b-\varepsilon_2-iT$};
\end{tikzpicture}
```

FIGURE 3. A contour $\Gamma_{T,\varepsilon_1,\varepsilon_2}$ with counterclockwise orientation (it may or may not enclose 0)

We shall analyze the product function $\Phi(s)f(s)$ over growing contours $\Gamma_{T,\varepsilon_1,\varepsilon_2}$ of the form as in Figure 3 for all real numbers $T>0$ and $\varepsilon_1,\varepsilon_2>0$ such that $a+\varepsilon_1<b-\varepsilon_2$. We denote by $U_{T,\varepsilon_1,\varepsilon_2}$ the open subset of $\mathbf{C}_{(a,b)}$ enclosed by $\Gamma_{T,\varepsilon_1,\varepsilon_2}$ and having that rectangle as its boundary.

THEOREM B.3.2.1 (Asymptotic Residue Theorem). *Let $a<b$ be real numbers, $f:\mathbf{C}_{(a,b)}\to\mathbf{C}$ a meromorphic function with slow growth near its poles within $\mathbf{C}_{(a,b)}$. Let $a'<b'$ be real numbers such that $[a,b]\subset(a',b')$, and $\Phi:\mathbf{C}_{(a',b')}\to\mathbf{C}$ a holomorphic function that is uniformly Schwartz.*

*Let $\varepsilon_1,\varepsilon_2>0$ be real numbers such that $a+\varepsilon_1<b-\varepsilon_2$, and such that $f$ has no poles on the vertical lines $\sigma=a+\varepsilon_1,b-\varepsilon_2$. Then for $\{T_k\}_{k\ge 0}$ the sequence of real numbers witnessing the slow growth of $f$ near its poles, we have:*

## PDF page 606

**606** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

(1) *the following limit exists:*

$$
\lim_{|k|\to+\infty}\sum_{\rho\in U_{T_k,\varepsilon_1,\varepsilon_2}}\Phi(\rho)\operatorname{Res}_{s=\rho}f(s) \tag{B.3.2.1}
$$

(*where the sum in* (B.3.2.1) *is indexed by the poles of $f$ contained in $U_{T_k,\varepsilon_1,\varepsilon_2}$*),

(2)

$$
-\frac{1}{2\pi i}\int_{a+\varepsilon_1-i\infty}^{a+\varepsilon_1+i\infty}\Phi(s)f(s)\,\mathrm{d}s+\frac{1}{2\pi i}\int_{b-\varepsilon_2-i\infty}^{b-\varepsilon_2+i\infty}\Phi(s)f(s)\,\mathrm{d}s=\lim_{|k|\to+\infty}\sum_{\rho\in U_{T_k,\varepsilon_1,\varepsilon_2}}\Phi(\rho)\operatorname{Res}_{s=\rho}f(s) \tag{B.3.2.2}
$$

*with absolutely convergent integrals on the left side.*

PROOF OF THEOREM B.3.2.1. We will apply the Residue Theorem to the rectangles $\Gamma_{T_k,\varepsilon_1,\varepsilon_2}$ and let $|k|$ tend to $+\infty$, using Lemma B.3.1.2 to get the asymptotic vanishing of the integrals over the horizontal segments of $\Gamma_{T_k,\varepsilon_1,\varepsilon_2}$.

The Residue Theorem applied to the meromorphic function $\Phi(s)f(s)$ whose poles are not on the boundary $\Gamma_{T_k,\varepsilon_1,\varepsilon_2}$ yields

$$
\frac{1}{2\pi i}\int_{\Gamma_{T_k,\varepsilon_1,\varepsilon_2}}\Phi(s)f(s)\,\mathrm{d}s=\sum_{\rho\in U_{T_k,\varepsilon_1,\varepsilon_2}}\Phi(\rho)\operatorname{Res}_{s=\rho}f(s). \tag{B.3.2.3}
$$

The left side of (B.3.2.3) is

$$
-\frac{1}{2\pi i}\int_{a+\varepsilon_1-iT_k}^{a+\varepsilon_1+iT_k}+\frac{1}{2\pi i}\int_{b-\varepsilon_2-iT_k}^{b-\varepsilon_2+iT_k}-\frac{1}{2\pi i}\int_{a+\varepsilon_1-iT_k}^{b-\varepsilon_2-iT_k}+\frac{1}{2\pi i}\int_{a+\varepsilon_1+iT_k}^{b-\varepsilon_2+iT_k}(\Phi(s)f(s)\,\mathrm{d}s), \tag{B.3.2.4}
$$

The uniformly Schwartz condition on $\Phi$ and slow growth condition on $f$ (which includes at most polynomial growth along vertical lines) ensure that $\Phi(s)f(s)$ is absolutely integrable on the two vertical lines $\operatorname{Re}(s)=a+\varepsilon_1,b-\varepsilon_2$, and if we let $|k|\to+\infty$ then by Lemma B.3.1.2 the third and fourth integrals in (B.3.2.4) tend to $0$ $|k|\to\infty$, so as $|k|\to\infty$ the left side of (B.3.2.3) has a limit that is equal to

$$
-\frac{1}{2\pi i}\int_{a+\varepsilon_1-i\infty}^{a+\varepsilon_1+i\infty}\Phi(s)f(s)\,\mathrm{d}s+\frac{1}{2\pi i}\int_{b-\varepsilon_2-i\infty}^{b-\varepsilon_2+i\infty}\Phi(s)f(s)\,\mathrm{d}s. \tag{B.3.2.5}
$$

We deduce that the limit in (B.3.2.1) converges, and that (B.3.2.2) holds (with absolutely convergent integrals). $\square$

**B.4. Explicit Formulas for Hecke $L$-functions**

In this section we review for ease of access the explicit formulas for Hecke $L$-functions proved by Weil in **[Weil-b]**. Barner’s generalization in **[Bar**, §2**]** has the advantage of identifying a class of functions on which the functionals arising in the explicit formulas and corresponding to the Archimedean places attain a simpler form.

The main references for this section are Lang’s book **[Lang-b**, Ch. XVII**]**, where the explicit formulas are reproved under conditions that mildly generalize Barner’s in **[Bar**, §2**]**.

Occasional reference is also made to Lang’s book **[Lang-a**, Ch. X**]**, an earlier edition to **[Lang-b]** (where the arguments in Weil’s original article **[Weil-b]** are presented and, specifically, the continuity properties of the functionals arising in the explicit formulas for Hecke $L$-functions are proved).

**B.4.1. Complements on Poisson Summation and Cauchy Integrals.** In this subsection we will be proving identities between values of Dirac combs on piece-wise smooth functions on the positive real half-line with isolated jump singularities, by means of Poisson Summation and contour integration of their Mellin transform.

## PDF page 607

**B.4. EXPLICIT FORMULAS FOR HECKE $L$-FUNCTIONS** · **607**

B.4.1.1. *Slow decay in the presence of isolated jump singularities.* In this subsection we recall basic properties of the Mellin transform of smooth functions supported over the positive reals and decaying rapidly at zero and infinity, and we recall the Poisson Summation Formula over $\mathbf R_{>0}$ and its quotients by the discrete subgroups $\theta^{\mathbf Z}$, for $\theta\in\mathbf R_{>0}-\{1\}$.

Let $\theta\in\mathbf R_{>0}-\{1\}$. A continuous character $\chi:\theta^{\mathbf Z}\to \mathrm{U}(1)$ is of the form $\chi(\theta^m)=\theta^{imx}$ for some $x\in\mathbf R$. The imaginary number $ix$ is uniquely determined modulo the discrete group $2\pi i\mathbf Z/\log(\theta)$. We will refer to a choice of $ix$ as $\log\chi(\theta)$, and all constructions and assertions made throughout this section involving $\log\chi(\theta)$ will, a priori, depend on such choice.

For a function $\phi:\mathbf R\to\mathbf C$, we say $\phi$ is *piece-wise smooth* if and only if there is a discrete subset $\Sigma\subset\mathbf R$ such that $\phi$ is smooth on $\mathbf R-\Sigma$ and all $\phi^{(j)}$’s have both one-sided limits at each $x\in\Sigma$. We refer the reader to **[Fol-2**, Ch. 2, §2.2, p. 32**]** for more on piece-wise smooth functions on the real line. A function $\phi:\mathbf R_{>0}\to\mathbf C$ is called *piece-wise smooth* if and only if $\phi(e^x)$ is piece-wise smooth as a function of $x\in\mathbf R$.

We begin with the following:

LEMMA B.4.1.1 (Slow decay in the presence of isolated jump singularities). *Let $\phi:\mathbf R_{>0}\to\mathbf C$ be a function. Assume:*

(1) *$\phi$ is smooth away from finitely many jump singularities; i.e., there exist finitely many points $\{t_1,\ldots,t_N\}\subset\mathbf R_{>0}$ such that for each integer $k\ge 0$, the derivative $(t\partial_t)^k\phi$ exists and is continuous away from $\{t_1,\ldots,t_N\}$ and its one-sided limits as $t\to t_m^{\pm}$ exist for each $1\le m\le N$,*

(2) *$|\phi(t)|$ and $|(t\partial_t)\phi(t)|$ are bounded and decay faster than any positive power of $e^{-|\log(t)|}$ as $|\log(t)|\to+\infty$; i.e., for every integer $N\ge 0$, there exist real numbers $C_N>0$ and $T>0$ such that for all $t\in\mathbf R_{>0}$ with $|\log(t)|>T$, we have:*

$$
|\phi(t)|,|(t\partial_t)\phi(t)|<C_Ne^{-N|\log(t)|}. \tag{B.4.1.1}
$$

*Then the Mellin transform*

$$
\Phi(s):=\int_{\mathbf R_{>0}}\phi(t)t^s\frac{\mathrm{d}t}{t},\ s\in\mathbf C \tag{B.4.1.2}
$$

*is entire, and we have*

$$
|\Phi(s)|\ll|s|^{-1} \tag{B.4.1.3}
$$

*uniformly over the vertical strips of bounded width in $\mathbf C$ as $|s|\to+\infty$ over each fixed such strip.*

PROOF. Let $\{t_1,\ldots,t_N\}\subset\mathbf R_{>0}$ be the finitely many singularities of $\phi$, and call $A>0$ a real number such that $\{t_1,\ldots,t_N\}\subset(1/A,A)$. Then $\int_{1/A}^A\phi(t)t^s\frac{\mathrm{d}t}{t}$ is an entire function of $s\in\mathbf C$ since (i) $\phi$ is bounded over $[1/A,A]$ and (ii) by (2), $\int_0^{1/A}+\int_A^{+\infty}\left(\phi(t)t^s\frac{\mathrm{d}t}{t}\right)$ (limit of $\int_{1/n}^{1/A}+\int_A^n$ as $n\to\infty$) is an entire function of $s\in\mathbf C$ since both integrals converge absolutely and uniformly on all vertical strips of bounded width in $\mathbf C$. This proves $\Phi$ is entire.

It remains to prove (B.4.1.2). Let $\{\varphi_0,\varphi_1,\ldots,\varphi_N\}$ be a smooth partition of unity on $\mathbf R_{>0}$ with $\varphi_m$ compactly supported near $t_m$ for $1\le m\le N$ and equal to $1$ near $t_m$ (so $\varphi_0$ vanishes near each $t_m$), we can write

$$
\phi=\varphi_0\phi+\varphi_1\phi+\cdots+\varphi_N\phi.
$$

We can apply the *proof* of Proposition B.2.1.9(2) (with the integer $N$ there, not to be confused with $N$ above, equal to $1$) to the function $\varphi_0\phi$ because the given exponential decay of $\phi$ and $\phi'$ near $0,\infty$ is all that proof requires to attain the conclusion there with the integer $N$ there equal to $1$. Thus, we can pass to $\phi-\varphi_0\phi$ and then separately treat each $\varphi_m\phi$ with $1\le m\le N$; i.e., it is enough to treat the case $\phi$ is compactly

## PDF page 608

**608** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

supported over $(1/A,A)$ for some $A>1$ and is smooth except for one jump singularity at $t=1$. Define $a:=\phi(1^+)-\phi(1^-)$.

We have

$$
a-\int_{1/A}^1\phi'(t)t^{s+1}\frac{\mathrm{d}t}{t}-\int_1^A\phi'(t)t^{s+1}\frac{\mathrm{d}t}{t}=s\int_{1/A}^1\phi(t)t^s\frac{\mathrm{d}t}{t}+s\int_1^A\phi(t)t^s\frac{\mathrm{d}t}{t}, \tag{B.4.1.4}
$$

which gives

$$
\Phi(s)=\frac{a}{s}-\frac{1}{s}\int_0^{+\infty}\phi'(t)t^{s+1}\frac{\mathrm{d}t}{t}. \tag{B.4.1.5}
$$

We fix a bounded interval $I\subset\mathbf R$, and since $\phi'$ is also compactly supported over $(1/A,A)$ with at most one jump discontinuity there exists a real number $C_I>0$ such that $\int_0^{+\infty}|\phi'(t)|t^{\sigma}\,\mathrm{d}t\le C_I$ for all $\sigma\in I$. We deduce that (B.4.1.3) holds for $\phi$ with implied constant $C_I+|a|$. $\square$

PROPOSITION B.4.1.2 (Poisson Summation Formula - jump singularities). *Let $\theta\in\mathbf R_{>0}-\{1\}$ be a real number, $\phi:\mathbf R_{>0}\to\mathbf C$ a function as in Lemma B.4.1.1. Let*

$$
\Phi(s):=\int_{\mathbf R_{>0}}\phi(t)t^s\frac{\mathrm{d}t}{t},\ s\in\mathbf C \tag{B.4.1.6}
$$

*be the Mellin transform of $\phi$ (an entire function by Lemma B.4.1.1) and $\chi$ a continuous character of the discrete subgroup $\theta^{\mathbf Z}\subset\mathbf R_{>0}$.*

*The following identity holds:*

$$
\log(\theta)\sum_{m\in\mathbf Z}\chi(\theta^m)\frac{\lim_{t\to(\theta^m)^+}\phi(t)+\lim_{t\to(\theta^m)^-}\phi(t)}{2}=\sum_{m\in\mathbf Z}\Phi\left(\frac{\log\chi(\theta)+2\pi im}{\log(\theta)},\right) \tag{B.4.1.7}
$$

*where the series in the right side is convergent and independent of the choice of $\log\chi(\theta)$.*

We refer the reader to **[Pinsky**, Ch. 4, §4.2, Exercise 4.2.9, p. 226**]** for a generalization in the case $\chi=1$. Before proving Proposition B.4.1.2, we make some remarks.

REMARK B.4.1.3. There are at most finitely many integers $m\in\mathbf Z$ such that $\theta^m\in\{t_1,\ldots,t_N\}$, and so, away from finitely many integers $m\in\mathbf Z$ we have

$$
\frac{\lim_{t\to(\theta^m)^+}\phi(t)+\lim_{t\to(\theta^m)^-}\phi(t)}{2}=\phi(\theta^m).
$$

REMARK B.4.1.4. The series in the right side of (B.4.1.7) is generally not absolutely convergent under the stated assumptions on $\phi$,$^{12}$ though it is so if $\phi$ is smooth (as opposed to only piece-wise smooth). An example of $\phi$ that satisfies the assumptions but is not smooth is

$$
\phi(t):=\mathrm{1}_{[1,2]}(t). \tag{B.4.1.8}
$$

We have:

$$
\Phi(s)=\int_1^2t^s\frac{\mathrm{d}t}{t}=\frac{2^s-1}{s} \tag{B.4.1.9}
$$

which is entire, with value $\log(2)$ at $s=0$.

Upon choosing, for instance, $\chi=1$ and $\theta=2$, we obtain $\Phi\left(\frac{2\pi im}{\log(2)}\right)=0$ for all $m\in\mathbf Z-\{0\}$ whereas $\Phi(0)=\log(2)$. The left side of (B.4.1.7) is

$$
\log(2)\sum_{m\in\mathbf Z}\frac{\mathrm{1}_{[1,2]}((2^m)^+)+\mathrm{1}_{[1,2]}((2^m)^-)}{2}=\log(2)\frac{\mathrm{1}_{[1,2]}(1)}{2}+\log(2)\frac{\mathrm{1}_{[1,2]}(2)}{2}=\log(2).
$$

$^{12}$Can you give an example in which absolute convergence of the sum provably does not hold?

## PDF page 609

**B.4. EXPLICIT FORMULAS FOR HECKE $L$-FUNCTIONS** · **609**

PROOF OF PROPOSITION B.4.1.2. For $\psi(u)=\phi(u^{\log\theta})$ with $u>0$, the analogous decay hypotheses hold (as $u\mapsto u^{\log\theta}$ is an automorphism of $\mathbf R_{>0}$) and its Mellin transform is

$$
\Psi(s)=\frac{1}{\log\theta}\Phi\left(\frac{s}{\log\theta}\right).
$$

One thereby checks that (B.4.1.7) for $\phi,\Phi,\theta$ is the same as (B.4.1.7) for $\psi,\Psi,e$. Thus, now we may and do assume $\theta=e$, which simplifies the notation and algebraic work considerably.

For $\phi_0$ satisfying the hypotheses (with $\theta=e$), define the $\mathbf Z$-periodic function

$$
\alpha(x):=\sum_{m\in\mathbf Z}\phi_0(e^{x+m}) \tag{B.4.1.10}
$$

of $x\in\mathbf R$, where the series converges absolutely and locally uniformly since $\phi_0(e^x)$ (as a function of $x\in\mathbf R$) decays faster than any positive power of $e^{-|x|}$ as $|x|\to+\infty$. Since $(\mathrm{d}/\mathrm{d}x)(\phi_0(e^x))$ also has such exponential decay, clearly $\alpha(x)$ is $C^1$ away from the $t_m$’s, at which $\alpha$ and $\alpha'$ have at most jump discontinuities.

Since $\alpha$ is a $\mathbf Z$-periodic piecewise-$C^1$ function on $\mathbf R$, by **[Fol-2**, §2.2, Thm. 2.1, p. 35**]** (where “piecewise smooth” means “piecewise $C^1$” by definition), its Fourier series converges pointwise:

$$
\lim_{N\to+\infty}\sum_{m\in\mathbf Z:|m|\le N}a_me^{2\pi imx} \tag{B.4.1.11}
$$

exists, where the Fourier coefficients are given by

$$
a_m:=\int_0^1\alpha(x)\,e^{-2\pi imx}\,\mathrm{d}x. \tag{B.4.1.12}
$$

and the pointwise limit of (B.4.1.11) is:

$$
\frac{\alpha(x^+)+\alpha(x^-)}{2} \tag{B.4.1.13}
$$

where for each sign $\pm$ we define the notation $f(x^{\pm}):=\lim_{u\to x^{\pm}}f(u)$ for a function $f$ defined on a punctured neighborhood of $x$. In particular, the limit in (B.4.1.11) is $\alpha(x)$ at each point $x\in\mathbf R$ at which $\alpha$ is continuous.

We have:

$$
a_m=\int_0^1\alpha(x)\,e^{-2\pi imx}\,\mathrm{d}x=\int_0^1\left\{\sum_{k\in\mathbf Z}\phi_0(e^{x+k})\right\}e^{-2\pi imx}\,\mathrm{d}x=\sum_{k\in\mathbf Z}\int_0^1\phi_0(e^{x+k})\,e^{-2\pi imx}\,\mathrm{d}x.
$$

The exchange in the order of summation and integration is valid due to $\phi_0(e^x)$ being in $L^1(\mathbf R)$. We further have:

$$
\sum_{k\in\mathbf Z}\int_0^1\phi_0(e^{x+k})\,e^{-2\pi imx}\,\mathrm{d}x=\sum_{k\in\mathbf Z}\int_k^{k+1}\phi_0(e^x)\,e^{-2\pi im(x-k)}\,\mathrm{d}x
$$

$$
=\sum_{k\in\mathbf Z}\int_k^{k+1}\phi_0(e^x)\,e^{-2\pi imx}\,\mathrm{d}x
$$

$$
=\int_{-\infty}^{+\infty}\phi_0(e^x)\,e^{-2\pi imx}\,\mathrm{d}x
$$

$$
=\mathcal F(\phi_0(e^x))(m)
$$

where $\mathcal F$ denotes the Fourier transform on $\mathbf R$. We deduce the identity of sums of pointwise convergent series:

$$
\sum_{m\in\mathbf Z:|m|\le N_0}\frac{\phi_0(e^{x^++m})+\phi_0(e^{x^-+m})}{2}+\sum_{m\in\mathbf Z:|m|>N_0}\phi_0(e^{x+m})=\sum_{m\in\mathbf Z}\mathcal F(\phi_0(e^x))(m)e^{2\pi imx} \tag{B.4.1.14}
$$

## PDF page 610

**610** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

where $N_0>0$ is a large enough integer locally dependent on $x$ such that for every $m\in\mathbf Z$ with $|m|>N_0$ we have $x+m\notin\{e^{t_1},\ldots,e^{t_N}\}$.

Any continuous character of $e^{\mathbf Z}$ lifts to a continuous character of $\mathbf R_{>0}$. The dual group $\widehat{e^{\mathbf Z}}$ is the quotient $\mathbf R/2\pi\mathbf Z$, and it is described as the group of characters of the form $\chi(e)=e^{-iu}$ for $u\in\mathbf R$. For $\chi$ one such character, $u$ is uniquely determined modulo $2\pi\mathbf Z$.

For $u_0\in\mathbf R$ the unique real number contained in the interval $[0,2\pi)$ such that $\chi(e)=e^{-iu_0}$, we see that $\widetilde{\chi}(x):=x^{-iu_0}$ is a lift of $\chi$ to a continuous character of $\mathbf R_{>0}$. As such, $\widetilde{\chi}$ is smooth and multiplication by $\widetilde{\chi}$ preserves the hypotheses on $\phi$.

Now set $\phi_0:=\widetilde{\chi}\phi$ and apply (B.4.1.14) to this choice of $\phi_0$ to obtain, for every $x\in\mathbf R_{>0}$:

$$
\sum_{m\in\mathbf Z:|m|\le N_0}\chi(e^m)\frac{\phi(e^{x^++m})+\phi(e^{x^-+m})}{2}+\sum_{m\in\mathbf Z:|m|>N_0}\chi(e^m)\phi(e^{x+m})=\sum_{m\in\mathbf Z}\mathcal F(\phi_0(e^x))(m)e^{2\pi imx} \tag{B.4.1.15}
$$

and we compute:

$$
\mathcal F(\phi_0(e^x))(y)=\int_{\mathbf R}\widetilde{\chi}(e^x)\phi(e^x)e^{-2\pi ixy}\,\mathrm{d}x=\int_{\mathbf R}e^{-2\pi ix\frac{u_0}{2\pi}}\phi(e^x)e^{-2\pi ixy}\,\mathrm{d}x=\Phi(-iu_0-2\pi iy). \tag{B.4.1.16}
$$

Upon combining (B.4.1.10) and (B.4.1.16), we deduce that we have

$$
\sum_{m\in\mathbf Z:|m|>N_0}\chi(e^m)\frac{\phi((e^m)^+)+\phi((e^m)^-)}{2}+\sum_{m\in\mathbf Z:|m|>N_0}\chi(e^m)\phi(e^m)=\sum_{m\in\mathbf Z}\Phi(-iu_0-2\pi im) \tag{B.4.1.17}
$$

with $\phi(t^{\pm}):=\lim_{u\to t^{\pm}}\phi(u)$ for every $t\in\mathbf R_{>0}$.

We note that the series on the right side of (B.4.1.17) is convergent and invariant under exchanging positive and negative integers, and invariant under the left-translation action on $\Phi$ by $2\pi i\mathbf Z$. In particular, it is independent of the choice of $\log\chi(e)=-iu_0$, since such choice is unique modulo translation of $i\mathbf R$ by $2\pi i\mathbf Z$. $\square$

REMARK B.4.1.5. For the identity in (B.4.1.7) with $\chi=1$, we further refer the reader to **[Horm**, Ch. VII, Thm. 7.2.1**]** in its form of **[Horm**, Ch. VII, p. 178, (7.2.1)$'$**]** applied to $\phi(e^x)$, $a:=2\pi/\log(\theta)$ and $n=1$ (noting that our convention in defining the Fourier transform on the real line follows **[Fol**, Ch. 8, p. 249**]**, resting upon the choice of $\exp(-2\pi ix)$ as additive character of $\mathbf R$, whereas in **[Horm**, Ch. VII, Def. 7.1.1, (7.1.3)**]** the renormalizing factor of $2\pi$ is missing from the chosen additive character $\exp(ix)$).

B.4.1.2. *Cauchy Integrals of $\Phi(s)L'_v(\chi,s)/L_v(\chi,s)$ and weighted Dirac combs.* We give preparations on using the Asymptotic Residue Theorem to compute line integrals of $\Phi(s)L'_v(\chi,s)/L_v(\chi,s)$ with $v$ a finite place of a number field $F$. In what follows we write $L_f(s,\chi)$ for the finite Hecke $L$-function of a continuous (unitary) character $\chi\in\widehat{C_F}$, and $\Phi$ for the entire Mellin transform of a choice of Schwartz function on $\mathbf R_{>0}$ with exponential decay (Definition B.2.1.1(2)).

For $F$ a number field, $\chi\in\widehat{C_F}$ a continuous character, and $\sigma\in\mathbf R$ a real number, the formal sum of Dirac measures

$$
D_{\chi,\mathfrak p}:=\sum_{m>0}\chi(\mathfrak p^m)N(\mathfrak p)^{m\sigma}\delta_{N(\mathfrak p)^m} \tag{B.4.1.18}
$$

will be referred to as the *local Dirac comb* at the maximal ideal $\mathfrak p\subset\mathcal O_F$, assuming $\chi$ is unramified at $\mathfrak p$.

The formal sum $D_{\chi,\mathfrak p}$ consists of terms in the topological dual space $\mathcal S(\mathbf R)'$ (called “tempered distributions”) of the locally convex Schwartz space $\mathcal S(\mathbf R)$, and it makes sense as an element of $\mathcal S(\mathbf R)'$ too: if $f\in\mathcal S(\mathbf R)$ satisfies

## PDF page 611

**B.4. EXPLICIT FORMULAS FOR HECKE $L$-FUNCTIONS** · **611**

$|f(x)|\le A|x|^{-(\sigma+2)}$ for $|x|\ge 1$ then

$$
\sum_{m>0}N(\mathfrak p)^{m\sigma}|f(N(\mathfrak p)^m)|\le A\sum_{m\ge 1}N(\mathfrak p)^{-2}=\frac{A}{N(\mathfrak p)^2-1},
$$

so for any $\varepsilon>0$ if we require $|f(x)|\le B/(1+|x|^{\sigma+2})$ for all $x\in\mathbf R$ and sufficiently small $B$ (depending on $\varepsilon$ and $N(\mathfrak p)$) then $|D_{\chi,\mathfrak p}(f)|<\varepsilon$. The sum $D_{\chi,\mathfrak p}$ therefore converges for the weak topology $\sigma(\mathcal S(\mathbf R)',\mathcal S(\mathbf R))$ on $\mathcal S(\mathbf R)'$ since it converges pointwise.

REMARK B.4.1.6. Although not needed for our purposes, the sum $D_{\chi,\mathfrak p}$ even converges for the strong-dual topology of uniform convergence on bounded subsets of $\mathcal S(\mathbf R)$ in the sense of topological vector spaces (not to be confused with metric-boundedness; see §C.2.1–§C.2.2 for a discussion of topologies on topological duals of Hausdorff locally convex topological vector spaces).

To prove the convergence in the strong-dual topology $\mathcal S(\mathbf R)'_{\beta}$, we first note that $\mathcal S(\mathbf R)$ is complete and barreled (as is any Fréchet space **[Scha**, Ch. II, 7.1**]**) and its closed bounded subsets (in the sense of topological vector spaces) are compact by Lemma D.1.3.7(3). For any barreled Hausdorff locally convex topological vector space $E$, a sequence $\{\varphi_n\}$ in $E'$ that is pointwise convergent (i.e., $\{\varphi_n(x)\}$ is convergent in $\mathbf C$ for all $x\in E$) is pointwise bounded, which is to say it is bounded for the weak topology $\sigma(E',E)$. Thus, by **[Scha**, Ch. IV, 4.6**]** the pointwise limit $\varphi:E\to\mathbf C$ belongs to $E'$ and $\varphi_n\to\varphi$ uniformly on all precompact subsets of $E$. Since bounded subsets have bounded closure **[Scha**, Ch. I, 5.1**]**, if all closed bounded subsets of $E$ are compact (such as for $E=\mathcal S(\mathbf R)$) then $\varphi_n\to\varphi$ uniformly on bounded subsets; i.e., $\varphi_n\to\varphi$ in $E'_{\beta(E',E)}$.

In this subsection we provide a method to compute the value of $D_{\chi,\mathfrak p}$ at certain Schwartz functions on the real line by means of a version of the Poisson Summation Formula from Proposition B.4.1.2 combined with the Asymptotic Residue Theorem (i.e., Theorem B.3.2.1).

LEMMA B.4.1.7 (Poisson Summation and Cauchy Integrals). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character, $\mathfrak p\subset\mathcal O_F$ a prime ideal such that $\chi$ is unramified at $\mathfrak p$. Let $\phi\in\mathcal S_\mathrm{E}(\mathbf R_{>0})$ be a Schwartz function on $\mathbf R_{>0}$ with exponential decay (Definition B.2.1.1(2)).*

*Let*

$$
\Phi(s):=\int_{\mathbf R_{>0}}\phi(t)t^s\frac{\mathrm{d}t}{t} \tag{B.4.1.19}
$$

*be the entire and uniformly Schwartz Mellin transform of $\phi$.*

*Then, for every real number $a>0$, the following identities with absolutely convergent sums hold:*

$$
\log N(\mathfrak p)\sum_{m\in\mathbf Z}\chi(\mathfrak p^m)\phi(N(\mathfrak p)^m)=\sum_{m\in\mathbf Z}\Phi\left(\frac{\log\chi(\mathfrak p)+2\pi im}{\log N(\mathfrak p)}\right)=-\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\Phi(s)\frac{\log N(\mathfrak p)}{1-\chi(\mathfrak p)^{-1}N(\mathfrak p)^s}\,\mathrm{d}s \tag{B.4.1.20}
$$

*for any choice of $\log\chi(\mathfrak p)$.*

We provide a proof of Lemma B.4.1.7 below.

REMARK B.4.1.8. The identity is obtained upon combining **[Den**, (2.13)**]** with **[Den**, (2.18)**]** and **[Den**, (2.19)**]**, noting that $\Phi$ fulfils the requirements of **[Den**, Thm.1.7**]** (which are only needed for $\widetilde{a}=a$, in the notation of loc.cit.). Indeed, since $\phi$ is Schwartz and with exponential decay, then $\Phi(\sigma+ix)$ is Schwartz as a function of $x$ for every $\sigma$, and in fact uniformly for $\sigma$ varying over bounded intervals, by Lemma B.2.1.9(2). This implies that $\Phi$ satisfies conditions **[Den**, Thm.1.7,(1),(2)**]**. We need only show that condition **[Den**, Thm.1.7,(3)**]** is also satisfied. This is a consequence of Lemma B.2.1.9(3).

The identity in (B.4.1.20) therefore holds by **[Den**, (2.18)**]**. Note that the restriction on $a$ to satisfy $a\le 2$ in **[Den**, Thm.1.17**]** (with $w=0$ there) is unnecessary for the arguments proving **[Den**, (2.18)**]** to hold, and it

## PDF page 612

**612** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

is only used to obtain the identity in **[Den**, Thm.1.7,(4)**]** by accessing the estimates from **[Lang-b**, Ch. XVII, Prop. 2.7**]**.

LEMMA B.4.1.9. *The following identity holds for $z\in\mathbf C-\mathbf Z$:*

$$
(1-e^{2\pi iz})^{-1}=\frac{1}{2}-\frac{1}{2\pi iz}-\frac{1}{2\pi i}\sum_{m\in\mathbf Z-\{0\}}\left(\frac{1}{z-m}+\frac{1}{m}\right) \tag{B.4.1.21}
$$

*where the series in the rightmost side of (B.4.1.21) is absolutely and locally uniformly convergent over $\mathbf C-\mathbf Z$. Moreover, for every real number $a\ne 0$, we have on the horizontal line $\{\operatorname{Im}(z)=a\}$:*

$$
\left|\sum_{m\in\mathbf Z-\{0\}}\left(\frac{1}{z-m}+\frac{1}{m}\right)\right|\le C_a \tag{B.4.1.22}
$$

*and*

$$
\sum_{m\in\mathbf Z-\{0\}}\left|\frac{1}{z-m}+\frac{1}{m}\right|\le C'_a|z| \tag{B.4.1.23}
$$

*where $C_a,C'_a>0$ are constants depending only on $a$.*

PROOF. Let $A>0$ be a real number, and $z\in\mathbf C$ be such that $|z|\le A$. For any integer $m$ such that $|m|\ge 2A$, we have

$$
\left|\frac{1}{z-m}+\frac{1}{m}\right|=\frac{|z|}{|m(z-m)|}\le\frac{A}{|m|\cdot||z|-|m||}\le\frac{2A}{|m|^2}
$$

and so for any $A>0$, the series in the rightmost side of (B.4.1.21) is the sum of a series that converges absolutely and uniformly over the closed ball of radius $A$ and centered at the origin, and finitely many meromorphic functions of the form $\frac{1}{z-m}+\frac{1}{m}$. This shows that the series converges absolutely and uniformly on the compact subsets of $\mathbf C-\mathbf Z$.

From the classical identity

$$
\psi(1-z)=-\gamma+\sum_{m\ge 1}\left(\frac{1}{z-m}+\frac{1}{m}\right) \tag{B.4.1.24}
$$

for $\psi(z):=\Gamma'(z)/\Gamma(z)$ over $\mathbf C-\mathbf N_{>0}$, we likewise have (evaluating with $-z$)

$$
\psi(z+1)=-\gamma-\sum_{m\le-1}\left(\frac{1}{m}+\frac{1}{z-m}\right) \tag{B.4.1.25}
$$

over $\mathbf C-\mathbf N_{<0}$. Moreover, from $\Gamma(z+1)=z\Gamma(z)$ we obtain

$$
\psi(z+1)=\psi(z)+1/z \tag{B.4.1.26}
$$

over $\mathbf C-\mathbf N_{\le 0}$. Taking the log-derivative of Euler’s reflection formula for the $\Gamma$-function (i.e. $\Gamma(z)\Gamma(1-z)=\pi/\sin(\pi z)$, valid over $\mathbf C-\mathbf Z$) yields

$$
\psi(1-z)-\psi(z)-\frac{1}{z}=\pi\cot(\pi z)-\frac{1}{z} \tag{B.4.1.27}
$$

over $\mathbf C-\mathbf Z$.

By (B.4.1.24), (B.4.1.25), and (B.4.1.26), the left side of (B.4.1.27) agrees with $\sum_{m\in\mathbf Z-\{0\}}\left(\frac{1}{z-m}+\frac{1}{m}\right)$. Since we have

$$
\pi\cot(\pi z)=\pi i\frac{e^{\pi iz}+e^{-\pi iz}}{e^{\pi iz}-e^{-\pi iz}}=\frac{2\pi i}{2}\frac{e^{2\pi iz}-1+2}{e^{2\pi iz}-1}=\pi i+2\pi i\frac{1}{e^{2\pi iz}-1}, \tag{B.4.1.28}
$$

## PDF page 613

**B.4. EXPLICIT FORMULAS FOR HECKE $L$-FUNCTIONS** · **613**

the identity in (B.4.1.21) holds over $\mathbf C-\mathbf Z$. From (B.4.1.27) and (B.4.1.28) we deduce for $z=\sigma+ia$ with $\sigma\in\mathbf R$ and real $a\ne 0$ that

$$
\left|\sum_{m\in\mathbf Z-\{0\}}\left(\frac{1}{z-m}+\frac{1}{m}\right)\right|=\left|\pi i+\frac{2\pi i}{e^{2\pi i\sigma}e^{-2\pi a}-1}-\frac{1}{\sigma+ia}\right|\le C_a \tag{B.4.1.29}
$$

which is (B.4.1.22).

To obtain (B.4.1.23) we proceed as follows. Over $\mathbf C-(\mathbf Z-\{0\})$ we have

$$
\sum_{m\in\mathbf Z-\{0\}}\left|\frac{1}{z-m}+\frac{1}{m}\right|=|z|\sum_{m\in\mathbf Z-\{0\}}\left|\frac{1}{(z-m)m}\right|\le|z|(2\zeta(2))^{1/2}\left(\sum_{m\in\mathbf Z-\{0\}}\frac{1}{|z-m|^2}\right)^{1/2} \tag{B.4.1.30}
$$

by the Cauchy-Schwartz inequality.

The series $\sum_{m\in\mathbf Z-\{0\}}\frac{1}{|z-m|^2}$ in (B.4.1.30) is absolutely and locally uniformly convergent over $\mathbf C-(\mathbf Z-\{0\})$, and its sum is continuous and horizontally $1$-periodic. In particular, it is bounded on all horizontal lines $\{\operatorname{Im}(z)=a\}$ for all real numbers $a\ne 0$. We call its sum $A_a$, and define $C'_a:=(2\zeta(2))^{1/2}A_a^{1/2}$ to see that (B.4.1.23) holds. $\square$

PROOF OF LEMMA B.4.1.7. We proceed as in **[Den**, p. 8**]** and observe that upon setting

$$
z:=\frac{1}{2\pi i}(s\log N(\mathfrak p)-\log\chi(\mathfrak p)) \tag{B.4.1.31}
$$

in (B.4.1.21), since $\mathrm{d}/\mathrm{d}s=((\log N(\mathfrak p))/(2\pi i))\,\mathrm{d}/\mathrm{d}z$ and

$$
L_{\mathfrak p}(s,\chi)=\frac{1}{1-\chi(\mathfrak p)(N\mathfrak p)^{-s}}=\frac{1}{1-e^{-2\pi iz}}
$$

has $z$-derivative $2\pi i/(1-e^{2\pi iz})$, we obtain

$$
\frac{L'_{\mathfrak p}(s,\chi)}{L_{\mathfrak p}(s,\chi)}=\frac{1}{2}\log N(\mathfrak p)-\frac{1}{s-\frac{\log\chi(\mathfrak p)}{\log N(\mathfrak p)}}-\sum_{m\in\mathbf Z-\{0\}}\left(\frac{1}{s-\frac{\log\chi(\mathfrak p)+2\pi im}{\log N(\mathfrak p)}}+\frac{\log N(\mathfrak p)}{2\pi im}\right). \tag{B.4.1.32}
$$

The change of variables in (B.4.1.31) is affine-linear and hence by Lemma B.4.1.9 the series on the right side of (B.4.1.32) is absolutely and locally uniformly convergent on compact subsets away from the image of the integers under the inverse of (B.4.1.31), which is the discrete set $\log\chi(\mathfrak p)+(2\pi i/N(\mathfrak p))\mathbf Z$.

For any $\sigma\ne 0$, the estimate in (B.4.1.23) from Lemma B.4.1.9 applied to

$$
z=\left(\frac{\log N(\mathfrak p)}{2\pi}t-\frac{\log\chi(\mathfrak p)}{2\pi i}\right)+\frac{\log N\mathfrak p}{2\pi}\sigma i
$$

(decomposition into real and imaginary parts) translates into the estimate over $\sigma+i\mathbf R$:

$$
\frac{1}{\left|\sigma+it-\frac{\log\chi(\mathfrak p)}{\log N(\mathfrak p)}\right|}+\sum_{m\in\mathbf Z-\{0\}}\left|\frac{1}{\sigma+it-\frac{\log\chi(\mathfrak p)+2\pi im}{\log N(\mathfrak p)}}+\frac{\log N(\mathfrak p)}{2\pi im}\right|\le C_{\mathfrak p,\sigma}|t|. \tag{B.4.1.33}
$$

As in **[Den**, (2.13)**]**, we obtain:

$$
\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\Phi(s)\frac{L'_{\mathfrak p}(s,\chi)}{L_{\mathfrak p}(s,\chi)}\,\mathrm{d}s=\frac{1}{4\pi i}\log N(\mathfrak p)\int_{a-i\infty}^{a+i\infty}\Phi(s)\,\mathrm{d}s-\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\frac{\Phi(s)}{s-\frac{\log\chi(\mathfrak p)}{\log N(\mathfrak p)}}\,\mathrm{d}s
$$

$$
-\sum_{m\in\mathbf Z-\{0\}}\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\Phi(s)\left(\frac{1}{s-\frac{\log\chi(\mathfrak p)+2\pi im}{\log N(\mathfrak p)}}+\frac{\log N(\mathfrak p)}{2\pi im}\right)\,\mathrm{d}s
$$

## PDF page 614

**614** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

where the exchange of the order of summation and integration is valid by Dominated Convergence using $C_{\mathfrak p,\sigma}|\Phi(\sigma+it)||t|$ as a majorant, as provided by (B.4.1.33) which is integrable over $\sigma+i\mathbf R$ for each $\sigma\ne 0$ since $\Phi$ is Schwartz on vertical lines by Lemma B.2.1.9.

We have $\int_{a+i\mathbf R}\Phi(s)\,\mathrm{d}s=\int_{a+i\mathbf R}(s\Phi(s)/s)\,\mathrm{d}s=0$ by Theorem B.2.2.4(2) with $N=0$, so

$$
\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\Phi(s)\frac{L'_{\mathfrak p}(s,\chi)}{L_{\mathfrak p}(s,\chi)}\,\mathrm{d}s=-\frac{1}{2\pi i}\sum_{m\in\mathbf Z}\int_{a-i\infty}^{a+i\infty}\frac{\Phi(s)}{s-\frac{\log\chi(\mathfrak p)+2\pi im}{\log N(\mathfrak p)}}\,\mathrm{d}s \tag{B.4.1.34}
$$

which by (B.2.2.6) from Theorem B.2.2.4 (with $N=0$ and pure imaginary $z=(\log\chi(\mathfrak p)+2\pi im)/\log N\mathfrak p$) gives

$$
\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\Phi(s)\frac{L'_{\mathfrak p}(\chi,s)}{L_{\mathfrak p}(\chi,s)}\,\mathrm{d}s=-\sum_{m\in\mathbf Z}\Phi\left(\frac{\log\chi(\mathfrak p)+2\pi im}{\log N(\mathfrak p)}\right). \tag{B.4.1.35}
$$

By Proposition B.4.1.2 with $\theta=N(\mathfrak p)$, and noting that $L'_{\mathfrak p}(s,\chi)/L_{\mathfrak p}(s,\chi)=\log N(\mathfrak p)/(1-\chi(\mathfrak p)^{-1}N(\mathfrak p)^s)$, we see that (B.4.1.20) holds. $\square$

**B.4.2. Explicit formulas from the Asymptotic Residue Theorem.** We let $\phi\in\mathcal S(\mathbf R_{>0})$ be a Schwartz function with exponential decay, and $\Phi(s):=M(\phi)(s)$ its entire Mellin transform.

B.4.2.1. *Logarithmic derivative of completed $L(s,\chi)$ and the Asymptotic Residue Formula.* By **[Lang-b**, Ch. XVII, Prop. 2.3, Cor. 2.5, Prop. 2.7**]**, the function

$$
f(s)=\frac{L'(s,\chi)}{L(s,\chi)} \tag{B.4.2.1}
$$

has slow growth near its poles (in the sense of Definition B.3.1.1)) over the vertical strip $\mathbf C_{(1-a,a)}$ for any $1<a\le 2$. Moreover, $\Phi$ is uniformly Schwartz over any vertical strip. Upon replacing $a$ with $a-\varepsilon$ for small enough $\varepsilon>0$ so that $a>1$ and $f$ has no poles on $\sigma=a,1-a$, we may apply the Asymptotic Residue Theorem (namely Theorem B.3.2.1) to obtain the identity with convergence on both sides

$$
\delta_{\chi}(\Phi(0)+\Phi(1))-\sum_{\rho:L(\rho,\chi)=0}\Phi(\rho)=\lim_{T\to+\infty}\sum_{\rho:|\operatorname{Im}(\rho)|<T}\Phi(\rho)n_{\rho}
$$

where the right side has terms indexed by the poles of $L'(s,\chi)/L(s,\chi)$ (counted *without* multiplicity) contained within $\mathbf C_{(1-a,a)}$ and $n_{\rho}:=\operatorname{ord}_{\rho}(L(s,\chi))$ the residue at $\rho$, and the left side having terms indexed by the zeros of $L(s,\chi)$ (counted *with* multiplicity) and being shorthand notation for the limit:

$$
\lim_{T\to+\infty}\sum_{\rho:L(\rho,\chi)=0,|\operatorname{Im}(\rho)|<T}\Phi(\rho).
$$



The Asymptotic Residue Formula says

$$
-\frac{1}{2\pi i}\int_{1-a-i\infty}^{1-a+i\infty}\Phi(s)\frac{L'(s,\chi)}{L(s,\chi)}\,\mathrm{d}s+\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\Phi(s)\frac{L'(s,\chi)}{L(s,\chi)}\,\mathrm{d}s=-\delta_{\chi}(\Phi(0)+\Phi(1))+\sum_{\rho:L(\rho,\chi)=0}\Phi(\rho) \tag{B.4.2.2}
$$

Upon using the functional equation from Proposition 3.2.1.3(3) (and expressing$^{13}$ $\epsilon(s,\chi)$ there as a product involving the factor $A_{\chi}^{\alpha s+\beta}$), we have

$$
\frac{L'(s,\chi)}{L(s,\chi)}=\frac{L'(\bar\chi,1-s)}{L(\bar\chi,1-s)}+\log(A_{\chi}) \tag{B.4.2.3}
$$

where

$$
A_{\chi}:=|N(\mathfrak{d}_{F/\mathbf Q})|\cdot N(\mathfrak f_{\chi}).
$$

$^{13}$Should a precise reference be given here for the expression for $\epsilon(s,\chi)$ being invoked?

## PDF page 615

**B.4. EXPLICIT FORMULAS FOR HECKE $L$-FUNCTIONS** · **615**

Thus, the following identity holds:

$$
\frac{\log(A_{\chi})}{2\pi i}\int_{1-a-i\infty}^{1-a+i\infty}\Phi(s)\,\mathrm{d}s+\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\Phi(1-s)\frac{L'(s,\bar\chi)}{L(s,\bar\chi)}\,\mathrm{d}s+\frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty}\Phi(s)\frac{L'(s,\chi)}{L(s,\chi)}\,\mathrm{d}s \tag{B.4.2.4}
$$

$$
=-\delta_{\chi}(\Phi(0)+\Phi(1))+\sum_{\rho:L(\rho,\chi)=0}\Phi(\rho).
$$

Since $a>1$, absolute and uniform convergence of the Euler product for $L_f(s,\chi)$ in right half-planes $\operatorname{Re}(s)\ge 1+\varepsilon$ implies the absolute and uniform convergence of the series:

$$
\frac{L'(s,\chi)}{L(s,\chi)}=\sum_{v\in\Sigma_F}\frac{L'_v(s,\chi)}{L_v(s,\chi)} \tag{B.4.2.5}
$$

over the vertical line $\operatorname{Re}(s)=a$, where $L_v(\chi,s)$ are the local factors of $L(s,\chi)$ defined in (3.2.1.1) and (3.2.1.3). The same holds for

$$
\frac{L'(s,\bar\chi)}{L(s,\bar\chi)}=\sum_{v\in\Sigma_F}\frac{L'_v(s,\bar\chi)}{L_v(s,\bar\chi)}. \tag{B.4.2.6}
$$

We further observe that

$$
\frac{L'_v(s,\chi)}{L_v(s,\chi)}=-\log N(\mathfrak p_v)\sum_{m>0}\frac{\chi(\mathfrak p_v)^m}{N(\mathfrak p_v)^{ms}},\quad \frac{L'_v(s,\bar\chi)}{L_v(s,\bar\chi)}=-\log N(\mathfrak p_v)\sum_{m>0}\frac{\bar\chi(\mathfrak p_v)^m}{N(\mathfrak p_v)^{ms}} \tag{B.4.2.7}
$$

for every finite place $v$ of $F$, where the series converge absolutely and uniformly over the vertical line $\operatorname{Re}(s)=a$, since $a>1$. This is the starting point of the proof of the Explicit Formulas of Weil (see **[Weil-b]**, **[Lang-b**, Ch. XVII, Thm. 3.1**]**, and **[Bar**, Thm. 1**]**).

B.4.2.2. *Non-Archimedean local factors.* We analyze, for each finite place $v$ of $F$, the integral:

$$
\log N(\mathfrak p_v)\int_{a-i\infty}^{a+i\infty}\Phi(s)\sum_{m>0}\frac{\chi(\mathfrak p_v)^m}{N(\mathfrak p_v)^{ms}}\,\mathrm{d}s. \tag{B.4.2.8}
$$

By Dominated Convergence, we are allowed to interchange the order of summation and integration to get

$$
\log N(\mathfrak p_v)\sum_{m>0}\chi(\mathfrak p_v)^m\int_{a-i\infty}^{a+i\infty}\frac{\Phi(s)}{N(\mathfrak p_v)^{ms}}\,\mathrm{d}s=\log N(\mathfrak p_v)\sum_{m>0})\frac{i\chi(\mathfrak p_v)^m}{N(\mathfrak p_v)^{ma}}\int_{-\infty}^{+\infty}\frac{\Phi(a+it)}{N(\mathfrak p_v)^{imt}}\,\mathrm{d}t. \tag{B.4.2.9}
$$

By viewing $\Phi(a+it)\in\mathcal S(\mathbf R)$ and $N(\mathfrak p_v)^{imt}$ as tempered distributions for $m>0$, Mellin/Fourier inversion (for $\phi\in\mathcal S(\mathbf R_{>0})$) gives the identity:

$$
\log N(\mathfrak p_v)\frac{\chi(\mathfrak p_v)^m}{N(\mathfrak p_v)^{ma}}\int_{-\infty}^{+\infty}\frac{\Phi(a+it)}{N(\mathfrak p_v)^{imt}}\,\mathrm{d}t=\log N(\mathfrak p_v)\chi(\mathfrak p_v)^m\,\delta_{N(\mathfrak p_v)^m}(\phi) \tag{B.4.2.10}
$$

where $\delta_{N(\mathfrak p_v)^m}$ is Dirac’s $\delta$-distribution. Similarly, we obtain (using that $\mathrm{d}s=i\,\mathrm{d}t$ and $1-s=(1-a)-it$)

$$
\log N(\mathfrak p_v)\int_{a-i\infty}^{a+i\infty}\Phi(1-s)\frac{\bar\chi(\mathfrak p_v)^m}{N(\mathfrak p_v)^{ms}}\,\mathrm{d}s=-i\log N(\mathfrak p_v)\frac{\bar\chi(\mathfrak p_v^m)}{N(\mathfrak p_v)^m}\delta_{N(\mathfrak p_v)^{-m}}(\phi) \tag{B.4.2.11}
$$

B.4.2.3. *Archimedean Local Factors.* We now fix $v$ an Archimedean place.

We have:

$$
\frac{L'_v(s,\chi)}{L_v(s,\chi)}=-\alpha_v+\frac{1}{a_v}\frac{\Gamma'\left(\frac{s-s_v}{a_v}\right)}{\Gamma\left(\frac{s-s_v}{a_v}\right)} \tag{B.4.2.12}
$$

## PDF page 616

**616** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

where $\alpha_v = -\frac{1}{2}\log(\pi)$ if $v$ is real, $\alpha_v = -\log(2\pi)$ if $v$ is complex, and $a_v = [\mathbf{C} : F_v]$. The complex number $s_v$ is purely imaginary and completely determined by the restriction of the continuous character $\chi \in \widehat{C_F}$ to $F_v^\times$.

We analyze the line integral from (B.4.2.4):

$$
\tag{B.4.2.13} \frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty} \left\{\Phi(s)\frac{L'_v(s,\chi)}{L_v(s,\chi)} + \Phi(1-s)\frac{L'_v(s,\overline{\chi})}{L_v(s,\overline{\chi})}\right\} \mathrm{d}s.
$$

PROPOSITION B.4.2.1. *Let $F$ be a number field, $\chi \in \widehat{F_v^\times}$ a continuous character of $F_v^\times$ for an Archimedean place $v$ of $F$. For any real number $a > 1$, the line integral:*

$$
\tag{B.4.2.14} \frac{1}{2\pi i}\int_{a-i\infty}^{a+i\infty} \left\{\Phi(s)\frac{L'_v(s,\chi)}{L_v(s,\chi)} + \Phi(1-s)\frac{L'_v(s,\overline{\chi})}{L_v(s,\overline{\chi})}\right\} \mathrm{d}s
$$

*equals:*

$$
\tag{B.4.2.15} \int_0^{+\infty} \left\{\frac{N_v\phi(1)}{x} - (\phi(e^x)e^{s_v x} + \phi(e^{-x})e^{-s_v x})\frac{e^{(\frac{2}{N_v}-\frac{1}{2})x}}{1-e^{-\frac{2}{N_v}x}}\right\} \mathrm{d}x
$$

*where $N_v = 1$ if $v$ is real, $N_v = 2$ if $v$ is complex, and $s_v \in i\mathbf{R}$ satisfies $\chi_v(t) = t^{s_v}$ for $t \in \mathbf{R}_{>0} \subset F_v^\times$.*

PROOF. $^{14}$Upon writing $s_v = -i\varphi$, the proof in [**Bar**, p.150] applies, upon observing that by Stirling's Formula for $\Gamma(z)$ we may and do apply the Asymptotic Residue Theorem (see Theorem B.3.2.1) to replace the vertical line of integration $\mathrm{Re}(s) = a$ with the vertical line $\mathrm{Re}(s) = 1/2$, without picking up any residue.

The line integral in (B.4.2.14) therefore equals:

$$
\tag{B.4.2.16} \frac{1}{2\pi i}\int_{1/2-i\infty}^{1/2+i\infty} \Phi(s)\left\{\frac{\Gamma'}{\Gamma}\left(\frac{N_v(s+i\varphi)}{2}\right) + \frac{\Gamma'}{\Gamma}\left(\frac{N_v(1-s-i\varphi)}{2}\right)\right\} \mathrm{d}s.
$$

A change of variables in (B.4.2.16) combined with [**Bar**, Proposition, p. 146], applied to $\phi$ Schwartz with exponential decay, gives (B.4.2.15). We note that in this special case, [**Bar**, Proposition, p. 146] is classical and due to Euler. The equality between (B.4.2.15) and (B.4.2.16) is a consequence of Mellin/Fourier inversion (which is especially tractable since $\phi \in \mathcal{S}(\mathbf{R}_{>0})$ with exponential decay). $\square$

B.4.2.4. *Explicit Formulas for Hecke $L$-functions.* We can now collect the results obtained in the previous subsections into the following result:$^{15}$

THEOREM B.4.2.2 (Explicit Formulas for Hecke $L$-functions). *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character, $\phi \in \mathcal{S}(\mathbf{R})$ a Schwartz function with exponential decay, $\Phi(s) := M(\phi)(s)$ its Mellin transform. The following identity holds:*

(B.4.2.17)

$$
-\Phi(-1/2) - \Phi(1/2) + \sum_{\rho:L(\rho,\chi)=0} \Phi(\rho-1/2) = \phi(1)\log(A_\chi)
$$

$$
- \sum_{v\in\Sigma_{F,f}}\sum_{m>0} \frac{\log N(\mathfrak{p}_v)}{N(\mathfrak{p}_v)^{m/2}}\left\{\chi(\mathfrak{p}_v)^m\phi(N(\mathfrak{p}_v)^m) + \overline{\chi}(\mathfrak{p}_v)^m\phi(N(\mathfrak{p}_v)^{-m})\right\}
$$

$$
+ \sum_{v\in S_\infty}\int_0^{+\infty} \left\{\frac{N_v\phi(1)}{x} - (\phi(e^x)e^{s_v x} + \phi(e^{-x})e^{-s_v x})\frac{e^{(\frac{2}{N_v}-\frac{1}{2})x}}{1-e^{-\frac{2}{N_v}x}}\right\} \mathrm{d}x.
$$

$^{14}$Brian still needs to check proof of this by reading [**Bar**, pp. 150-1], make sure formulas are correct.

$^{15}$Brian should double-check this.

## PDF page 617

**B.4. EXPLICIT FORMULAS FOR HECKE L-FUNCTIONS** · **617**

Proof. The identity in (B.4.2.17) is obtained by combining (B.4.2.2) with (B.4.2.5), (B.4.2.6), (B.4.2.7), (B.4.2.10) and (B.4.2.11), together with Proposition B.4.2.1. $\square$

We note that the main difficulty in the proof of the main result in [Weil-b], explained in [Lang-a, Ch. X], and in [Bar], further explained in [Lang-b, Ch. XVII] stems from dropping any smoothness assumptions on the test function $\phi$. As discussed in this section, under the additional assumption that $\phi$ be Schwartz and with exponential decay the Explicit Formulas are ultimately a consequence of the Residue Theorem in its asymptotic version of Theorem B.3.2.1, and Mellin/Fourier inversion.

B.4.3. Fourier transform of $\log|\cdot|_v$. Let $F$ be a number field, $v$ a fixed place of $F$.

In this subsection we illustrate results of Connes from [Co, Appendix II, pp. 72-76], identifying the Fourier transform of the function $J_v := \log|\cdot|_v$, as a tempered distribution on $F_v$; i.e., an element of $\mathcal{S}(F_v)'$ (we further refer the reader to §2.1 for more on Schwartz-Bruhat functions on a Hausdorff locally compact abelian group; see also [Bru, §9]), the topological dual of the Hausdorff locally convex space $\mathcal{S}(F_v)$ of Schwartz-Bruhat functions on the Hausdorff locally compact additive abelian group $(F_v,+)$ of the local field $F_v$.

B.4.3.1. Calculation of the additive local Fourier transform of $\log|\cdot|_v$. We recall that we denote by:

$$
\tag{B.4.3.1} \rho_v : F_v^\times \times \mathcal{S}(F_v) \to \mathcal{S}(F_v)
$$

the continuous left-translation action of $F_v^\times$ on $\mathcal{S}(F_v)$ (see also, in the case $v$ is non-Archimedean, Lemma 6.1.2.2 for a study of the invariants and co-invariants under the induced action of $\mathcal{O}_{F_v}^\times \subset F_v^\times$, and to Theorem 3.4.3.3 for a classification of the homogeneous elements of $\mathcal{S}(F_v)'_\beta$ and Proposition 5.5.3.1 for a study of $\mathcal{S}(F_v)'_\beta$ in terms of its homogeneous elements). Explicitly, $\rho_v(g,f)(x) = f(g^{-1}x)$.

Let $F$ be a number field, $v$ a place of $F$. We denote by $\alpha_{v,0}$ the standard additive character of the local field $F_v$, as defined in Example A.3.1.8 and Example A.3.1.9. With respect to this choice of character, the additive Tamagawa measure $\nu_v$ on $F_v$ is self-dual, i.e. it is its own Plancherel measure under the isomorphism of Hausdorff locally compact abelian groups $F_v \simeq \widehat{F_v}$ induced by the choice of $\alpha_{v,0}$.

PROPOSITION B.4.3.1 (Fourier transform of $\log|\cdot|_v$ - non-Archimedean places). *Let $F$ be a number field, $v$ a non-Archimedean place. Let $|\cdot|_v$ be the normalized absolute value on $F$ and $F_v$ the completion of $F$ with respect to $|\cdot|_v$.*

*The Fourier transform $\widehat{J_v} \in \mathcal{S}(F_v)'$, defined relative to the standard additive character $\alpha_{v,0}$ of $F_v$, of the function*

$$
\tag{B.4.3.2} J_v(x) := \frac{\log|x|_v}{\log(q_v)}
$$

*of $x \in F_v$ (where $q_v$ is the size of the residue field at $v$) satisfies the following conditions:*

*(1) As tempered distributions on $F_v$, we have:*

$$
\tag{B.4.3.3} \rho'_v(g,\widehat{J_v}) = \widehat{J_v} - \frac{\log|g|_v}{\log(q_v)}\delta_0
$$

*where $\rho'_v$ is the adjoint action on $\mathcal{S}(F_v)'$. Explicitly, for any $f \in \mathcal{S}(F_v)$, we have*

$$
\tag{B.4.3.4} \langle\widehat{J_v},\rho_v(g,f)\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = \langle\widehat{J_v},f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} - \frac{\log|g|_v}{\log(q_v)}f(0)
$$

*for every $g \in F_v^\times$.*

*(2) For every $f \in C_c^\infty(F_v^\times) \subset \mathcal{S}(F_v)$, we have*

$$
\tag{B.4.3.5} \langle\widehat{J_v},f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = -\frac{1}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{F_v^\times} f(g)\,\mathrm{d}\mu_v(g)
$$

## PDF page 618

**618** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

*where $\mu_v$ is the local multiplicative Tamagawa measure on $F_v^\times$ from Definition A.3.2.2.*

*The function $J_v \in \mathcal{S}(F_v)$ is unique for the properties of vanishing at 1 and satisfying (B.4.3.5).*

The meaning of “adjoint action” $\rho'_v$ in (B.4.3.3) is the effect of the linear dual of the action of $g$.

PROOF. The identity, for all $g \in F_v^\times$:

$$
\tag{B.4.3.6} \int_{F_v} \rho_v(g,f)(x)\overline{\psi}_v(xy)\,\mathrm{d}\nu_v(x) = |g|_v\rho_v(g^{-1},\widehat{f})(y)
$$

where $\nu_v$ is the local additive Tamagawa measure on $F_v$ from Definition A.3.1.2, and $\psi_v$ is the normalized additive character chosen as in [**CF**, Ch. XV, §2.5, p. 319] implies

$$
\tag{B.4.3.7} \langle\widehat{J_v},\rho_v(g,f)\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = \langle J_v,\widehat{\rho_v(g,f)}\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'_\beta} = \langle J_v,|g|_v\rho_v(g^{-1},\widehat{f})\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'}.
$$

We compute

(B.4.3.8)

$$
\langle J_v,|g|_v\rho_v(g^{-1},\widehat{f})\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = |g|_v\int_{F_v} \widehat{f}(gx)\frac{\log|x|_v}{\log(q_v)}\,\mathrm{d}\nu_v(x) = \int_{F_v} \widehat{f}(x)\frac{\log|x|_v}{\log(q_v)}\,\mathrm{d}\nu_v(x) - \frac{\log|g|_v}{\log(q_v)}f(0)
$$

for all $g \in F_v^\times$, so the left side of (B.4.3.7) equals

$$
\langle\widehat{J_v},f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} - \frac{\log|g|_v}{\log(q_v)}\langle\delta_0,f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'}.
$$

This says that (B.4.3.3) holds.

If $f \in C_c^\infty(F_v^\times) \subset \mathcal{S}(F_v)$ then $f(0) = 0$, so (B.4.3.3) gives that $\widehat{J_v}$ is $F_v^\times$-invariant on $C_c^\infty(F_v^\times)$. By [?, Rem. p. 27], for any locally profinite group $G$ the space of left $G$-invariant linear functionals on $C_c^\infty(G)$ is 1-dimensional. Thus, for $G = F_v^\times$ that space is generated by

$$
L_0 : f \mapsto \langle L_0,f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} := \int_{F_v^\times} f(g)\,\mathrm{d}\mu_v(g).
$$

There therefore exists a unique complex number $A \in \mathbf{C}$, $A \neq 0$, such that $\widehat{J_v} = AL_0$ on the subspace $\ker(\delta_0) \subset C_c^\infty(F_v^\times)$ of $\mathcal{S}(F_v)$. This determines $\widehat{J_v}$ up to a nonzero constant and adding a scalar multiple of $\delta_0$.

We have, upon choosing $f = 1_{\mathcal{O}_{F_v}^\times}$:

$$
\tag{B.4.3.9} \langle L_0,f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = \int_{F_v^\times} f(g)\,\mathrm{d}\mu_v(g) = \mu_v(\mathcal{O}_{F_v}^\times).
$$

We write $1_{\mathcal{O}_{F_v}^\times} = 1_{\mathcal{O}_{F_v}} - \rho_v(\pi_v,1_{\mathcal{O}_{F_v}})$ and from (B.4.3.4) we obtain

(B.4.3.10)

$$
\langle\widehat{J_v},1_{\mathcal{O}_{F_v}^\times}\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = \langle\widehat{J_v},1_{\mathcal{O}_{F_v}} - \rho_v(\pi_v,1_{\mathcal{O}_{F_v}})\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = \langle\widehat{J_v},1_{\mathcal{O}_{F_v}}\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} - \langle\widehat{J_v},1_{\mathcal{O}_{F_v}}\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} - 1
$$

which reads:

$$
\tag{B.4.3.11} \langle\widehat{J_v},1_{\mathcal{O}_{F_v}^\times}\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = -1.
$$

Upon combining (B.4.3.10) with (B.4.3.9), we deduce that indeed $A = -1/\mu_v(\mathcal{O}_{F_v}^\times)$, and so (B.4.3.5) holds. The condition (2) on $\widehat{J_v}$ thereby determines $\widehat{J_v}$ up to adding an element of $\mathbf{C}\delta_0$ and so determines $J_v$ as a distribution up to adding an element of $\mathbf{C}\widehat{\delta}_0 = \mathbf{C}$. Thus, requiring $J_v(1) = 0$ gives uniqueness. $\square$

We now proceed to compute the Fourier transform of the tempered distribution $\log|\cdot|_v$ on $F_v$ for $v$ an Archimedean place of the number field $F$. Throughout the Proposition below, $\gamma$ denotes Euler's constant determined by the equation

$$
\frac{\Gamma'(\frac{1}{2})}{\Gamma(\frac{1}{2})} = -\gamma - 2\log(2).
$$

## PDF page 619

**B.4. EXPLICIT FORMULAS FOR HECKE L-FUNCTIONS** · **619**

PROPOSITION B.4.3.2 (Fourier transform of $\log|\cdot|_v$ - Archimedean places). *Let $F$ be a number field, $v$ an Archimedean place. Let $|\cdot|_v$ be the normalized absolute value on $F$ and $F_v$ the completion of $F$ with respect to $|\cdot|_v$.*

*The Fourier transform $\widehat{J_v} \in \mathcal{S}(F_v)'$, defined relative to the standard additive character $\alpha_{v,0}$ of $F_v$, of the function*

$$
\tag{B.4.3.12} J_v(x) := \log|x|_v
$$

*of $x \in F_v$, is computed according to the following formulas:*

*(1) If $v$ is real, then we have:*

$$
\tag{B.4.3.13} \langle\widehat{J_v},f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = -\lim_{\varepsilon\to 0^+}\left(\int_{|x|\ge\varepsilon} f(x)\,\frac{\mathrm{d}x}{|x|} + 2f(0)\log(\varepsilon)\right) - 2(\log(2\pi)+\gamma)f(0)
$$

*for every $f \in \mathcal{S}(\mathbf{R})$.*

*(2) If $v$ is complex, then we have:*

$$
\tag{B.4.3.14} \langle\widehat{J_v},f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'} = -\lim_{\varepsilon\to 0^+}\left(\int_{|z|^2\ge\varepsilon} f(x)\,\frac{|\mathrm{d}z\wedge \mathrm{d}\bar{z}|}{|z|^2} + 2\pi f(0)\log(\varepsilon)\right) - 4\pi(\log(2\pi)+\gamma)f(0)
$$

*for every $f \in \mathcal{S}(\mathbf{C})$.*

For the above calculations, we refer the reader to the proof of [Co, Appendix II, Lemma 2, p. 72],$^{16}$ and specifically to [Co, (32), (33), (34), p.73], and [Co, (41), (42), p. 75]. Note that the local multiplicative Tamagawa measures $\mu_v$ we are using in (B.4.3.2) are not the canonical measures on the $\mathbf{R}_{>0}$-modulated groups $\mathbf{R}^\times$ and $\mathbf{C}^\times$: these are obtained by dividing by 2 for $v$ real, and by $2\pi$ for $v$ complex, thus explaining the additional factors of 2, respectively $2\pi$ (i.e. the volumes of the respective “local unit groups” $\{|x| = 1\} \subset F_v^\times$) in the above formulas compared with the formulas in [Co, Appendix II, pp. 72-75].$^{17}$

B.4.4. Idelic Explicit Formulas. Let $F$ be a number field. We conclude this section by rephrasing the Explicit Formulas as an identity between continuous linear functionals on $\mathcal{D}(C_F) = C_c^\infty(C_F)$.

*B.4.4.1. Weil's Principal Values from the Explicit Formulas via additive local Fourier transform.*

DEFINITION B.4.4.1 (Connes-Weil Principal Values). Let $F$ be a number field. For every place $v$ of $F$, we define, relative to the standard additive character $\alpha_{v,0}$ of $F_v$:$^{18}$

(1) The continuous$^{19}$ functional on $\mathcal{S}(F_v)$ assigned by:$^{20}$

$$
\tag{B.4.4.1} \mathrm{C}_{\alpha_{v,0}}\int_{F_v^\times} f(g)\,\mathrm{d}\mu_v(g) := \begin{cases} -\langle\widehat{J_v},f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'}, & v\mid\infty, \\ -\mu_v(\mathcal{O}_{F_v}^\times)\langle\widehat{J_v},f\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'}, & v\nmid\infty \end{cases}
$$

for all $f \in \mathcal{S}(F_v)$, where the notation $\langle\widehat{J_v},\cdot\rangle_{\mathcal{S}(F_v),\mathcal{S}(F_v)'}$ means $\int_{F_v} J_v\widehat{f}\,\mathrm{d}\nu_v$ by definition, where $\nu_v$ is the self-dual measure on $F_v$ with respect to $\alpha_{v,0}$ and the Fourier transform $\widehat{f}$ also rests on $\nu_v$.$^{21}$ We refer to $\mathrm{C}_{\alpha_{v,0}}\int_{F_v^\times}(\cdot)\,\mathrm{d}\mu_v$ as Connes' Principal Value relative to $\alpha_{v,0}$, for $\int_{F_v^\times}(\cdot)\,\mathrm{d}\mu_v$.

$^{16}$Brian needs to recheck the proof, both for factors of 2 and $2\pi$ in the integrals and for the coefficient of $f(0)$ in both parts

$^{17}$For part (1), should we tell the reader that Weil defines the right side to be the meaning of $\int_{F_v^\times} f(g)|g|_v^{1/2}/|1-g|_v\,\mathrm{d}\mu_v(g)$?

$^{18}$It would be much more convenient to give the definition directly here for $\mathrm{C}_\alpha$ for all non-trivial $\alpha \in \widehat{F}_v$, not just for $\alpha = \alpha_{v,0}$. We should also then comment that the definition below using $\alpha$ is unaffected by pre-composing $\alpha$ with multiplication by $\{|x| = 1\}$!

$^{19}$Continuity of right side in $f$ must be proved as a separate lemma before this definition, treating $v\mid\infty$ and $v\nmid\infty$ separately

$^{20}$In a clear way, should emphasize that the notation $\mu_v$ on the left side is just notation, and that the choice of $\alpha$ is baked into the right side.

$^{21}$This should go similarly for all $\alpha \in \widehat{F}_v-\{1\}$ and the associated self-dual measure $\nu$.

## PDF page 620

**620** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

(2) The continuous$^{22}$ functional on $\mathcal{D}(F_v^\times) = C_c^\infty(F_v^\times)$:

$$
\tag{B.4.4.2} \int_{F_v^\times,\alpha_{v,0}}' \frac{f(x)|x|_v^{1/2}}{|1-x|_v}\,\mathrm{d}\mu_v(x) := \mathrm{C}_{\alpha_{v,0}}\int_{F_v^\times} f(1+x)|1+x|_v^{-1/2}\,\mathrm{d}\mu_v(g)
$$

for all $f \in \mathcal{D}(F_v^\times)$. We refer to (B.4.4.2) as the Connes-Weil Principal Value relative to $\alpha_{v,0}$, for $\int_{F_v^\times}(\cdot)\frac{|x|_v^{1/2}}{|1-x|_v}\,\mathrm{d}\mu_v(x)$. This notation is “justified” by (B.4.4.5) below.

REMARK B.4.4.2 (On normalizations for the Haar measure on $F_v^\times$). Let $F$ be a number field. We note that the local multiplicative Tamagawa measure $\mu_v$ chosen on $F_v^\times$ for $v$ a non-Archimedean place of $F$ is not the canonical measure defined in Definition D.2.1.1 on any modulated group. The absolute value $|\cdot|_v$ promotes $F_v^\times$ to a $q_v^{\mathbf{Z}}$-modulated group, and the canonical measure $\mu_{\mathrm{can}}$ is related to $\mu_v$ by the following formula:

$$
\tag{B.4.4.3} \mu_{\mathrm{can}} = \frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\mu_v.
$$

Indeed, this choice of Haar measure gives the subset:

$$
A_T := \{x \in F_v^\times : |x|_v \in [1,T)\} \subset F_v^\times
$$

for $T > 1$ any real number, volume:

$$
\frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\mu_v(A_T) = \frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\sum_{0\le m<\log_{q_v}(T)} \mu_v(\pi_v^{-m}\mathcal{O}_{F_v}^\times) = \log(T) + O(1)
$$

which is the defining requirement of the canonical measure on the modulated group $F_v^\times$ (see (D.2.1.4) from Definition D.2.1.1).

When $v$ is Archimedean, the local multiplicative Tamagawa measure $\mu_v$ is not the canonical measure either.$^{23}$ The canonical measure $\mu_{\mathrm{can}}$ on $F_v^\times$ for $v$ Archimedean is related to $\mu_v$ by the formula:

$$
\tag{B.4.4.4} \mu_{\mathrm{can}} = \frac{1}{M_v}\mu_v
$$

where $M_v$ is the volume of the local unit group, just as for the case $v$ is non-Archimedean: $M_v = 2$ if $v$ is real, and $M_v = 2\pi$ if $v$ is complex.

The following is the main calculation of this section:

LEMMA B.4.4.3 (Weil's Principal Values at the non-Archimedean places). *Let $F$ be a number field, $v$ a non-Archimedean place of $F$. Let $\mathfrak{p}_v \subset \mathcal{O}_F$ be the unique prime ideal corresponding to the finite place $v$.*

*For any $f \in C_c^\infty(F_v^\times)$ such that $f(1) = 0$, we have*

$$
\tag{B.4.4.5} \int_{F_v^\times,\alpha_{v,0}}' \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) = \int_{F_v^\times} \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g)
$$

*and for $T \in C_c^\infty(F_v^\times)' = \mathcal{D}(F_v^\times)'$ unique such that $\widehat{T}(1_{\mathcal{O}_{F_v}^\times}) = 0$ and its restriction to $\ker(\delta_1) \subset C_c^\infty(F_v^\times)$ is the functional*

$$
\frac{N(\mathfrak{p}_v)}{N(\mathfrak{p}_v)-1}\frac{\nu_v}{|1-x|_v},
$$

*we have*

$$
\tag{B.4.4.6} \int_{F_v^\times,\alpha_{v,0}}' \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) = -\mu_v(\mathcal{O}_{F_v}^\times)\langle T,f(x)|x|_v^{-1/2}\rangle_{\mathcal{D}(F_v^\times),\mathcal{D}(F_v^\times)'}
$$

*for all $f \in \mathcal{D}(F_v^\times) = C_c^\infty(F_v^\times)$ with $f(1) = 0$.*

$^{22}$Continuity of right side in $f$ must be proved as a separate lemma before this definition, treating $v\mid\infty$ and $v\nmid\infty$ separately

$^{23}$Should we refer in some way to the cautionary comment at the end of §B.4.3?

## PDF page 621

**B.4. EXPLICIT FORMULAS FOR HECKE L-FUNCTIONS** · **621**

Proof. By Lemma A.3.2.3, we have:

$$
\mu_v = \frac{N(\mathfrak{p}_v)}{N(\mathfrak{p}_v)-1}\frac{\nu_v}{|\cdot|_v}
$$

where $\mathfrak{p}_v$ is the unique prime ideal of $\mathcal{O}_F$ corresponding to the finite place $v$.

Assume first $f(1) = 0$. Then, upon defining

$$
\tag{B.4.4.7} u(x) := \frac{f(1+x)}{|1+x|_v^{1/2}}
$$

(which vanishes near $x = -1$ since $f$ vanishes near $0$), we have $u(0) = 0$ and $u \in C_c^\infty(F_v^\times)$. Thus, by (B.4.3.5) from Proposition B.4.3.1 and (B.4.4.1) we have that (B.4.4.2) is equal to

$$
\mathrm{C}_{\alpha_{v,0}}\int_{F_v^\times} u(x)\,\mathrm{d}\mu_v(x) = \int_{F_v^\times} \frac{f(1+x)}{|1+x|_v^{1/2}}\,\mathrm{d}\mu_v(x) \tag{B.4.4.8}
$$

$$
= \frac{N(\mathfrak{p}_v)}{N(\mathfrak{p}_v)-1}\int_{F_v} \frac{f(1+x)}{|1+x|_v^{1/2}}\frac{\mathrm{d}\nu_v(x)}{|x|_v} = \frac{N(\mathfrak{p}_v)}{N(\mathfrak{p}_v)-1}\int_{F_v} \frac{f(1+y-1)}{|1+y-1|_v^{1/2}}\frac{\mathrm{d}\nu_v(y-1)}{|y-1|_v} = \frac{N(\mathfrak{p}_v)}{N(\mathfrak{p}_v)-1}\int_{F_v} \frac{f(y)|y|_v}{|y-1|_v|y|_v^{1/2}}\frac{\mathrm{d}\nu_v(y)}{|y|_v} = \int_{F_v^\times} \frac{f(x)|x|_v^{1/2}}{|1-x|_v}\,\mathrm{d}\mu_v(x),
$$

We deduce that (B.4.4.5) holds on the hyperplane $\ker(\delta_1) \subset C_c^\infty(F_v^\times)$.

We have:

$$
\langle\widehat{J_v},f(1+x)|1+x|_v^{-1/2}\rangle_{\mathcal{D}(F_v^\times),\mathcal{D}(F_v^\times)'} = \langle J_v,\int_{F_v} f(1+y)|1+y|_v^{-1/2}\overline{\alpha_{v,0}(xy)}\,\mathrm{d}\nu_v(y)\rangle_{\mathcal{D}(F_v^\times),\mathcal{D}(F_v^\times)'} \tag{B.4.4.9}
$$

$$
= \langle J_v,\alpha_{v,0}(x)\int_{F_v} f(z)|z|_v^{-1/2}\overline{\alpha_{v,0}(xz)}\,\mathrm{d}\nu_v(z)\rangle_{\mathcal{D}(F_v^\times),\mathcal{D}(F_v^\times)'} = \langle\widehat{\alpha_{v,0}\cdot J_v},f(x)|x|_v^{-1/2}\rangle_{\mathcal{D}(F_v^\times),\mathcal{D}(F_v^\times)'}
$$

which, combined with (B.4.4.5), shows that $T := \widehat{\alpha_{v,0}\cdot J_v}$ is the unique element in $\mathcal{D}(F_v^\times)'$ that restricts on $\ker(\delta_1) \subset \mathcal{D}(F_v^\times)$ to the functional:

$$
\frac{N(\mathfrak{p}_v)}{N(\mathfrak{p}_v)-1}\frac{\nu_v}{|1-x|_v}
$$

and satisfies $\widehat{T}(1_{\mathcal{O}_{F_v}^\times}) = 0$:

$$
\langle\widehat{T},1_{\mathcal{O}_{F_v}^\times}\rangle = \langle T,\widehat{1_{\mathcal{O}_{F_v}^\times}}\rangle = \langle\widehat{\alpha_{v,0}J_v},\widehat{1_{\mathcal{O}_{F_v}^\times}}\rangle = \langle\alpha_{v,0}J_v,1_{\mathcal{O}_{F_v}^\times}\rangle = \int_{\mathcal{O}_{F_v}^\times} \alpha_{v,0}J_v\,\mathrm{d}\mu_v = 0
$$

because $J_v|_{\mathcal{O}_{F_v}^\times} = 0$. $\square$

B.4.4.2. *Change of local additive character.* Upon replacing $\alpha_{v,0}$ with a different additive character of the local field $F_v$, the following Lemma explains how the Connes-Weil Principal Value changes. We refer the reader to the calculation in [Co, Lemma 3, p.76].

LEMMA B.4.4.4 (Change of additive character Lemma). *Let $F$ be a number field, $v$ a fixed finite place of $F$. We write $q_v$ for the size of the residue field at $v$. Let $\alpha_{v,0}$ be the standard additive character of the local*

## PDF page 622

**622** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

*field $F_v$ and let $\alpha \in \widehat{F_v}$ be an arbitrary non-trivial additive character, so there exists a unique $x_v \in F_v^\times$ such that $\alpha(x) = \alpha_{v,0}(x_v x)$.*

*We have:*

*(1) for any $f \in \mathcal{S}(F_v)$:*

$$
\tag{B.4.4.10} \mathrm{C}_\alpha\int_{F_v^\times} f(g)\,\mathrm{d}\mu_v(g) = f(0)\,\mu_v(\mathcal{O}_{F_v}^\times)\frac{\log|x_v|_v}{\log(q_v)} + \mathrm{C}_{\alpha_{v,0}}\int_{F_v^\times} f(g)\,\mathrm{d}\mu_v(g)
$$

*(2) for any $f \in \mathcal{D}(F_v^\times)$:*

$$
\tag{B.4.4.11} \int_{F_v^\times,\alpha}' \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) = f(1)\,\mu_v(\mathcal{O}_{F_v}^\times)\frac{\log|x_v|_v}{\log(q_v)} + \int_{F_v^\times,\alpha_{v,0}}' \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g)
$$

PROOF. (1) : The Lemma follows from (B.4.3.4) from Proposition B.4.3.1, as we now explain. The measure $|x_v|_v^{1/2}\nu_v$ is self-dual relative to the choice of character $\alpha$ (by Plancherel's Theorem), using [**CF**, Ch. XV, Ch. 4, §4.1, Thm. 4.1.2]. Thus,

(B.4.4.12)

$$
\mathrm{C}_\alpha\int_{F_v^\times} f(g)\,\mathrm{d}\mu_v(g) = \mu_v(\mathcal{O}_{F_v}^\times)\int_{F_v} \left\{\frac{-\log|y|_v}{\log(q_v)}\int_{F_v} f(u)\overline{\alpha}(uy)\,(|x_v|_v^{1/2}\,\mathrm{d}\nu_v(u))\right\}(|x_v|_v^{1/2}\,\mathrm{d}\nu_v(y))
$$

$$
= \mu_v(\mathcal{O}_{F_v}^\times)\int_{F_v} \left\{\frac{-\log|y|_v}{\log(q_v)}\int_{F_v} f(u)\overline{\alpha_{v,0}}(x_v uy)\,(|x_v|_v^{1/2}\,\mathrm{d}\nu_v(u))\right\}(|x_v|_v^{1/2}\,\mathrm{d}\nu_v(y))
$$

$$
= \mu_v(\mathcal{O}_{F_v}^\times)\int_{F_v} \left\{\frac{-\log|y|_v}{\log(q_v)}|x_v|_v\int_{F_v} f(u)\overline{\alpha_{v,0}}(x_v uy)\,\mathrm{d}\nu_v(u)\right\}\mathrm{d}\nu_v(y)
$$

$$
= -\mu_v(\mathcal{O}_{F_v}^\times)\langle J_v(y),|x_v|_v\widehat{f}(x_v y)\rangle_{\mathcal{S}(F_v)',\mathcal{S}(F_v)}.
$$

Now use (B.4.3.4) with $g = x_v^{-1}$ and (B.4.4.1) to see this equals recalling that $\rho_v$ denotes the left-translation action of $F_v^\times$ on $F_v$, which by (B.4.3.4) equals:

$$
\tag{B.4.4.13} \mathrm{C}_{\alpha_{v,0}}\int_{F_v^\times} f(g)\,\mathrm{d}\mu_v(g) + f(0)\,\mu_v(\mathcal{O}_{F_v}^\times)\frac{\log|x_v|_v}{\log(q_v)}.
$$

(2) : We have:

$$
\int_{F_v^\times,\alpha}' \frac{f(x)|x|_v^{1/2}}{|1-x|_v}\,\mathrm{d}\mu_v(x) := \mathrm{C}_\alpha\int_{F_v^\times} f(1+x)|1+x|_v^{-1/2}\,\mathrm{d}\mu_v(g)
$$

and so (B.4.4.11) follows from (B.4.4.10). $\square$

B.4.4.3. *Calculation of Weil's Principal Values.*

LEMMA B.4.4.5 (Weil's Principal Values at the non-Archimedean places). *Let $F$ be a number field, $v$ a non-Archimedean place of $F$, $q_v$ the size of the residue field at $v$, and $p$ the residue characteristic of $F_v$.*

*For any $f \in \mathcal{D}(F_v^\times) = C_c^\infty(F_v^\times)$ we have*

$$
\tag{B.4.4.14} \frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{F_v^\times,\alpha_{v,0}}' \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) = \mathrm{PF}_0\int_{F_v^\times} \frac{f(x)|x|_v^{1/2}}{|1-x|_v}\,\mathrm{d}\mu_{\mathrm{can},v}(x) - \log|\mathfrak{d}_{F_v/\mathbf{Q}_p}^{-1}|_v f(1),
$$

*where the principal value $\mathrm{PF}_0\int_{F_v^\times} \frac{f(x)|x|_v^{1/2}}{|1-x|_v}\,\mathrm{d}\mu_{\mathrm{can},v}(x)$ (for the canonical measure $\mu_{\mathrm{can},v}$ on the modulated group $(F_v^\times,|\cdot|_v)$) is defined as in [Weil-e, §15] to be*

$$
\frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{F_v^\times-\mathcal{O}_{F_v}^\times} \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) + \frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{\mathcal{O}_{F_v}^\times} \frac{(f(g)-f(1))|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g).
$$

## PDF page 623

**B.4. EXPLICIT FORMULAS FOR HECKE L-FUNCTIONS** · **623**

REMARK B.4.4.6. Note that $f(g)-f(1)$ vanishes in any small enough open neighborhood of $1 \in F_v^\times$. The integrand in the second integral used for defining Weil's principal value therefore makes sense. For $f = 1_{\mathcal{O}_{F_v}^\times}$, this lemma is also addressed in [Co, Lemma 2, p. 72] with different normalizations for the Haar measures.

PROOF. Assume first that $f$ vanishes at $g = 1$. Then (B.4.4.14) holds by (B.4.4.5) and (B.4.4.11). Since (B.4.4.14) is stable under replacement of $f$ with $f-1_{\mathcal{O}_{F_v}^\times}\cdot f(1)$, to treat the general case it remains to check both sides for $f = 1_{\mathcal{O}_{F_v}^\times}$.

Let $d = \mathrm{ord}_v(\mathfrak{d}_{F_v/\mathbf{Q}_p}) \ge 0$.

By design of $\mathfrak{d}_{F_v/\mathbf{Q}_p}$, the additive character $\alpha(x) = \alpha_{v,0}(\pi_v^{-d}x)$ (for a uniformizer $\pi_v$ at $v$) is trivial on $\mathcal{O}_{F_v}$ and non-trivial on $\mathfrak{m}_v^{-1}$, and the self-dual measure relative to it is $q_v^{d/2}\nu_v = N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{1/2}\nu_v$. By Lemma B.4.4.4(2), we have

$$
\tag{B.4.4.15} \frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{F_v^\times,\alpha}' \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) = f(1)\log|\mathfrak{d}_{F_v/\mathbf{Q}_p}^{-1}|_v + \frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{F_v^\times,\alpha_{v,0}}' \frac{f(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g).
$$

Since $\frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\mu_v = \mu_{\mathrm{can},v}$ as per Remark B.4.4.2, the calculation of $\frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{F_v^\times,\alpha_{v,0}}' \frac{f(x)|x|_v^{1/2}}{|1-x|_v}\,\mathrm{d}\mu_v(x)$ for $f = 1_{\mathcal{O}_{F_v}^\times}$ can be done directly from the definitions, using that $\alpha_{v,0}$ has self-dual measure $\nu_v = N(\mathfrak{d}_{F_v/\mathbf{Q}_p})^{-1/2}\mu$ for the Haar measure $\mu$ on $F_v$ giving $\mathcal{O}_{F_v}$ volume 1. The key calculation$^{24}$ is

$$
\int_{F_v} \frac{1_{\mathcal{O}_{F_v}^\times}(1+y)}{\sqrt{|1+y|_v}}\alpha_{v,0}(xy)\,\mathrm{d}\mu(y) = \alpha_{v,0}(-x)\left(1_{\mathfrak{d}_{F_v/\mathbf{Q}_p}^{-1}}(x) - \frac{1}{q_v}1_{\mathfrak{m}_v^{-1}\mathfrak{d}_{F_v/\mathbf{Q}_p}}(x)\right)
$$

and shows that (B.4.4.14) holds in this case too. $\square$

B.4.4.4. *Reformulation of Weil's Explicit Formulas.* We can now rewrite Weil's Explicit Formulas as an identity of distributions on the idele class group; i.e., as elements of $\mathcal{D}(C_F)'$.

THEOREM B.4.4.7 (Idelic Explicit Formulas). *Let $F$ be a number field. For every $\varphi \in \mathcal{D}(C_F)$, the sums on each side of the identity:*

(B.4.4.16)

$$
\sum_{c\in\Omega(C_F):L(c)=0} \frac{1}{\overline{\mu}_1(C_F^1)}\int_{C_F} \varphi(g)c(g)|g|_F^{-1/2}\,\mathrm{d}\overline{\mu}(g) = \frac{1}{\overline{\mu}_1(C_F^1)}\int_{C_F} \varphi(g)|g|_F^{-1/2}\,\mathrm{d}\overline{\mu}(g) + \frac{1}{\overline{\mu}_1(C_F^1)}\int_{C_F} \varphi(g)|g|_F^{1/2}\,\mathrm{d}\overline{\mu}(g)
$$

$$
- \sum_{v\in S_{F,\infty}} \frac{1}{M_v}\int_{F_v^\times,\alpha_{v,0}}' \frac{\varphi(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g)
$$

$$
- \sum_{v\in S_{F,f}} \frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{F_v^\times,\alpha_{v,0}}' \frac{\varphi(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g)
$$

*(where $M_v = 2$ if $v$ is real, and $M_v = 2\pi$ if $v$ is complex) absolutely converge for every $\varphi \in \mathcal{D}(C_F)$ and converge in $\mathcal{D}(C_F)'_\beta$ defining the same continuous functional on $\mathcal{D}(C_F)$.*

The topology on $\mathcal{D}(C_F)$ is the countable strict locally convex inductive limit $\varinjlim \mathcal{D}(C_F/K)$ where $K$ varies through a decreasing countable cofinal system of compact subgroups of $C_F$ for which $C_F/K$ is a Lie group with finitely generated component group (see [Bru, pp. 44-45]). For the proof of Theorem B.4.4.7 we shall use the following (see Definition D.2.1.1 and the subsequent discussion after that for the concept and main results on modulated Hausdorff locally compact abelian groups):

$^{24}$the right side should be double-checked

## PDF page 624

**624** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

LEMMA B.4.4.8. *Let $G$ be an $\mathbf{R}_{>0}$-modulated group abelian Lie group (possibly disconnected). Let $\mu_G$ be a choice of Haar measure on $G$. Let $\mathcal{Z} \subset \Omega(G)$ be a subset whose intersection with every connected component of $\Omega(G)$ is discrete and contained within a single vertical strip of bounded width of the connected component.$^{25}$ For any $\varphi \in \mathcal{D}(G)$, the sum*

$$
\tag{B.4.4.17} \sum_{c\in \mathcal{Z}} \int_G \varphi(g)c(g)\,\mathrm{d}\mu_G(g)
$$

*is absolutely convergent.*

Proof. We choose the Haar measure $\mu_1$ on $G^1$ compatible with the given $\mu_G$ on $G$ and the measure $\mathrm{d}t/t$ on $\mathbf{R}_{>0}$ via the exact sequence of topological groups $1 \to G^1 \to G \xrightarrow{|\cdot|_G} \mathbf{R}_{>0} \to 1$. For a choice of continuous homomorphic section $\tau$ to $|\cdot|_G$, (B.4.4.17) can be rewritten termwise as

$$
\tag{B.4.4.18} \sum_{c\in \mathcal{Z}} \int_{\mathbf{R}_{>0}} t^s c(\tau(t))\int_{G^1} \varphi(g\tau(t))\chi_1(g)\,\mathrm{d}\mu_1(g)\,\frac{\mathrm{d}t}{t}
$$

where $\chi_1 := c|_{G^1}$.

Since $G^1$ is a (possibly disconnected) compact abelian Lie group, up to splitting the sum into finitely many sub-sums and adjusting $\varphi$ accordingly, we may focus on integrating over $(G^1)^0 = \mathbf{T}^N$ for an integer $N \ge 0$. We therefore have for all $z = (z_k)_{1\le k\le N} \in \mathbf{T}^N$ that $\chi_1(z) = \prod_{1\le k\le N} z_k^{a_k}$ for some $(a_k)_{1\le k\le N} \in \mathbf{Z}^N$.

As a function of $(s,(a_k)_{1\le k\le N}) \in \mathbf{C}\times\mathbf{Z}^N$, the term for $c$ in (B.4.4.18) is, up to a positive multiplicative constant (depending on $\mu_1((G^1)^0)$),

$$
\Phi(s,(a_k)_{1\le k\le N}) = \int_{\mathbf{R}_{>0}} t^s c(\tau(t))\int_{\mathbf{T}^N} \varphi(z\tau(t))\prod_{1\le k\le N} z_k^{a_k}\,\mathrm{d}\mu_N(z)\,\frac{\mathrm{d}t}{t}
$$

where $\mu_N$ is the volume-1 Haar measure on $\mathbf{T}^N$. This decays rapidly on the vertical strips $\mathbf{C}_I$ of bounded width of the Riemann surface $\mathbf{C}\times\mathbf{Z}^N$: for every real number $T > 0$ and integer $M \ge 0$, there exists a real number $C_{T,M} > 0$ independent of $c$ such that:

$$
\sup_{(s,(a_k)_{1\le k\le N})\in \mathbf{C}_I\times\mathbf{Z}:|\mathrm{Im}(s)|>T,||(a_k)_{1\le k\le N}||_\infty>T} |\Phi(s,(a_k))| < C_{T,M}\,T^{-3M}.
$$

This rapid decay condition is a consequence of the Uniform Riemann-Lebesgue Lemma (Theorem D.3.4.2 with $D = (t\partial_t)^M(\sum_{1\le k\le N}(z_k\partial_{z_k})^2)^M$), and thereby implies the absolute convergence of the sum in (B.4.4.17).$^{26}$ $\square$

LEMMA B.4.4.9 (Convergence of sums of Mellin transforms). *Let $F$ be a number field, $\varphi \in \mathcal{D}(C_F)$.*

*Then for any subset $\mathcal{Z}$ of the set:*

$$
\{c \in \Omega(C_F) : L(c) = 0\} \subset \Omega(C_F)
$$

*where $L(c)$ is the Hecke $L$-function of $F$, and for any real number $a \in \mathbf{R}$, the sum:*

$$
\tag{B.4.4.19} \sum_{c\in \mathcal{Z}} \int_{C_F} \varphi(g)c(g)|g|_F^a\,\mathrm{d}\mu(g)
$$

*converges absolutely.*

Proof. Multiplication by $|\cdot|_F^a$ is a linear topological automorphism on $\mathcal{D}(C_F)$, and so we may and do assume $a = 0$.

$^{25}$Need some hypothesis on $\mathcal{Z}$ preventing “too many” $c \in \mathcal{Z}$ near a given large height.

$^{26}$Must explain clearly how we are bringing in that $\mathcal{Z}$ doesn't accumulate too much at a given height.

## PDF page 625

**B.4. EXPLICIT FORMULAS FOR HECKE L-FUNCTIONS** · **625**

We let $k \subset C_F^1$ be a compact subgroup with open compactly generated orthogonal such that $\varphi$ is $k$-invariant. The contribution from $c$ that are not $k$-invariant vanishes since

$$
\int_{C_F} \varphi(g)c(g)\,\mathrm{d}\mu(g) = \int_{C_F/k} \varphi(\bar{g})\left(\int_k c(k)\,\mathrm{d}k\right)\mathrm{d}\bar{\mu}(g),
$$

so we may replace $C_F$ with $G := C_F/k$, an abelian Lie group, and $\mu$ with the unique Haar measure $\mu_G$ on $C_F/k$ prescribed by $\mu$ and the volume-1 Haar measure on $k$ as per Theorem D.1.2.1, in (B.4.4.19). The result then follows from Lemma B.4.4.8. $\square$

PROOF OF THEOREM B.4.4.7. By Proposition B.4.3.2 and Lemma B.4.4.5, for each place $v$ of $F$ and $\varphi_v \in \mathcal{D}(F_v^\times)$ we have

$$
\tag{B.4.4.20} \int_{F_v^\times,\alpha_{v,0}}' \frac{\varphi_v(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) = \mathrm{PF}_0\int_{F_v^\times} \frac{\varphi_v(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g)
$$

for Archimedean places $v$ (where the principal value on the right side is defined to be the right sides of (B.4.3.13) and (B.4.3.14), depending on whether $v$ is real or complex) and

$$
\tag{B.4.4.21} \frac{\log(q_v)}{\mu_v(\mathcal{O}_{F_v}^\times)}\int_{F_v^\times,\alpha_{v,0}}' \frac{\varphi_v(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) = \mathrm{PF}_0\int_{F_v^\times} \frac{\varphi_v(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_{\mathrm{can},v}(g) - \log|\mathfrak{d}_{F_v/\mathbf{Q}_p}^{-1}|_v\varphi_v(1)
$$

for non-Archimedean $v$.

For each place $v$ of $F$, define the test function $\varphi_v \in \mathcal{D}(F_v^\times)$ to be the composition of $\varphi \in \mathcal{D}(C_F)$ with the closed homomorphism $F_v^\times \subset C_F$. The right side of (B.4.4.16) agrees with the sum on the right side of the identity$^{27}$

$$
\Delta(\varphi) = \varphi(1)\log|\mathfrak{d}_{F/\mathbf{Q}}^{-1}|_F + D(\varphi) - \sum_{v\in\Sigma_F} D_v(\varphi_v)
$$

displayed at the end of [Weil-e, §16], where

$$
D_v(\varphi_v) := \mathrm{PF}_0\int_{F_v^\times} \frac{\varphi_v(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_{\mathrm{can},v}(g)
$$

(with $\mu_{\mathrm{can},v}$ the canonical measure on the modulated group $F_v^\times$ as in Definition D.2.1.1: $\mathrm{d}t/t$ for real $v$, $|\mathrm{d}z\wedge \mathrm{d}\bar{z}|/(2\pi z\bar{z})$ for complex $v$, and $(\log(q_v)/\mu_v(\mathcal{O}_{F_v}^\times))\mu_v$ for any Haar measure $\mu_v$ on $F_v^\times$ for finite $v$),

$$
D(\varphi) := \int_{C_F} \varphi(g)|g|_F^{-1/2}\,\mathrm{d}\bar{\mu}(g) + \int_{C_F} \varphi(g)|g|_F^{1/2}\,\mathrm{d}\bar{\mu}(g),
$$

and $\Delta(\varphi)$ defined to be the sum on the left side of (B.4.4.16) (absolutely convergent by Lemma B.4.4.9).

We note that for each $\varphi \in \mathcal{D}(C_F)$, the sum in the right side of (B.4.4.16) has all but finitely many terms vanishing: to see this, for any non-Archimedean place $v$ of $F$ we compute

$$
\tag{B.4.4.22} \mathrm{PF}_0\int_{F_v^\times} \frac{\varphi_v(g)|g|_v^{1/2}}{|1-g|_v}\,\mathrm{d}\mu_v(g) = \mathrm{PF}_0\sum_{m\in\mathbf{Z}}\int_{\mathcal{O}_{F_v}^\times} \frac{\varphi_v(g\pi_v^m)|g\pi_v^m|_v^{1/2}}{|1-g\pi_v^m|_v}\,\mathrm{d}\mu_{v,0}(g)
$$

as is shown by deducing the case $\varphi_v(1) = 0$ from Theorem D.1.2.1 and then verifying the case $\varphi_v = 1_{\mathcal{O}_{F_v}^\times}$ (for which case both sides vanish). For all $v$ non-Archimedean with large enough residue characteristic (depending on the support of $\varphi \in \mathcal{D}(C_F)$), $\varphi_v(\pi_v^m g) = 0$ for all $g \in \mathcal{O}_{F_v}^\times$ and all $m \neq 0$, and so the right side of (B.4.4.22) vanishes.

To verify that both sides of (B.4.4.16) as linear functionals on $\mathcal{D}(C_F)$ are continuous and as an infinite sum of functionals is convergent in $\mathcal{D}(C_F)'_\beta$, we can use the argument from Remark B.4.1.6 with $\mathcal{S}(\mathbf{R})$ replaced by $\mathcal{D}(C_F)$ provided that each term in the sums on both sides is continuous on $\mathcal{D}(C_F)$ and that $\mathcal{D}(C_F)$ is

$^{27}$Must explain to the reader how to obtain this identity from Theorem B.4.2.2.

## PDF page 626

**626** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

complete and barreled with its closed bounded subsets all compact. The continuity of the local terms on the right side is immediate from combining the continuity of each restriction map $\mathcal{D}(C_F)\to\mathcal{D}(F_v)$ (which follows from $F_v^\times\to C_F$ being a closed embedding and hence proper [Bru, p. 58]) and continuity in Definition B.4.4.1; the continuity of the global terms on both sides is seen by passage to the locally convex inductive limit from the straightforward case of $\varphi$ with a fixed compact support.

Since $\mathcal{D}(C_F)$ is a strict countable locally convex inductive limit of Fréchet spaces [Bru, p. 46], completeness and barreledness of $\mathcal{D}(C_F)$ are inherited from the Fréchet space via passage to the inductive limit [Scha, Ch. II, 6.6, Cor. 1 to 7.2]. The compactness of closed bounded subsets in $\mathcal{D}(C_F)$ is part of [Bru, §4, Cor. 2 to Thm. 2].

$\square$

**B.5. Recurrence and equidistribution**

In this section we record a proof of a uniform version of the Kronecker-Weyl Theorem, and prove, as an application required in Chapter ?? of this work, the strong recurrence on vertical strips of the reciprocal Euler factors of Hecke $L$-functions. We will be discussing the concept of recurrence for holomorphic functions on vertical strips, and basic permanence properties as the need arises.

**B.5.1. Preparations.** This section is devoted to reviewing the small amount of ergodic theory required, providing some complements with a view towards the intended applications. Most of the results herein are well-known or direct consequences of well-known mathematics, and can be found in the referred literature. We include the arguments here for completeness, ease of access, and to discuss minor variations needed for applicability.

We will not be requiring the general Ergodic Theorem of Birkhoff-Khinchin (see, for instance, [CFSS, Ch.1,§2,Thm.1]), nor theory and lexicon from ergodic theory. We will be very briefly pointing out to the reader how the results discussed below fit within terminology and principles of ergodic theory. Each will be an incarnation of the classical Kronecker-Weyl Theorem, expressing the unique ergodicity of certain linear flows on tori.

Main references for the results and respective preparations throughout this section are [HK, Part 1,Ch.4,§4.1,4.2] (focusing on the one and two-dimensional cases only), and the unpublished [Hu1, §4.3] and [Hu2, Appendix A], for proofs of the finite-dimensional continuous and discrete versions, respectively, of the classical Kronecker-Weyl Theorem.

We denote by

$$
\mathbf{T}:=\mathbf{R}/\mathbf{Z}
$$

the additive compact Hausdorff topological group of the unit circle. For any integer $N\ge 1$, we write $[N]$ for the ordered subset

$$
[N]:=\{1,\dots,N\}\subset\mathbf{Z}.
$$

DEFINITION B.5.1.1. We define

(1) The compact Hausdorff topological product group

$$
\mathbf{T}^N:=\prod_{1\le k\le N}\mathbf{T}. \tag{B.5.1.1}
$$

(2) For a subset $U\subset\mathbf{R}^N$ and a continuous 1-parameter subgroup $\gamma:\mathbf{R}\to\mathbf{R}^N$, we write

$$
\gamma(t)\in U\bmod 1 \tag{B.5.1.2}
$$

to mean that the image of $\gamma(t)$ in $\mathbf{T}^N$ under the quotient map $\theta$ is contained in the image of $U$, i.e. $\overline{\gamma}(t)\in\theta(U)$. Equivalently, $\gamma(t)\in U+\mathbf{Z}^N$. We write, for any interval $I\subset\mathbf{R}$

$$
I_U:=\{t\in I:\gamma(t)\in U\bmod 1\}\subset I. \tag{B.5.1.3}
$$

## PDF page 627

**B.5. RECURRENCE AND EQUIDISTRIBUTION** · **627**

We identify $\mathbf{T}$ with the unit circle within $\mathbf{C}^\times$ via the quotient topological group homomorphism

$$
\exp(2\pi i t):\mathbf{R}\to\mathbf{T}
$$

whose kernel is the discrete subgroup $\mathbf{Z}\subset\mathbf{R}$.

For any integer $N\ge 1$ and any vector $(\tau_1,\dots,\tau_N)$ in $\mathbf{R}^N$, we may consider the smooth map:

$$
\overline{\gamma}_N:\mathbf{R}\to\mathbf{T}^N
$$

defined as the composition of $\gamma_N(t):=t\cdot(\tau_1,\dots,\tau_N)\in\mathbf{R}^N$ followed by the projection $\theta_N:\mathbf{R}^N\to\mathbf{T}^N$.

When $\tau_1,\dots,\tau_N$ are $\mathbf{Q}$-linearly independent, $\overline{\gamma}_N$ is injective with dense image, as we will be recalling in Theorem B.5.2.1. In this case, $\overline{\gamma}_N$ is a one-parameter subgroup of the torus $\mathbf{T}^N$, and it induces a continuous flow on $\mathbf{T}^N$ by left-translation with dense image.

**B.5.2. Kronecker-Weyl.** The following Theorem is the multi-dimensional version of [HK, Part 1, Thm.4.1.15] and its method of proof is analogous to the argument [HK, Part 1, §4.1.6]. We will only be requiring the case when $(\tau_1,\dots,\tau_N)\in\mathbf{R}^N$ has $\mathbf{Q}$-independent coordinates. A full proof in the general case when the vector $(\tau_1,\dots,\tau_N)\in\mathbf{R}^N$ in the statement has not necessarily $\mathbf{Q}$-independent coordinates can be found in the appendix of [Hu1, §4.3, Proof of Lemma 4.3], and we will be following it closely to establish the case of continuous functions.

B.5.2.1. *The classical Kronecker-Weyl Theorem.* For any integer $N\ge 1$, we say a function $u:\mathbf{T}^N\to\mathbf{C}$ is Riemann-integrable if and only if the composition $u\circ\theta:[0,1)^N\to\mathbf{C}$ is a function whose real and imaginary parts are both Riemann-integrable on the half-open cube $[0,1)^N$ in the standard sense of Riemann-integrability on convex subsets within Euclidean spaces.

We denote by $\mu_N$ the volume-1 Haar measure on $\mathbf{T}^N$, and recall that $\mu_N$ agrees under $\theta_N$ with the measure induced by restriction to $[0,1)^N$ of the Lebesgue measure $\lambda_N$ on $\mathbf{R}^N$, i.e.

$$
\mu_N=(\theta_N)_*(\lambda_N|_{[0,1)^N})
$$

since $[0,1)^N$ is a fundamental domain for the continuous action by left-translations of the closed discrete subgroup $\mathbf{Z}^N\subset\mathbf{R}^N$.

THEOREM B.5.2.1 (Kronecker-Weyl). *Let $\tau:=(\tau_1,\dots,\tau_N)\in\mathbf{R}^N$ be a vector. Let $0\le d\le N$ be the dimension of the $\mathbf{Q}$-linear subspace generated within $\mathbf{R}$ by the coordinates of $\tau$.*

Then

(1) *$\tau$ generates a continuous 1-parameter group $\overline{\gamma}_\tau:\mathbf{R}\to\mathbf{T}^N$ whose image has closure a $d$-dimensional closed torus $G$ within $\mathbf{T}^N$.*

(2) *For every Riemann integrable function $u:G\to\mathbf{C}$, the following identity holds*

$$
\lim_{T\to+\infty}\frac{1}{2T}\int_{-T}^T u(\overline{\gamma}(t))\,\mathrm{d}t=\lim_{T\to+\infty}\frac{1}{T}\int_0^T u(\overline{\gamma}(t))\,\mathrm{d}t=\int_G u(\xi)\,\mathrm{d}\mu_G(\xi) \tag{B.5.2.1}
$$

*where $\mu_G$ is the volume-1 Haar measure on $G$.*

We will use the following:

LEMMA B.5.2.2. *Let $X$ be a compact Hausdorff space, $\mu$ a regular Borel measure on $X$, and $U\subset X$ an open subset such that $\mu(\partial U)=0$. For every $\varepsilon>0$, there exist continuous functions $u_1,u_2:X\to[0,1]$ such that:*

$$
u_1(x)\le\mathrm{1}_U(x)\le u_2(x) \tag{B.5.2.2}
$$

## PDF page 628

**628** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

for all $x\in X$, and:

$$
\int_X (u_2-u_1)(x)\,\mathrm{d}\mu(x)<\varepsilon. \tag{B.5.2.3}
$$

PROOF. We fix $\varepsilon>0$. Since $\mu$ is a finite regular Borel measure, by [Fol, Prop. 7.7(a)] there exists a closed subset $K_1\subset U$ such that $\mu(U-K_1)<\varepsilon/2$. By openness of $U$, $K_2:=X-U$ is closed. By Urysohn's Lemma ([Fol, Thm. 4.32], one of whose equivalent forms is that for any $K\subset U\subset X$ with $K$ closed and $U$ open, there exists a continuous compactly-supported function $f:X\to[0,1]$ such that $\mathrm{1}_K(x)\le f(x)\le\mathrm{1}_U(x)$ for all $x\in X$), there exists a continuous function $u_1:X\to[0,1]$ such that $K_1\subset u_1^{-1}(1)$ and $K_2\subset u_1^{-1}(0)$. In particular, we have $u_1(x)\le\mathrm{1}_U(x)$ for all $x\in X$.

We now let $\bar U\subset X$ be the closure of $U$. Since $\mu$ is regular, there exists an open subset $U'\subset X$ containing $\bar U$ and such that $\mu(U'-\bar U)<\varepsilon/2$. Calling $H_1:=\bar U$ and $H_2:=X-U'$, two disjoint closed subsets of $X$, by Urysohn's Lemma again there exists a continuous function $u_2:X\to[0,1]$ such that $H_1\subset u_2^{-1}(1)$ and $H_2\subset u_2^{-1}(0)$. In particular, we have

$$
\mathrm{1}_{K_1}(x)\le u_1(x)\le\mathrm{1}_U(x)\le\mathrm{1}_{\bar U}(x)\le u_2(x)\le\mathrm{1}_{U'}(x)
$$

for all $x\in X$. We now observe that we have

$$
\int_X (u_2-u_1)(x)\,\mathrm{d}\mu(x)\le\mu(U')-\mu(K_1)=\mu(U'-\bar U)+\mu(\partial U)+\mu(U)-\mu(K_1)<\varepsilon/2+\mu(\partial U)+\varepsilon/2=\varepsilon
$$

since we assumed $\mu(\partial U)=0$. This completes the proof of the Lemma.

$\square$

REMARK B.5.2.3. (1) Let $U\subset[0,1)^N$ be a subset such that $\partial U$ (in $[0,1)^N$) is a Lebesgue null-set. Then, upon denoting by $\widehat U$ the image of $U$ under $\theta_N$ in $\mathbf{T}^N$, we have $\mu_N(\partial\widehat U)=0$. To see this, we proceed as follows. Since $\theta_N:\mathbf{R}^N\to\mathbf{T}^N$ is a covering map, it is open. When restricted to $[0,1]^N$, it is also closed since $\mathbf{T}^N$ is compact and $[0,1]^N$ is Hausdorff. Upon calling $\bar U$ the closure of $U$ in $[0,1]^N$, the Lebesgue measure of the boundary of $U$ in $[0,1]^N$ is again zero, since $(\bar U-U)\cap[0,1)^N$ has measure zero by assumption, and $[0,1]^N-[0,1)^N$ is a null-set. Since we have $\theta_N(\bar U-U)=\partial\widehat U$, it follows that $\partial\widehat U$ is a $\mu_N$-null set.

(2) For any Jordan-measurable subset $\Delta\subset[0,1)^N$, we deduce that the image $\widehat\Delta$ in $\mathbf{T}^N$ has boundary of $\mu_N$-measure zero, and so its interior qualifies for the $U$ in Lemma B.5.2.2 and has the same $\mu_N$-measure as $\widehat\Delta$.

The proof recorded below follows closely the argument provided in [Hu1, §4.3, Proof of Lemma 4.3].

PROOF of Theorem B.5.2.1. (1): The case $N=1$ is easy, so assume $N>1$. We start off by discussing the special case in which the coordinates of $\tau$ are $\mathbf{Q}$-linearly independent.

In this case, $\overline{\gamma}$ is injective. Indeed, if $\gamma(t)=\gamma(t')$ for distinct $t,t'\in\mathbf{R}$ then

$$
(t-t')\cdot\tau\in\mathbf{Z}^N
$$

gives a $\mathbf{Q}$-linear dependence relation among the $N$ coordinates of $\tau$ since $N>1$, a contradiction. Thus, $\overline{\gamma}$ is injective.

We now call $G$ the closure of the image of $\overline{\gamma}$ in $\mathbf{T}^N$. This is a closed connected subgroup of $\mathbf{T}^N$ and as such it is contained in the kernel a non-trivial character $\chi:\mathbf{T}^N\to\mathbf{T}$ if the dimension of $G$ is less than $N$. But $\chi(z_1,\dots,z_N)=\prod z_j^{a_j}$ for some nonzero $a\in\mathbf{Z}^N$ (viewing $\mathbf{T}$ multiplicatively), so this would give a $\mathbf{Q}$-linear dependence relation on the coordinates of $\tau$, contradicting the assumption. We deduce that we have $G=\mathbf{T}^N$.

In the general case, let $G$ be the closure of the image of $\overline{\gamma}$. This is a closed connected subgroup of $\mathbf{T}^N$, and as such it is itself a torus. We call $r$ its dimension. Then $G^\perp\subset\widehat{\mathbf{T}^N}$ is a finitely generated free subgroup of rank $N-r$. Let $\chi\in G^\perp$.

## PDF page 629

**B.5. RECURRENCE AND EQUIDISTRIBUTION** · **629**

Then $\chi$ is of the form $\chi(z_1\cdots z_N)=\prod_{1\le k\le N}z_k^{a_k}$ for a unique vector $(a_k)_{1\le k\le N}\in\mathbf{Z}^N$, and the defining condition of $G^\perp$ is $1=\chi(e^{2\pi i\tau_1 t}\cdots e^{2\pi i\tau_N t})=e^{2\pi i t(\sum\tau_k a_k)}$ for all $t\in\mathbf{R}$, which reads $\sum_{1\le k\le N}\tau_k a_k=0$.

It follows that $G^\perp$ is contained within a $\mathbf{Q}$-linear subspace of $\mathbf{Q}^N$ of codimension $d$, and it equals the intersection of such a subspace with $\mathbf{Z}^N$. The rank of $G^\perp$ is therefore $N-d$, and $\widehat{\mathbf{T}^N}/G^\perp\simeq\widehat G$ by [DE, Prop. 3.6.1(c)] (see also Lemma D.1.4.6(3)), from which it follows that $G$ is a $d$-dimensional closed subtorus of $\mathbf{T}^N$.

(2): We first assume that the coordinates of $\tau$ are $\mathbf{Q}$-linearly independent, so $\overline{\gamma(\mathbf{R})}$ has closure $\mathbf{T}^N$ by (1). Assume that (B.5.2.1) holds for all continuous functions $u\in C(\mathbf{T}^N)$. Let $\Delta\subset[0,1)^N$ be any Jordan-measurable open subset (so $\mu(\partial\Delta)=0$) and denote by $\widehat\Delta$ its image in $\mathbf{T}^N$.

Since $\Delta$ is Jordan-measurable, its boundary is a null-set for the Lebesgue measure on $\mathbf{R}^N$, and hence $\mu_N(\partial\widehat\Delta)=0$. Since integration on $\mathbf{T}^N$ with respect to $\mu_N$ is insensitive to $\mu_N$-null-sets, by openness of $\theta$ (a continuous quotient homomorphism of topological groups) we may replace $\Delta$ by its interior, to the effect of replacing $\widehat\Delta$ by its interior.

By Lemma B.5.2.2, for every $\varepsilon>0$ there exist continuous functions $u_1,u_2\in C(\mathbf{T}^N)$ such that $u_1,u_2$ are real-valued, and

$$
u_1(\xi)\le\mathrm{1}_{\widehat\Delta}(\xi)\le u_2(\xi) \tag{B.5.2.4}
$$

for all $\xi\in\mathbf{T}^N$, $\mathrm{1}_{\widehat\Delta}$ being the indicator function of $\widehat\Delta\subset\mathbf{T}^N$, and such that

$$
\int_{\mathbf{T}^N}(u_2-u_1)(\xi)\,\mathrm{d}\mu_N(\xi)<\varepsilon. \tag{B.5.2.5}
$$

By (B.5.2.1) applied to the continuous function $u=u_2-u_1$, we also obtain

$$
\lim_{T\to+\infty}\frac{1}{2T}\int_{-T}^T (u_2-u_1)(\overline{\gamma}(t))\,\mathrm{d}t<\varepsilon \tag{B.5.2.6}
$$

and therefore

$$
\lim_{T\to+\infty}\frac{1}{2T}\int_{-T}^T u_2(\overline{\gamma}(t))\,\mathrm{d}t-\varepsilon<\lim_{T\to+\infty}\frac{1}{2T}\int_{-T}^T\mathrm{1}_{\widehat\Delta}(\overline{\gamma}(t))\,\mathrm{d}t<\lim_{T\to+\infty}\frac{1}{2T}\int_{-T}^T u_1(\overline{\gamma}(t))\,\mathrm{d}t+\varepsilon, \tag{B.5.2.7}
$$

and likewise

$$
\int_{\mathbf{T}^N}u_2(\xi)\,\mathrm{d}\mu(\xi)-\varepsilon<\int_{\mathbf{T}^N}\mathrm{1}_{\widehat\Delta}(\xi)\,\mathrm{d}\mu_N(\xi)<\int_{\mathbf{T}^N}u_1(\xi)\,\mathrm{d}\mu_N(\xi)+\varepsilon \tag{B.5.2.8}
$$

Upon letting $\varepsilon$ tend to zero, we deduce from the assumed continuous case (applied to $u_1$ and $u_2$) that (B.5.2.1) holds for the indicator function of $\widehat\Delta$, for any Jordan-measurable subset $\Delta\subset[0,1)^N$.

This case then propagates (B.5.2.1) to arbitrary Riemann sums, since each Riemann sum is an integral on $\mathbf{T}^N$ with respect to $\mu_N$, of a finite $\mathbf{C}$-linear combination of indicator functions of images in $\mathbf{T}^N$ of Jordan-measurable subsets in $[0,1)^N$.

We next deduce that (B.5.2.1) holds for all Riemann-integrable $\mathbf{R}$-valued functions $u$ on $\mathbf{T}^N$. For $\varepsilon>0$, we can pick a Riemann step function $\widetilde u$ on $\mathbf{T}^N$ so that $|\widetilde u-u|\le\varepsilon$ pointwise on $\mathbf{T}^N$. Thus,

$$
\left|\frac{1}{T}\int_0^T\widetilde u(\overline{\gamma}(t))\,\mathrm{d}t-\frac{1}{T}\int_0^T u(\overline{\gamma}(t))\,\mathrm{d}t\right|\le\frac{1}{T}\int_0^T|\widetilde u-u|\circ\overline{\gamma}(t)\,\mathrm{d}t\le\varepsilon,
$$

and similarly with $(1/(2T))\int_{-T}^T$ and $\int_{\mathbf{T}^N}\mathrm{d}\mu_N$. By the settled Riemann step-function case for $\widetilde u$, if $T$ is sufficiently large then

$$
\left|\int_{\mathbf{T}^N}\widetilde u\,\mathrm{d}\mu_N-\frac{1}{T}\int_0^T\widetilde u(\overline{\gamma}(t))\,\mathrm{d}t\right|\le\varepsilon,\quad\left|\int_{\mathbf{T}^N}\widetilde u\,\mathrm{d}\mu_N-\frac{1}{2T}\int_{-T}^T\widetilde u(\overline{\gamma}(t))\,\mathrm{d}t\right|\le\varepsilon.
$$

## PDF page 630

**630** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

Thus, we get analogous estimates for $3\varepsilon$ with $u$ in place of $\widetilde u$, so the desired conclusion holds for $u$. By $\mathbf{R}$-linearity, this conclusion holds for general $\mathbf{C}$-valued Riemann-integrable functions on $\mathbf{T}^N$ by analyzing real and imaginary parts separately.

We are thereby reduced to the case of continuous $u$ in (B.5.2.1) when the coordinates of $\tau$ are $\mathbf{Q}$-linearly independent. For a $\mathbf{C}$-sub-algebra $A\subset C(\mathbf{T}^N)$ dense with respect to the uniform-norm topology on $C(\mathbf{T}^N)$, with $A$ to be chosen, we now assume that (B.5.2.1) holds for all the elements of $A$ and deduce it for all continuous functions $u$ on $\mathbf{T}^N$. Pick $\varepsilon>0$ and $v\in A$ such that $|v-u|\le\varepsilon$ pointwise on $\mathbf{T}^N$. We then have $\left|\int_{\mathbf{T}^N}v\,\mathrm{d}\mu_N-\int_{\mathbf{T}^N}u\,\mathrm{d}\mu_N\right|\le\varepsilon$ and for all sufficiently large $T$ (depending on $\varepsilon$ and $v$) we have

$$
\left|\frac{1}{T}\int_0^T v(\overline{\gamma}(t))\,\mathrm{d}t-\int_{\mathbf{T}^N}v\,\mathrm{d}\mu_N\right|\le\varepsilon,\quad\left|\frac{1}{2T}\int_{-T}^T v(\overline{\gamma}(t))\,\mathrm{d}t-\int_{\mathbf{T}^N}v\,\mathrm{d}\mu_N\right|\le\varepsilon,
$$

so each of $(1/T)\int_0^T v(\overline{\gamma}(t))\,\mathrm{d}t$ and $(1/(2T))\int_{-T}^T v(\overline{\gamma}(t))\,\mathrm{d}t$ are within $2\varepsilon$ of $\int_{\mathbf{T}^N}u\,\mathrm{d}\mu_N$. But also

$$
\left|\frac{1}{T}\int_0^T v(\overline{\gamma}(t))\,\mathrm{d}t-\frac{1}{T}\int_0^T u(\overline{\gamma}(t))\,\mathrm{d}t\right|\le\frac{1}{T}\int_0^T|v-u|(\overline{\gamma}(t))\,\mathrm{d}t\le\varepsilon
$$

and likewise for $(1/(2T))\int_{-T}^T$, so both $(1/T)\int_0^T u(\overline{\gamma}(t))\,\mathrm{d}t$ and $(1/(2T))\int_{-T}^T u(\overline{\gamma}(t))\,\mathrm{d}t$ are within $3\varepsilon$ of $\int_{\mathbf{T}^N}u\,\mathrm{d}\mu_N$ for all sufficiently large $T$. This yields the desired result for $u$ once we have such an algebra $A$.

We now choose $A$. Upon denoting by $\widehat{\mathbf{T}^N}$ the group of continuous unitary characters of $\mathbf{T}^N$, we consider the subset

$$
A:=\{f\in C(\mathbf{T}^N):f(\xi)=\sum_{0\le k\le N_f}c_k\cdot\chi_k(\xi),\,N_f\in\mathbf{N},\,c_k\in\mathbf{C},\,\chi_k\in\widehat{\mathbf{T}^N}\text{ for all }k\}\subset C(\mathbf{T}^N) \tag{B.5.2.9}
$$

of all finite sums of continuous unitary characters of $\mathbf{T}^N$ with complex coefficients. $A$ is a nonzero $\mathbf{C}$-sub-algebra whose elements separate the points of $\mathbf{T}^N$. Indeed, $A$ is the $\mathbf{C}$-sub-algebra generated by the continuous unitary characters of $\widehat{\mathbf{T}^N}$, and to check the separation condition it is enough to check that given two distinct points $\xi,\xi'\in\mathbf{T}^N$, there exists a continuous unitary character $\chi\in\widehat{\mathbf{T}^N}$ such that $\chi(\xi)\ne\chi(\xi')$. Since $\xi\ne\xi'$, there exists $k\in\mathbf{Z}$ with $1\le k\le N$, such that $\xi_k\ne\xi'_k$. We let $a\in\mathbf{Z}^N$ be such that $a_j=0$ for all $j\ne k$, and $a_k=1$. The corresponding character $\chi$ under the group-isomorphism $\widehat{\mathbf{T}^N}\simeq\mathbf{Z}^N$ separates $\xi$ and $\xi'$.

By the Stone-Weierstrass Theorem, $A\subset C(\mathbf{T}^N)$ is dense with respect to the uniform-norm topology on $C(\mathbf{T}^N)$. By the foregoing, we are reduced to proving that (B.5.2.1) holds for $u$ the arbitrary element in $A$.

Before treating such $u$, we return to the general case (allowing $\mathbf{Q}$-linear dependence among the coordinates of $\tau$). Since $G$ is a closed connected subgroup of $\mathbf{T}^N$, it is itself isomorphic, as a Lie group, to a torus. Any choice of isomorphism $G\simeq\mathbf{T}^d$ of Lie groups pushes forward $\mu_G$ to the standard volume-1 Haar measure on $\mathbf{T}^d$.

We may replace $\mu_N$ with the finite regular Borel measure $\mu$ on $\mathbf{T}^N$ defined on the Borel sets $A$ of $\mathbf{T}^N$ as $\mu(A):=\mu_G(G\cap A)$, and apply Lemma B.5.2.2 with this choice of $\mu$, to propagate the assertion in (B.5.2.1) from the case of continuous complex-valued functions on $G$, to the case of Riemann integrable functions on $G$. The rest of the reductions in the foregoing apply upon replacing $\mathbf{T}^N$ with $G$. Now it remains to treat the $\mathbf{Q}$-linearly independent case (since using a uniformization of $G$ yields $\tau'$ that that satisfies $\mathbf{Q}$-linear independence for its $d$ coordinates).

Any $u\in A$ is of the form

$$
u(\xi)=\sum_{a\in\mathbf{Z}^N}c_a\cdot\xi_1^{a_1}\cdot\ldots\cdot\xi_N^{a_N} \tag{B.5.2.10}
$$

## PDF page 631

**B.5. RECURRENCE AND EQUIDISTRIBUTION** · **631**

with $c_a\ne 0$ for at most finitely many $a\in\mathbf{Z}^N$, and where $\xi\in\mathbf{T}^N$ is written in coordinates $\xi=(\xi_1,\dots,\xi_N)$ since each $\chi\in\widehat{\mathbf{T}^N}\simeq\mathbf{Z}^N$ is of the form

$$
\chi(\xi)=\prod_{k=1}^N\xi_k^{a_k}
$$

for a unique $a=(a_1,\dots,a_N)\in\mathbf{Z}^N$. We write $\chi_a$ for the continuous character of $\mathbf{T}^N$ corresponding to $a\in\mathbf{Z}^N$.

We have

$$
\widehat u(\chi_b)=\int_{\mathbf{T}^N}u(\xi)\cdot\overline{\chi_b(\xi)}\,\mathrm{d}\mu(\xi)=\int_{[0,1)^N}\sum_{a\in\mathbf{Z}^N}c_a\cdot e^{2\pi i a_1 x_1}\cdot\ldots\cdot e^{2\pi i a_N x_N}\cdot\overline{e^{2\pi i b_1 x_1}\cdot\ldots\cdot e^{2\pi i b_N x_N}}\,\mathrm{d}x_1\cdots\mathrm{d}x_N. \tag{B.5.2.11}
$$

By orthogonality of the exponentials $\{e^{2\pi i t N}, N\in\mathbf{Z}\}\subset L^2([0,1))$, we obtain

$$
\widehat u(\chi_b)=c_b. \tag{B.5.2.12}
$$

We have

$$
\lim_{T\to+\infty}\frac{1}{2T}\int_{-T}^T u(e^{2\pi i t\tau_1},\dots,e^{2\pi i t\tau_N})\,\mathrm{d}t=\lim_{T\to+\infty}\frac{1}{2T}\sum_{b\in\mathbf{Z}^N}c_b\int_{-T}^T e^{2\pi i(b_1\tau_1+\cdots+b_N\tau_N)t}\,\mathrm{d}t \tag{B.5.2.13}
$$

where we are allowed to interchange the summation and the integral since $c_b=0$ for all but finitely many $b$.

Suppose $b_1\tau_1+\cdots+b_N\tau_N\ne 0$ for one of the finitely many $b$ such that $c_b\ne 0$. Then we have:

$$
\left|\frac{1}{2T}\int_{-T}^T e^{2\pi i(b_1\tau_1+\cdots+b_N\tau_N)t}\mathrm{d}t\right|\le\frac{1}{2T\pi(b_1\tau_1+\cdots+b_N\tau_N)}|e^{2\pi i(b_1\tau_1+\cdots+b_N\tau_N)T}-e^{-2\pi i(b_1\tau_1+\cdots+b_N\tau_N)T}|=o_b(1) \tag{B.5.2.14}
$$

as $T\to+\infty$.

The right side of (B.5.2.13) therefore equals $\sum_{b:b_1\tau_1+\cdots+b_N\tau_N=0}c_b$. The left side of (B.5.2.13) is also written as

$$
\lim_{T\to+\infty}\frac{1}{2T}\int_{-T}^T u(e^{2\pi i t\tau_1},\dots,e^{2\pi i t\tau_N})\,\mathrm{d}t=\lim_{T\to+\infty}\frac{1}{2T}\int_{-T}^T u(\overline{\gamma}(t))\,\mathrm{d}t.
$$

But $\sum_{b:b_1\tau_1+\cdots+b_N\tau_N=0}c_b=\int_{G^\perp}\widehat u(\chi)\chi(1)\,\mathrm{d}\mu_{G^\perp}(\chi)$ with $\mu_{G^\perp}$ the counting measure on $G^\perp$ dual to the volume-1 measure on $\mathbf{T}^N/G$. This integral over $G^\perp$ is equal to

$$
\int_G u(\xi)\,\mathrm{d}\mu_G(\xi)
$$

by the Poisson summation formula (see Theorem D.1.2.7(3)). The case of $(1/T)\int_0^T$ goes similarly.

$\square$

COROLLARY B.5.2.4 (Uniform distribution). *Pick $\tau=(\tau_1,\dots,\tau_N)\subset\mathbf{R}^N$. Let $\gamma_\tau:\mathbf{R}\to\mathbf{T}^N$ be the continuous 1-parameter group generated by $\tau$. Let $G$ be the closure of the image of $\gamma_\tau$ in $\mathbf{T}^N$, and $\mu_G$ the volume-1 Haar measure on $G$.*

*For every open subset $U\subset[0,1)^N$, upon denoting by $\widehat U$ the image of $U$ in $\mathbf{T}^N$ under the quotient map $\theta$, if $\mu_G(\partial(\widehat U\cap G))=0$ then we have:*

$$
\lim_{T\to+\infty}\frac{\lambda([-T,T]_U)}{2T}=\lim_{T\to+\infty}\frac{\lambda([0,T]_U)}{T}=\mu_G(\widehat U\cap G). \tag{B.5.2.15}
$$

PROOF. The function $u:=\mathrm{1}_{\widehat U\cap G}$ is Riemann-integrable on $G$ since $\mu_G(\partial(\widehat U\cap G))=0$. The identities in (B.5.2.15) are then a special case of (B.5.2.1) from Theorem B.5.2.1.

$\square$

REMARK B.5.2.5. There is a discrete-time version of both Theorem B.5.2.1 and Corollary B.5.2.4. Both are proved by closely adapting the arguments provided above. We further refer the reader to [Hu2, Lemma A.14, p. 93].

## PDF page 632

**632** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

**B.5.3. Strong recurrence of non-Archimedean Euler factors.** We begin by recalling basic concepts on self-approximation properties of holomorphic and meromorphic functions on an open non-empty vertical strip in $\mathbf{C}$.

B.5.3.1. *Strong recurrence.* Let $I\subset\mathbf{R}$ be a non-empty interval. Recall that we write $\mathbf{C}_I$ to denote the vertical strip

$$
\mathbf{C}_I:=\{s\in\mathbf{C}:\mathrm{Re}(s)\in I\}. \tag{B.5.3.1}
$$

In particular, if $I=(a,b)$ is a bounded open interval, we have

$$
\mathbf{C}_I=\{s\in\mathbf{C}:a<\mathrm{Re}(s)<b\}
$$

and if $I=[a,b)$, $(a,\infty)$, respectively $[a,\infty)$, we have

$$
\mathbf{C}_I=\{s\in\mathbf{C}:a\le\mathrm{Re}(s)<b\},\;\mathbf{C}_I=\{s\in\mathbf{C}:\mathrm{Re}(s)>a\},\;\mathbf{C}_I=\{s\in\mathbf{C}:\mathrm{Re}(s)\ge a\}.
$$

DEFINITION B.5.3.1. (1) For a subset $X\subset\mathbf{R}$ we define the upper density of $X$ to be

$$
\limsup_{T\to+\infty}\frac{\lambda([-T,T]\cap X)}{2T}. \tag{B.5.3.2}
$$

(2) Let $I\subset\mathbf{R}$ be an open non-empty interval. We say that a holomorphic function $f:\mathbf{C}_I\to\mathbf{C}$ is strongly recurrent on a compact subset $K\subset \mathbf{C}_{>R}$ if and only if for every $\varepsilon>0$, the set $X_K(\varepsilon)$ of all $t\in\mathbf{R}$ such that

$$
\sup_{s\in K}|f(s+it)-f(s)|<\varepsilon
$$

has positive upper density in $\mathbf{R}$.

We recall that the notion of (strong) "recurrence" for a holomorphic function on a vertical strip $\mathbf{C}_I$, for $I\subset\mathbf{R}$ a non-empty open interval, was studied in B. Bagchi's PhD thesis [Ba1, Ch. 1,2]. Strong recurrence is a self-approximation property of holomorphic functions on vertical strips. We refer the reader to [Ba1, Ch. 1, §1.4] (respectively [Ba1, Ch. 2, §2.3]).

B.5.3.2. Strong recurrence of reciprocal partial Euler products on open strips containing $i\mathbf{R}$. The main result of this section is the following:

PROPOSITION B.5.3.2. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We write $S_f:=S\cap\Sigma_{F,f}$. For each $v\in S_f$, we denote by $\pi_v$ a choice of uniformizer at $v$. Let $\chi\in\widehat{C_F}$ be a continuous character unramified at the finite places of $F$ contained in $S$.*

*There exists a real number $N_S>0$ and a sequence $\{T_k\}_{k\in\mathbf{Z}}\subset\mathbf{R}$, such that:*

(1) $T_k\ge 0$ if $k\ge 0$, $T_k\le 0$ if $k\le 0$, and $T_k\le T_{k+1}|$ for every $k\in\mathbf{Z}$.

(2) $\lim_{|k|\to+\infty}|T_k|=+\infty$.

(3) For all $k\in\mathbf{Z}$, we have:

$$
\prod_{v\in S_f}|\mathrm{1}-\chi(\pi_v)q_v^{-iT_k}|^{-1}\le N_S. \tag{B.5.3.3}
$$

In this subsection we provide a direct argument for Proposition B.5.3.2, resting on the Kronecker-Weyl Theorem and a uniform version of a classical Theorem of Carlson An alternative argument has been provided in Proposition 7.1.1.1 using the results of [Ba1, Ch. 2].

We prove the following stronger assertion:

PROPOSITION B.5.3.3 (Strong recurrence of reciprocal partial Euler products). *Let $F$ be a number field, $S$ a finite set of finite places of $F$. Let $\chi\in\widehat{C_F}$ be a continuous character unramified at all places in $S$.*

## PDF page 633

**B.5. RECURRENCE AND EQUIDISTRIBUTION** · **633**

*Let $I\subset\mathbf{R}$ be an open non-empty bounded interval containing $0\in\mathbf{R}$. Let $K\subset \mathbf{C}_I$ be an arbitrary compact subset with non-empty interior. Then for any real number $\varepsilon>0$, the subsets:*

$$
\left\{t\in[0,+\infty):\sup_{s\in K}\left|\prod_{v\in S}L_v(\chi_v|\cdot|_v^{s+it})^{-1}-\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1}\right|<\varepsilon\right\}\subset\mathbf{R} \tag{B.5.3.4}
$$

and

$$
\left\{t\in(-\infty,0]:\sup_{s\in K}\left|\prod_{v\in S}L_v(\chi_v|\cdot|_v^{s+it})^{-1}-\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1}\right|<\varepsilon\right\}\subset\mathbf{R} \tag{B.5.3.5}
$$

both have positive upper-density.

B.5.3.3. *Preparations on recurrence.* We begin with a few permanence properties of strong recurrence for holomorphic functions on non-empty open vertical strips of bounded width.$^{28}$

LEMMA B.5.3.4. *Let $I\subset\mathbf{R}$ be an open non-empty bounded interval, and $f:\mathbf{C}_I\to\mathbf{C}$ a holomorphic function.*

(1) *If $f$ is strongly recurrent on the compact subset $K\subset \mathbf{C}_I$ then it is strongly recurrent on any compact subset $K'\subset K$.*

(2) *If $f$ is strongly recurrent on any closed disc contained within $\mathbf{C}_I$ then it is strongly recurrent on any compact subset contained within $\mathbf{C}_I$.*

PROOF. We prove (1). If, for every $\varepsilon>0$, the set $X_K(\varepsilon)\subset\mathbf{R}$ has positive upper-density, then so does $X_{K'}(\varepsilon)$, since $X_K(\varepsilon)\subset X_{K'}(\varepsilon)$. This proves (1).

Let $K\subset \mathbf{C}_I$ be an arbitrary compact subset. There exists $c_0>0$ such that

$$
r_0:=\inf\{\sigma\in I:\sigma=\mathrm{Re}(s),\,s\in K\}>\inf I+c_0.
$$



We call $r_1:=\sup\{\sigma\in I:\sigma=\mathrm{Re}(s),\,s\in K\}$, and $r:=r_1-r_0$. Then $K$ is contained within a closed disc $D$ of radius $r$ centered at some $s\in \mathbf{C}_I$. By assumption, $f$ is strongly recurrent on $D$, and hence, by (2), so it is on $K$.

$\square$

Let $f:\mathbf{C}_I\to\mathbf{C}$ be a holomorphic function, with $I\subset\mathbf{R}$ an open non-empty bounded interval.

Sub-harmonicity of $|f|^2$ as a real valued function and on any domain of holomorphy of $f$, ensures that the sup-norm condition in the definition of strong recurrence can be verified through the following Lemma.

We denote by $\mu_A$ the Radon measure associated to the area form $\mathrm{d}s\wedge \mathrm{d}\bar s$ on the complex $s$-plane.

LEMMA B.5.3.5. *Let $I\subset\mathbf{R}$ be a non-empty open bounded interval, and $f:\mathbf{C}_I\to\mathbf{C}$ a holomorphic function. Let $K\subset \mathbf{C}_I$ be a non-empty compact subset, and $U\subset \mathbf{C}_I$ an open subset, such that:*

(1) *The closure of $U$ is compact and contained within $\mathbf{C}_I$.*

(2) *$K\subset U$ and the distance $\delta$ between $K$ and the complement of $U$ is positive.*

Fix $T>0$. Upon defining the subsets

$$
A_{\overline{U},r}(X,T):=\{t\in[-T,T]:\int_{\overline{U}}|f(s+it)-f(s)|^2\,\mathrm{d}\mu_A(s)<X\}\subset\mathbf{R} \tag{B.5.3.6}
$$

$$
A_K(X,T):=\{t\in[-T,T]:\sup_{s\in K}|f(s+it)-f(s)|<X\}\subset\mathbf{R} \tag{B.5.3.7}
$$

*for $X>0$, and the function $c(X):=\pi\delta^2 X^2$, for $X>0$, we have*

$$
A_{\overline{U},2}(c(X),T)\subset A_K(X,T) \tag{B.5.3.8}
$$

$^{28}$Brian needs to check the next two lemmas and how they are used in the subsequent proof of the preceding Proposition.

## PDF page 634

**634** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

for all $T>0$.

PROOF. We first show that an open subset $U\subset \mathbf{C}_I$ satisfying the assumptions (1),(2) exists, to conclude that the statement is non-vacuous. Let $a>0$ be the distance between $K$ and the complement of $\mathbf{C}_I$, and cover $K$ with finitely many discs of radius $a/2$. The union of their interiors is an example of such $U$. It is totally bounded by compactness of $K$. Its boundary is contained in a finite union of circles, and hence it is contained within $\mathbf{C}_I$. The closure of $U$ is therefore also contained within $\mathbf{C}_I$.

For any $s\in K$, we therefore have $\overline{D}_\delta(s)\subset U$.

We fix $s\in K$ arbitrary. Since, for every $t\in\mathbf{R}$, $|f(z+it)-f(z)|^2$ is a sub-harmonic function of $z\in U$, it follows that

$$
|f(s+it)-f(s)|^2\le\frac{1}{\pi\delta^2}\int_{\overline{D}_\delta(s)}|f(z+it)-f(z)|^2\,\mathrm{d}\mu_A(z)\le\frac{1}{\pi\delta^2}\int_{\overline{U}}|f(z+it)-f(z)|^2\,\mathrm{d}\mu_A(z) \tag{B.5.3.9}
$$

where $\mathrm{d}\mu_A(z)=|\mathrm{d}x\,\mathrm{d}y|$, for $z=x+iy$, is the normalized area measure on the complex $z$-plane. If $t\in\mathbf{R}$ satisfies the condition

$$
\int_{\overline{U}}|f(s+it)-f(s)|^2\,\mathrm{d}\mu_A(s)<\pi\delta^2 X^2=c(X) \tag{B.5.3.10}
$$

then by (B.5.3.9) we have, for all $s\in K$

$$
|f(s+it)-f(s)|<X. \tag{B.5.3.11}
$$

Since (B.5.3.10) implies (B.5.3.11) we therefore have $A_{\overline{U},2}(c(X),T)\subset A_K(X,T)$.

$\square$

B.5.3.4. *Strong recurrence of reciprocal finite Euler products.* We can now prove Proposition B.5.3.3.

PROOF of Proposition B.5.3.3. We denote by $\lambda$ the Lebesgue measure on the real line, normalized so as to give the interval $[0,1]$ volume 1. We define:

$$
u(s,(t_v)_{v\in S}):=\prod_{v\in S}L_v(\chi_v|\cdot|_v^{s+it_v\frac{2\pi}{\log(q_v)}})^{-1}-\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1} \tag{B.5.3.12}
$$

for $q_v:=N(\mathfrak{p}_v)$, with $\mathfrak{p}_v\subset\mathcal{O}_F$ the prime ideal corresponding to the finite place $v$ of $F$.

Since $\chi$ is unramified at $v\in S$, we have $L_v(\chi_v|\cdot|_v^s)^{-1}=1-\chi_v(\pi_v)q_v^{-s}|$. Thus, the function $u:\mathbf{C}\times\mathbf{T}^S\to\mathbf{C}$ is continuous and its holomorphic derivatives of arbitrary order with respect to $s$, formed pointwise over $\mathbf{C}\times\mathbf{T}^S$, are also continuous over $\mathbf{C}\times\mathbf{T}^S$.

Let $K\subset \mathbf{C}_I$ be a compact subset with non-empty interior. We define, for every real number $\varepsilon>0$:

$$
X(\varepsilon):=\{(t_v)_{v\in S}:\int_K|u(s,(t_v)_{v\in S})|^2\,\mathrm{d}\mu_A(s)<\varepsilon\}\subset\mathbf{T}^S. \tag{B.5.3.13}
$$

Since $u(s,\cdot)$ is a continuous function on $\mathbf{T}^S$ and $K$ is compact, $\int_K|u(s,(t_v)_{v\in S})|^2\,\mathrm{d}\mu_A(s)$ is also continuous on $\mathbf{T}^S$ and has a zero at $0\in\mathbf{T}^S$ (i.e. at $(t_v)_{v\in S}=0$). It follows that $X(\varepsilon)$ is open and non-empty.

We define $\tau=(\tau_v)_{v\in S}$ to be the vector in $\mathbf{R}^S$ whose coordinates are $\tau_v:=\frac{\log(q_v)}{2\pi}$.

We denote by $\gamma_\tau:\mathbf{R}\to\mathbf{R}^S$ the continuous 1-parameter subgroup generated by $\tau$, and by $\bar\gamma_\tau:\mathbf{R}\to\mathbf{T}^S$ the continuous 1-parameter group obtained by composition with the quotient homomorphism $\theta_S:\mathbf{R}^S\to\mathbf{T}^S$.

Note that

$$
u(s,\bar\gamma_\tau(t))=\prod_{v\in S}L_v(\chi_v|\cdot|_v^{s+it})^{-1}-\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1}.
$$

We denote by $G$ the closure of the image of $\gamma_\tau$ in $\mathbf{T}^S$, a closed sub-torus. We call $\mu_G$ the volume-1 Haar measure on $G$.

Assume for the moment that we have $\mu_G(\partial(X(\varepsilon)\cap G))=0$. Then by Corollary B.5.2.4 we have

$$
\lim_{T\to+\infty}\frac{\lambda(\{t\in[-T,T]:\bar\gamma_\tau(t)\in X(\varepsilon)\})}{2T}=\lim_{T\to+\infty}\frac{\lambda(\{t\in[0,T]:\bar\gamma_\tau(t)\in X(\varepsilon)\})}{T}=\mu_G(X(\varepsilon)\cap G) \tag{B.5.3.14}
$$

## PDF page 635

**B.5. RECURRENCE AND EQUIDISTRIBUTION** · **635**

and since $X(\varepsilon)\cap G$ is open in $G$ and non-empty (it contains the neutral element), its $\mu_G$-measure is positive.

Since we have:

$$
\{t\in I_T:\bar\gamma_\tau(t)\in X(\varepsilon)\}=\left\{t\in I_T:\int_K|\prod_{v\in S}L_v(\chi_v|\cdot|_v^{s+it})^{-1}-\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1}|^2\,\mathrm{d}\mu_A(s)<\varepsilon\right\} \tag{B.5.3.15}
$$

for $I_T$ either of the two intervals $[-T,T]$ and $[0,T]$, we deduce from (B.5.3.14), from positivity of $\mu_G(X(\varepsilon)\cap G)$, and from Lemma B.5.3.5, that $\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1}$ is indeed strongly recurrent over $\mathbf{C}_I$ (with a different $\varepsilon>0$ dependent on $\varepsilon$ and the distance between $K$ and the boundary of the strip) for $K\subset \mathbf{C}_I$ any compact subset with non-empty interior, and hence in particular for $K$ satisfying the assumptions of the Proposition. By combining (B.5.3.15) with (B.5.3.14) all assertions of the Proposition follow.

We now prove that we have $\mu_G(\partial(X(\varepsilon)\cap G))=0$, so that the Kronecker-Weyl Theorem (see Theorem B.5.2.1), through its Corollary B.5.2.4, applies. Let $d$ the dimension of the $\mathbf{Q}$-linear subspace of $\mathbf{R}$ generated by $(\tau_v)_{v\in S}$. The locus $\{(t_v)_{v\in S}\in G:\int_K|u(s,(t_v)_{v\in S})|^2\,\mathrm{d}\mu_A(s)=\varepsilon\}$ contains $\partial(X(\varepsilon)\cap G)$, and it has $\mu_G$-measure zero. To see this, we proceed as follows.

The subset:

$$
U:=\{(t_v)_{v\in S}\in G:\int_K|u(s,(t_v)_{v\in S})|^2\,\mathrm{d}\mu_A(s)=\varepsilon\}
$$

which reads

$$
\{(t_v)_{v\in S}\in G:\int_K((\mathrm{Re}(u)(s,(t_v)_{v\in S}))^2+(\mathrm{Im}(u)(s,(t_v)_{v\in S}))^2)\,\mathrm{d}\mu_A(s)=\varepsilon\}
$$

as a subset of $G$ pulls back to an analytic subset of $\mathbf{T}^d$ (the zero set of a nonzero real-analytic function) under any isomorphism $\mathbf{T}^d\simeq G$ of Hausdorff locally compact abelian groups, upon observing that any isomorphism of Hausdorff locally compact abelian groups $\mathbf{T}^d\simeq G$ is also a real-analytic diffeomorphism.

This is so, because the continuous function of $(t_v)_{v\in S}$:

$$
(t_v)_{v\in S}\mapsto\int_K|u(s,(t_v)_{v\in S})|^2\,\mathrm{d}\mu_A(s)
$$

is itself analytic, and $U$ is one of its level sets. Note that since $\varepsilon>0$, $U$ does not contain $(t_v)_{v\in S}=0$, and hence this function is analytic and nonzero, thus exhibiting $U$ as an analytic subset of $G$.

Since $\theta_S$ is itself analytic (i.e. its coordinate functions are complex-valued real-analytic functions) then the pre-image of $U$ in $\mathbf{R}^S$ under $\theta_S$ is a real-analytic subset of $\mathbf{R}^S$, and its intersection with $[0,1)^S$ therefore has Lebesgue measure zero by [Mit, Prop. 1]. Its image under the smooth composition of $\theta_S$ followed by the real-analytic diffeomorphism $\mathbf{T}^d\to G$ therefore has $\mu_G$-measure zero.

$\square$

Proposition B.5.3.2 follows from Proposition B.5.3.3 by choosing a small disc whose interior is non-empty and intersects $i\mathbf{R}$ in a non-empty open vertical interval containing none of the zeros of $\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1}$, nor in its interior nor on its boundary, and choosing it as $K$ in Proposition B.5.3.3. Over $K$, the absolute value of $\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1}$ is therefore strictly positive, and since $|\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)|$ is continuous over $K$, it attains a maximum $M>0$, and hence $|\prod_{v\in S}L_v(\chi_v|\cdot|_v^s)^{-1}|$ is bounded below by $1/M$. By choosing $\varepsilon>0$ in Proposition B.5.3.3 tiny compared to $1/M$, the Proposition implies that there exists a subset of $t\in\mathbf{R}$ of the real line of positive upper density such that $\prod_{v\in S}L_v(\chi_v|\cdot|_v^{s+it})$ is, for all such $t$'s, bounded above in absolute value by a positive real number independent of $s\in K$ (so including $s=0\in K$).

The positivity of the upper density implies the existence of a sequence $\{T_k\}$ satisfying the requirements of Proposition B.5.3.2.

## PDF page 636

**636** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

**B.6. Classical zero-free regions for Hecke $L$-functions**

In this section, we recall well known results on the existence of classical zero-free regions for general Hecke $L$-functions of arbitrary number fields, and discuss estimates on the polynomial growth of the finite $L$-function, its holomorphic derivatives of any order on vertical strips of bounded width, and of its reciprocal on the $1$-line.

**B.6.1. Zero-free regions for Hecke $L$-functions and estimates on $L'_f(s,\chi)/L_f(s,\chi)$.** We record here analogs of the main results on zero-free regions for the Riemann $\zeta$-function, and estimates for $\zeta'(s)/\zeta(s)$ on the $1$-line, adapted to the case of finite Hecke $L$-functions.

B.6.1.1. *Classical zero-free region for $L_f(s,\chi)$.* We recall the statement of the following well-known result, whose proof goes back to the argument of Hadamard and de la Vallée Poussin:

Proposition B.6.1.1 (Classical zero-free region for $L_f(s,\chi)$). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. There exists an absolute constant $A>0$, and a real number $A_{F,\chi}>0$ depending only on $F$ and $\chi$, such that $L_f(s,\chi)$ has no complex zeros in the region:*

$$
\sigma\ge 1-\frac{A}{[F:\mathbf Q]^4\log(A_{F,\chi}(|t|+3))} \tag{B.6.1.1}
$$

*and if $L_f(\sigma,\chi)=0$ for some $\sigma\in[1/2,1]$ then $\chi$ is quadratic and $\sigma$ is unique, simple, and satisfies $\sigma<1$.*

The real number $A_{F,\chi}$ can in fact be chosen to be $|N(\mathfrak{d}_{F/\mathbf Q})||N_{F/\mathbf Q}(\mathfrak f_\chi)|$ where $\mathfrak f_\chi$ is the conductor of $\chi$ [IK, Ch. 5, §5.1, (5.4)]. Proposition B.6.1.1 can be deduced from [IK, §5.4, Thm. 5.10, p. 106] upon setting $d=[F:\mathbf Q]$, $A_{F,\chi}:=\mathfrak{q}(f,0)$ in the notation of loc.cit. to denote the analytic conductor of the $L$-function (see [IK, Ch. 5, (5.7), p. 95]), and noting that the Rankin-Selberg convolutions $L_f(s,\chi\otimes\chi)$ and $L_f(s,\chi\otimes\bar\chi)$ both exist with the former entire when $\chi\ne\overline{\chi}$ (equivalently, when $\chi^2\ne 1$) since $L_f(s,\chi^2)$ is entire when $\chi$ is not quadratic, and the latter is $\zeta_F(s)$ (so it has a simple pole at $s=1$).

B.6.1.2. *Estimates for $L'_f(s,\chi)/L_f(s,\chi)$.* Let $F$ be a number field and $\chi\in\widehat{C_F}$ a continuous character.

On $\mathbf C_{>1}$, the Dirichlet series expansion of the associated “finite” Hecke $L$-function is

$$
L_f(s,\chi)=\sum_{0\ne I\subset\mathcal O_F}\frac{\chi(I)}{N(I)^s} \tag{B.6.1.2}
$$

(sum over nonzero ideals) and we define the summatory function

$$
S_{F,\chi}(x):=\sum_{I\subset\mathcal O_F:N(I)\le x}\chi(I). \tag{B.6.1.3}
$$

We note that we may define, for every real $x\ge 0$ the coefficients

$$
a_x:=\sum_{I\subset\mathcal O_F:N(I)=x}\chi(I) \tag{B.6.1.4}
$$

as a sum over nonzero ideals (so $a_x:=0$ if the set indexing the sum is empty). For instance, if $x$ is not of the form $N(I)$ for a nonzero ideal $I\subset\mathcal O_F$ (such as whenever $x$ is not an integer, or when $x=0$) then $a_x=0$.

We recall from [CF, Ch. VIII, §1, p. 205] that a continuous character $\chi\in\widehat{C_F}$ of the idele class group (equivalently a continuous character $\chi$ of the idele group $\mathrm{GL}_1(\mathbf A_F)$ such that $\chi(F^\times)=1$) is unramified outside a finite set $S$ of finite places of $F$ and so uniquely determines a character $\chi$ of the group $\mathrm{Div}(\mathcal O_{F,S})$ of fractional ideals via $\chi(I):=\chi(\mathfrak{a}_I)$ where $\mathfrak{a}_I\in\mathrm{GL}_1(\mathbf A_F)$ is the idele defined to have $v$-indexed coordinate $1$ if $v\in S\cup\Sigma_{F,\infty}$ and equal to $\pi_v^{\mathrm{ord}_v(I)}$ for $\pi_v$ a choice of local uniformizer in $F_v$ for finite $v\notin S$. This function $\chi$ of $\mathrm{Div}(\mathcal O_{F,S})$ satisfies $\chi(IJ)=\chi(I)\chi(J)$, so we can rewrite the Dirichlet series in (B.6.1.2) in the more

## PDF page 637

**B.6. CLASSICAL ZERO-FREE REGIONS FOR HECKE L-FUNCTIONS** · **637**

familiar form

$$
L_f(s,\chi)=\sum_{m\ge 1}\frac{a_m}{m^s}. \tag{B.6.1.5}
$$

We have $a_{mn}=a_ma_n$ for coprime integers $m,n\ge 1$ because any ideal $I\subset\mathcal O_F$ satisfying $N(I)=mn$ can be uniquely written as $I=JK$ for ideals $J,K\subset\mathcal O_F$ with $N(J)=m$ and $N(K)=n$.

The $m$th Dirichlet series coefficient $a_m$ of $L_f(\chi,s)$ satisfies

$$
|a_m|\le\#\{I\subset\mathcal O_F:N(I)=m\}\le\tau(m)^{[F:\mathbf Q]}
$$

where $\tau(m):=\#\{d\mid m\}$, so $a_m=O_{F,\varepsilon}(m^\varepsilon)$ for all $\varepsilon>0$. By similar reasoning, for every $\varepsilon>0$ we have

$$
S_{F,\chi}(x)\ll_\varepsilon x^{1+\varepsilon}. \tag{B.6.1.6}
$$

We record here the following consequence of the analytic behavior of $L_f(s,\chi)$:

Lemma B.6.1.2. *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character.*

*(1) If $\chi|_{C^1_F}$ is trivial then for the unique real number $t_0\in\mathbf R$ such that $\chi=|\cdot|^{-it_0}_F$ we have*

$$
\frac{S_{F,\chi|\cdot|^{it_0}_F}(x)}{x}=N(\mathfrak{d}_{F/\mathbf Q})^{-1/2}\overline{\mu}_1(C^1_F)+o(1) \tag{B.6.1.7}
$$

*(2) If $\chi|_{C^1_F}$ is non-trivial then*

$$
\frac{S_{F,\chi}(x)}{x}=o(1). \tag{B.6.1.8}
$$

*Proof.* (1) : The Hecke $L$-function $L_f(s,\chi|\cdot|^{it_0}_F)=\zeta_F(s)$ has a simple pole at $s=1$ whose residue is $N(\mathfrak{d}_{F/\mathbf Q})^{-1/2}\overline{\mu}_1(C^1_F)$. Upon applying [MVa, Cor. 8.8] with $c=N(\mathfrak{d}_{F/\mathbf Q})^{-1/2}\overline{\mu}_1(C^1_F)$, we see that (B.6.1.7) holds.

(2) : The Hecke $L$-function $L_f(s,\chi)$ is holomorphic over $\mathbf C_{>0}$. Upon applying [MVa, Cor. 8.8] with $c=0$, we see that (B.6.1.8) holds. $\square$

The following result is well-known to experts (see, for instance, [SW, §4, (4.1)]) and it is recorded in [T2, Ch. III, (3.11.7)] for $F=\mathbf Q$ and $\chi=1$. We provide the argument here below, following [Ingh3, Thm. 20, p. 60-62].

Theorem B.6.1.3. *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let*

$$
\eta:\mathbf R_{\ge 0}\to\mathbf R_{>0} \tag{B.6.1.9}
$$

*be a differentiable decreasing function satisfying the following conditions:*

*(1) $\eta(\mathbf R_{\ge 0})\subset(0,1/2]$.*

*(2) $\lim_{t\to+\infty}\eta'(t)=0$.*

*(3) $1/\eta(t)=O(\log(t))$.*

*Let $\alpha=\alpha_F$ be a real number satisfying $0<\alpha<1$ such that $\zeta_F(s)$ is non-vanishing on $\{0<|s-1|<\alpha\}. $ Assume that $L_f(s,\chi)$ has no zeros in the region*

$$
\sigma>1-\eta(|t|).
$$

*Then*

$$
\frac{L'_f(s,\chi)}{L_f(s,\chi)}=O_{\alpha,\chi}((\log(t))^2) \tag{B.6.1.10}
$$

*uniformly in the region*

$$
\sigma\ge 1-\alpha\eta(|t|) \tag{B.6.1.11}
$$

## PDF page 638

**638** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

*as $|t|\to+\infty$.*

*Proof.* The function $L'_f(s,\chi)/L_f(s,\chi)$ is holomorphic over $\mathbf C_{>1}$ and there it is an absolutely convergent Dirichlet series

$$
-\sum_{I\subset\mathcal O_F}\frac{\Lambda_{F,\chi}(I)}{N(I)^s} \tag{B.6.1.12}
$$

where

$$
\Lambda_{F,\chi}(I):=\chi(I)\Lambda_F(I)
$$

with the von Mangoldt function $\Lambda_F$ for $F$ defined by

$$
\Lambda_F(I):=\begin{cases}\log(N\mathfrak p), & I=\mathfrak p^k\text{ a prime power with }k\ge 1,\\ 0, & \text{otherwise (including }I=(1)\text{).}\end{cases} \tag{B.6.1.13}
$$

We define, for every integer $m\ge 1$:

$$
A_m:=\sum_{I\subset\mathcal O_F:N(I)=m}\chi(I)\Lambda_F(I), \tag{B.6.1.14}
$$

as a sum over the ideals of $\mathcal O_F$ whose norm is $m$ (so $A_1=0$ since $\Lambda_F((1))=0$).

Lemma B.6.1.4. *For $A_m$ as in* (B.6.1.14), $A_m=O_F(\log m)$ *as $m\to\infty$, where the $O$-constant depends on $[F:\mathbf Q]$ but not $\chi$.*

*Proof.* From the definition, $|A_m|\le\sum_{\mathfrak p,k:N(\mathfrak p^k)=m}\log(N\mathfrak p)$ where the sum is over prime ideals $\mathfrak p$ and integers $k\ge 1$ (recall $A_1=0$). If $m$ is not a prime power $>1$ then $A_m=0$, so we can assume $m=p^r$ with a rational prime $p$ and exponent $r\ge 1$. Then the equality $N(\mathfrak p^k)=m=p^r$ forces $\mathfrak p\mid p$, allowing at most $[F:\mathbf Q]$ possibilities for $\mathfrak p$ (given $m=p^r$), and for each such $\mathfrak p$ there is at most one possibility for $k$. Thus,

$$
|A_m|\le[F:\mathbf Q]\max_{\mathfrak p\mid p}\log(N\mathfrak p)\le[F:\mathbf Q]^2\log(p)\le[F:\mathbf Q]^2\log(m).
$$

$\square$

We will now be using Proposition B.1.1.3 and the method of proof of [Ingh3, Thm.20] to establish the Theorem. Without loss of generality, we may assume $t>0$ (e.g., pass to $\overline{L_f(s,\chi)}=L_f(\bar s,\bar\chi)$). Assume first that $\sigma>1+\alpha\eta(t)$. Then we have, from the absolute and locally uniform convergence of the Dirichlet series in (B.6.1.12):

$$
\left|\frac{L'_f(\chi,s)}{L_f(s,\chi)}\right|\le\sum_{I\subset\mathcal O_F}\frac{\Lambda_F(I)}{N(I)^{1+\alpha\eta(t)}}=-\frac{\zeta'_F(1+\alpha\eta(t))}{\zeta_F(1+\alpha\eta(t))}\le\frac{A}{\alpha\eta(t)} \tag{B.6.1.15}
$$

for some $A=A_F>0$ since $-\zeta'_F(s)/\zeta_F(s)=1/(s-1)+O(1)$ as $s\to 1$. By condition (3) on $\eta$, $A/\alpha\eta(t)=O(\log(t))$.

Since $L_f(s,\chi)$ is holomorphic and nonzero over the domain

$$
\Omega:=\{s=\sigma+it\in\mathbf C:\sigma>1-\eta(t),\,t>0\}
$$

and $\Omega$ is simply connected, the Dirichlet series

$$
Z_{F,\chi}(s):=\sum_{\mathfrak p,m}\frac{\chi(\mathfrak p)^m}{mN(\mathfrak p)^{ms}} \tag{B.6.1.16}
$$

on $\mathbf C_{>1}$ (where the sum is indexed by the prime ideals of $\mathcal O_F$ and by the positive integers $m\ge 1$) defines a branch of $\log L_f(s,\chi)$ that extends holomorphically over $\Omega$.

For $T>1$, we define

$$
s_0:=1+\alpha\eta(T)+iT \tag{B.6.1.17}
$$

## PDF page 639

**B.6. CLASSICAL ZERO-FREE REGIONS FOR HECKE L-FUNCTIONS** · **639**

and define the two circle

$$
\gamma_1(T):=\{s\in\mathbf C:|s-s_0|=2\alpha\eta(T)\}, \tag{B.6.1.18}
$$

$$
\gamma_2(T):=\left\{s\in\mathbf C:|s-s_0|=\frac{1+3\alpha}{2}\eta(T)\right\}.
$$

The two circles $\gamma_1(T),\gamma_2(T)$, whose radii we call $r_1(T)<r_2(T)<1$, are the same as in the proof of [Ingh3, Thm. 20, p. 62] (see [Ingh3, Thm. 20, Fig. 4, p. 61]), they share the same center $s_0$ defined in (B.6.1.17), and $\gamma_1(T)$ is enclosed within $\gamma_2(T)$.

There exists $T_1>1$ such that for all $T>T_1$, we have $\gamma_1(T),\gamma_2(T)\subset\Omega$: the argument to see this is provided in the proof of [Ingh3, Thm. 20, p. 62], and it rests on the fact that $\eta$ is decreasing, and on assumptions (1) and (2).

It follows that for all $T>T_1$, then $Z_{F,\chi}$ is holomorphic over the open disc $D_2(T)$ whose boundary is $\gamma_2(T)$. By Proposition B.1.1.3, applied to $\sigma=1/2$ (in the notation of the Proposition), we have that there exists $T_2>T_1$ such that

$$
\mathrm{Re}(Z_{F,\chi}(\sigma+it))=\log|L_f(\sigma+it,\chi)|\le\log(A_2t^{1+[F:\mathbf Q]/4})\le B_F\log(T) \tag{B.6.1.19}
$$

over $D_2(T)$ for all $T>T_2$, since $T-1<t<T+1$ for each $s=\sigma+it\in D_2(T)$ (as $r_2(T)<1$ and $\mathrm{Im}(s_0)=T$).

We further note that since $\#\{\mathfrak p\mid p\}\le[F:\mathbf Q]$ for all rational primes $p$,

$$
|{\rm R\mathrm{e}}(Z_{F,\chi}(s_0))|\le|Z_{F,\chi}(s_0)|\le\sum_{\mathfrak p,m}\frac{1}{mN(\mathfrak p)^{1+\alpha\eta(T)}}<[F:\mathbf Q]\sum_{m\ge 2}\frac{1}{m^{1+\alpha\eta(T)}}=[F:\mathbf Q](\zeta_{\mathbf Q}(1+\alpha\eta(T))-1)<\frac{2[F:\mathbf Q]}{\alpha\eta(T)}\le C_F\log(T)
$$

for all sufficiently large $T$.

By [Ingh3, Thm. E, p. 50] applied to $f=Z_{F,\chi}$, $z_0=s_0$, $r=r_1(T)$, $R=r_2(T)$, $U=C_F\log(T)$, we obtain

$$
|Z'_{F,\chi}(s)|<\frac{2r_2(T)}{(r_2(T)-r_1(T))^2}\{C_F\log(T)-{\rm R\mathrm{e}}(Z_{F,\chi}(s_0))\}<\frac{4(1+2\alpha)}{(1-\alpha^2)\eta(T)}\left(C_F\log(T)+\frac{1}{\alpha\eta(T)}\right) \tag{B.6.1.20}
$$

over the closure of the smaller disc $\overline{D}_1(T)$. The inequality in (B.6.1.20) holds in particular on the horizontal radial segment from the center $s_0$ to $1\pm\alpha\eta(T)+iT$ on $\gamma_1(T)$. Equivalently, the inequality holds at all $s=\sigma+iT$ with $1-\alpha\eta(T)\le\sigma\le 1+\alpha\eta(T)$.

By assumption (3) on $\eta$ and (B.6.1.20), we obtain $|Z'_{F,\chi}(s)|=O((\log(T))^2)$, and since $Z_{F,\chi}(s)=\log L_f(s,\chi)$ over $\overline{D}_2(T)\subset\Omega$, (B.6.1.10) follows on $\{1-\alpha\eta(t)\le\sigma\le 1+\alpha\eta(t):t\ge 1\}$. We already treated $\sigma>1+\alpha\eta(t)$ for $t\ge 1$, so we are done. $\square$

Corollary B.6.1.5 (Logarithmic derivative on the $1$-line). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Then*

$$
\frac{L'_f(1+it,\chi)}{L_f(1+it,\chi)}=O((\log(t))^2) \tag{B.6.1.21}
$$

*as $|t|\to+\infty$, where the implied constant depends only on $F$ and $\chi$.*

*Proof.* Choose $A$ small enough so that

$$
\eta(t):=\frac{A}{[F:\mathbf Q]^4\log(A_{F,\chi}(|t|+3))}
$$

satisfies $\eta(\mathbf R_{\ge 0})\subset(0,1/2]$. By Proposition B.6.1.1 and Theorem B.6.1.3, $L'_f(s,\chi)/L_f(s,\chi)=O((\log(t))^2)$ uniformly in the region $\sigma\ge 1-\alpha\eta(|t|)$ for some $\alpha\in(0,1)$, the implied constant depending on $\alpha$. In particular, (B.6.1.21) holds. $\square$

## PDF page 640

**640** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

B.6.1.3. *Polynomial growth of the reciprocal finite Hecke $L$-function on the $1$-line.* We record here below a polynomial growth estimate for the reciprocal of the finite Hecke $L$-function over the $1$-line. We will not be needing sharper sub-polynomial estimates.

Theorem B.6.1.6 (Polynomial growth of reciprocals on the $1$-line). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. There exists an integer $N=N_\chi>0$ such that we have:*

$$
\frac{1}{L_f(1+it,\chi)}=O_N(|t|^N) \tag{B.6.1.22}
$$

*as $|t|\to+\infty$.*

*Proof.* By the inequality $3+4\cos(\theta)+\cos(2\theta)=2(\cos\theta+1)^2\ge 0$ for all $\theta\in\mathbf R$ and by absolute convergence of the Euler product of $L_f(s,\chi)$ for $s\in\mathbf C_{>1}$, we have, following the proof of [CF, Ch. VIII, Thm. 2, p. 212]:

$$
|\zeta_F(\sigma)^3L(\sigma+it,\chi)^4L(\sigma+2it,\chi^2)|\ge 1 \tag{B.6.1.23}
$$

for $\sigma>1$ and all $t\in\mathbf R$. By the Convexity Bound from Proposition B.1.1.3, for every $\varepsilon>0$, there exists a real number $A_1>0$ depending on $\varepsilon>0$ and $\chi$ but not on $s\in\mathbf C$, and a real number $t_0(\varepsilon)>0$ such that

$$
|L_f(s,\chi)|\le A_1|t|^{[F:\mathbf Q]\frac{1-\sigma}{2}+\varepsilon} \tag{B.6.1.24}
$$

for all $\sigma\in[0,1]$ and $t\in\mathbf R$ such that $|t|>t_0(\varepsilon)$.

By Corollary B.6.1.5 we obtain that there exists a real number $A_2>0$ and a real number $t_1>0$ such that for all real numbers $t\in\mathbf R$ such that $|t|>t_1$, we have:

$$
\left|\frac{L'_f(1+it,\chi)}{L_f(1+it,\chi)}\right|\le A_2|\log(t)|^2. \tag{B.6.1.25}
$$

Since $L'_f(s,\chi)/L_f(s,\chi)$ is bounded on vertical lines within $\mathbf C_{>1}$ (it is an absolutely convergent Dirichlet series on $\mathbf C_{>1}$), by (B.6.1.10) applied over $\mathbf C_{\ge 1}$ we can use the Phragmen-Lindelöf Theorem [Lang-c, Ch. XII, §6, Cor. 6.3] to deduce that there exists a real number $A_3>0$ and a real number $t_2>0$ such that for all real numbers $|t|>t_2$ we have:

$$
\left|\frac{L'_f(s,\chi)}{L_f(s,\chi)}\right|\le A_3|t| \tag{B.6.1.26}
$$

uniformly over the vertical strip $\mathbf C_{[1,\sigma_0]}$ for any fixed $\sigma_0>1$, with $A_3$ and $t_2$ depending on $\chi$ and the choice of $\sigma_0$.

By (B.6.1.24) and (B.6.1.26), there exists an integer $N'>0$, a real number $A_4>0$, a real number $t_3>0$, such that for every real number $|t|>t_2$ we have uniformly over the vertical strip $\mathbf C_{[1,\sigma_0]}$:

$$
|L'_f(\chi,s)|\le A_4|t|^{N'}. \tag{B.6.1.27}
$$

By (B.6.1.23) and (B.6.1.24) (applied to $\chi^2$), we obtain that there exists an integer $M>0$ and a real number $B>0$ such that for every $|t|>T>\max\{t_0(\varepsilon),t_1,t_2,t_3\}$ we have:

$$
(\sigma-1)^3\le((\sigma-1)\zeta_F(\sigma))^3|L_f(\sigma+it,\chi)|^4|L_f(\sigma+it,\chi^2)|\le B|t|^{[F:\mathbf Q]\frac{1-\sigma}{2}+\varepsilon}|L_f(\sigma+it,\chi)|^4 \tag{B.6.1.28}
$$

for $\sigma\in(1,\sigma_0]$ and all $|t|>T$. We therefore have the inequality:

$$
|L_f(\sigma+it,\chi)|\ge\frac{(\sigma-1)^{\frac{3}{4}}}{B|t|^{[F:\mathbf Q]\frac{1-\sigma}{8}+\frac{\varepsilon}{4}}} \tag{B.6.1.29}
$$

for $\sigma\in(1,\sigma_0]$ and all $|t|>T$, which remains valid for $\sigma=1$ too.

## PDF page 641

**B.6. CLASSICAL ZERO-FREE REGIONS FOR HECKE L-FUNCTIONS** · **641**

We fix $\sigma_1\in(1,\sigma_0]$ and obtain:

$$
|L_f(1+it,\chi)-L_f(\sigma_1+it,\chi)|\le\int_1^{\sigma_1}|L'_f(x+it,\chi)|\mathrm{d}x\le(\sigma_1-1)A_4|t|^{N'} \tag{B.6.1.30}
$$

for all $|t|>T$. We obtain from (B.6.1.29) and (B.6.1.30) that

$$
|L_f(1+it,\chi)|\ge\frac{(\sigma_1-1)^{\frac{3}{4}}}{B|t|^{[F:\mathbf Q]\frac{1-\sigma_1}{8}+\frac{\varepsilon}{4}}}-(\sigma_1-1)A_4|t|^{N'}\ge\frac{(\sigma_1-1)^{\frac{3}{4}}}{B|t|^{\frac{\varepsilon}{4}}}-(\sigma_1-1)A_4|t|^{N'} \tag{B.6.1.31}
$$

for all $|t|>T$.

We now solve for $\sigma_1$ in the equation

$$
\frac{(\sigma_1-1)^{\frac{3}{4}}}{B|t|^{\frac{\varepsilon}{4}}}=2(\sigma_1-1)A_4|t|^{N'} \tag{B.6.1.32}
$$

to get

$$
\sigma_1(t)=\frac{1}{16\cdot B^4A_4^4|t|^{\varepsilon+4N'}}+1, \tag{B.6.1.33}
$$

and upon enlarging $T$ if necessary to ensure $\sigma_1(t)\in(1,\sigma_0]$ whenever $|t|>T$, we obtain:

$$
|L_f(1+it,\chi)|\ge\frac{1}{16\cdot B^4A_4^3|t|^{\varepsilon+3N'}} \tag{B.6.1.34}
$$

for all $|t|>T$. This proves that (B.6.1.22) holds, with an implied constant that depends on $\varepsilon$ and $N'$. $\square$

The next result is an analog for the reciprocal $1/L_f(s,\chi)$ of the finite Hecke $L$-function, of [Lang-b, Ch. XVII, §2, Prop. 2.7] on the existence of horizontal segments on which the logarithmic derivative of the completed Hecke $L$-function has no singularities and grows at most polynomially with respect to the absolute ordinate. In the special $F=\mathbf Q$ and $\chi=1$ it recovers [T2, Thm. 9.7].

We recall the following definition from (6.3.1.6) of Terminology 6.3.1.1: for $F$ a number field, $\chi\in\widehat{C_F}$ a continuous character, and $S$ a finite set of places of $F$ containing all the Archimedean places and with $S_f$ its subset of finite places, we define:

$$
L_{\Sigma_F-S}(\chi,s):=\prod_{v\in S}L_v(\chi_v|\cdot|^s_v)^{-1}L(s,\chi)
$$

a meromorphic function on $\mathbf C$ which agrees with the product of the finite Hecke $L$-function $L_f(s,\chi)$ and the finite product of entire functions $\prod_{v\in S_f}L_v(\chi_v|\cdot|^s_v)^{-1}$, where $L_v(\chi_v|\cdot|^s_v)$ is the local Euler factor at $v\in S_f$ of the Hecke $L$-function $L(s,\chi)$. The follow

Theorem B.6.1.7 (Slow growth near the poles of $1/L_{\Sigma_F-S}(\chi,s)$ - I). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. There exists a real number $A>0$ such that for all sufficiently large $T$ (depending on $\chi$ and $S$), the interval $(T,T+1)$ contains a real number $t$ such that*

$$
|L_{\Sigma_F-S}(\chi,\sigma+it)|>|t|^{-A} \tag{B.6.1.35}
$$

*for all $-1\le\sigma\le 2.$*

*For any real number $B>1$ and all sufficiently large $T$ (independently of $B$), the inequality*

$$
|L_{\Sigma_F-S}(\chi,\sigma+it)|>T^{-AB} \tag{B.6.1.36}
$$

*for all $-1\le\sigma\le 2$ holds for all $t\in[T,T+1]$ away from a subset of $[T,T+1]$ of measure $1/B$.*

## PDF page 642

**642** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

*Proof.* Pick $\sigma_0\ge 2$ and let $r=4\sqrt{1+(\sigma_0+1)^2}>4(\sigma_0+1)$. We fix an integer $N>\frac{[F:\mathbf Q]}{2}$ and choose $A_1>0$ with the following property: there exists $T_0>1$ such that:

$$
|L_{\Sigma_F-S}(\chi,s)|\le A_1|{\rm I\mathrm{m}}(s)|^N \tag{B.6.1.37}
$$

for all $s\in\mathbf C_{[\sigma_0-r,\sigma_0+r]}$ with $|{\rm I\mathrm{m}}(s)|>T_0$. That such $A_1>0$ exists is a consequence of boundedness of the entire function $\prod_{v\in S_f}L_v(\chi_v|\cdot|^s_v)^{-1}$, uniformly on the vertical strips of bounded width in $\mathbf C$, combined with Proposition B.1.1.3 which provides a real number $A_{0,N}>0$ such that:

$$
|L_f(s,\chi)|\le A_{0,N}|{\rm I\mathrm{m}}(s)|^N \tag{B.6.1.38}
$$

for all $s\in\mathbf C_{[\sigma_0-r,\sigma_0+r]}$ with $|{\rm I\mathrm{m}}(s)|>T_0$.

We fix $T\in\mathbf R$ such that $|T|>T_0$. By (B.6.1.37) and [T2, Ch. III, §3, Lemma $\alpha$, p. 56] applied to $f(s)=L_{\Sigma_F-S}(\chi,s)$ with $s_0=\sigma_0+iT$, $M=A_2\log(T)$, $r=4((\sigma_0+1)^2+1)^{1/2}$, with

$$
A_2:=\sup_{T\ge T_0+r}\left(N+\frac{1}{\log T}\log(A_1\zeta_F(\sigma_0))\right)
$$

(noting that $|1/L_{\Sigma_F-S}(\chi,\sigma_0+iT)|\le\zeta_F(\sigma_0)$), we obtain

$$
\left|\frac{L'_{\Sigma_F-S}(\chi,s)}{L_{\Sigma_F-S}(\chi,s)}-\sum_{\rho:|\rho-\sigma_0-iT|\le r/2}\frac{1}{s-\rho}\right|\le \frac{AA_2}{r}\log(T) \tag{B.6.1.39}
$$

where $A>0$ is provided by the cited Lemma in [T2] and the sum is indexed by the zeros of $L_{\Sigma_F-S}(\chi,s)$ (counted with multiplicity) within the disc $|s-s_0|\le r/2$. The application of [T2] uses that the disc $|s-s_0|\le r$ is contained inside $\mathbf C_{\ge\sigma_0-r}$.

Note that the box $[-1,\sigma_0]+i(T+[-1,1])$ is entirely contained within the disc $|s-s_0|\le r/4$. We now choose $T=t$ with $|t|>T_0+r$, and keep it fixed, and deduce

$$
\left|\frac{L'_{\Sigma_F-S}(\chi,\sigma+it)}{L_{\Sigma_F-S}(\chi,\sigma+it)}-\sum_{\rho:|\rho-\sigma_0-it|\le r/2}\frac{1}{\sigma+it-\rho}\right|\le \frac{AA_2}{r}\log(|t|) \tag{B.6.1.40}
$$

for all $\sigma\in[-1,\sigma_0]$. We further note that if $\rho=\beta+i\gamma$ is a zero of $L_{\Sigma_F-S}(\chi,s)$ satisfying $|\gamma-t|\le 1$ then since $0<\sigma_0-\beta\le\sigma_0$ we see that $\rho$ is contained within the disc $|s-\sigma_0-it|\le r/2$.

The zeros $\rho=\beta+i\gamma$ of $L_{\Sigma_F-S}(\chi,s)$ contained in the disc $|s-\sigma_0-it|\le r/2$ are either zeros of $\prod_{v\in S_f}L_v(\chi_v|\cdot|^s_v)^{-1}$ or of $L_f(s,\chi)$. In the former case, there is at most $\sum_{v\in S_f}\frac{r\log(q_v)}{2\pi}=O_{\sigma_0}(1)$ for $q_v:=N(\mathfrak p_v)$ for each $v\in S_f$ and $\mathfrak p_v\subset\mathcal O_F$ the unique prime ideal corresponding to the finite place $v$. In the latter case, there is at most $O(\log(|t|))$ such zeros of $L_f(s,\chi)$, by [Lang-b, Ch. XVII, §2, Prop. 2.4].

We denote by $[r]$ the highest nonnegative integer $x\le r$. For each zero $\rho$ of $L_{\Sigma_F-S}(\chi,s)$ satisfying $|\gamma-t|>1$ we have

$$
\left|\frac{1}{s-\rho}\right|=\frac{1}{(|\sigma-\beta|^2+|t-\gamma|^2)^{1/2}}\le 1 \tag{B.6.1.41}
$$

and so, up to replacing the implied constant $AA_2/r$ by a larger one, we obtain

$$
\frac{L'_{\Sigma_F-S}(\chi,\sigma+it)}{L_{\Sigma_F-S}(\chi,\sigma+it)}=\sum_{\rho:|\gamma-t|\le 1}\frac{1}{\sigma+it-\rho}+O(\log(|t|)) \tag{B.6.1.42}
$$

for $|t|>T_0$ and for all $\sigma\in[-1,\sigma_0]$. Since $\sigma_0\ge 2$, we obtain that (B.6.1.42) holds for all $|t|>T_0$ and all $\sigma\in[-1,2]$.

## PDF page 643

**B.7. RECIPROCALS AND PARTIAL EULER PRODUCTS ON THE 1-LINE** · **643**

We now integrate (B.6.1.42) across the horizontal segment from $2+it$ to $\sigma+it$ for $\sigma\in[-1,2]$ assuming $t$ is not the ordinate of a zero of $L_{\Sigma_F-S}(\chi,s)$. We obtain

$$
\log(L_{\Sigma_F-S}(\chi,\sigma+it))-\log(2+it) = \sum_{\rho:|\gamma-t|\le 1}(\log(\sigma+it-\rho)-\log(2+it-\rho)) + O(\log|t|) \tag{B.6.1.43}
$$

for all $|t|$ large enough and uniformly with respect to $\sigma\in[-1,2]$ (in the finite sum over zeros, we use the standard logarithm $\log(re^{i\theta}):=\log(r)+i\theta$ for $|\theta|<\pi$ on $\mathbf{C}-\mathbf{R}_{\le 0}\ni s-\rho$).

Since $\log(2+it)=O(\log|t|)$ and $\log(2+it-\rho)=O(1)$ for $|\gamma-t|\le 1$ with $O(\log|t|)$ such $\rho$'s, we obtain

$$
\log(L_{\Sigma_F-S}(\chi,s)) = \left(\sum_{\rho:|\gamma-t|\le 1}\log(s-\rho)\right) + O(\log|t|) \tag{B.6.1.44}
$$

for $s=\sigma+it$ with $|t|$ large enough that are not ordinates of a zero of $L_{\Sigma_F-S}(\chi,s)$ (only finitely many omissions for $t\in[a,b]$) and uniformly with respect to $\sigma\in[-1,2]$.

Upon taking real parts of both sides of (B.6.1.44), we proceed as in [T2, Ch. IX, §9.7, p. 219] and deduce that both (B.6.1.35) and (B.6.1.36) hold as asserted, for some real number $A>0$. $\square$

We deduce the following:

Corollary B.6.1.8 (Slow growth near the poles of $1/L_{\Sigma_F-S}(s,\chi)$ - II). *For each integer $m\ge 0$, there exist $A,\beta>0$ and a sequence of real numbers $\{T_k\}_{k\in\mathbf{Z}}$ such that $T_k\le T_{k+1}$, $\lim_{|k|\to+\infty}|T_k|=+\infty$, $T_k=O(|k|)$ such that*

$$
\sup_{s\in[-1,2]+iT_k}|\partial^m_s(1/L_{\Sigma_F-S}(s,\chi))|\le A|T_k|^{\beta} \tag{B.6.1.45}
$$

*for all $k\in\mathbf{Z}$.*

Proof. This is a consequence of Theorem B.6.1.7 (which handles $t\in[-T-1,-T]$ by passing to $\bar\chi$) using$^{29}$ boundedness on vertical strips (including the uniformly Schwartz property) for all derivatives of the completed $L$-functions of $\chi$ and exponential control on $\Gamma$-factors to apply the Phragmen-Lindelöf Theorem and the convexity bound on the derivatives $L^{(k)}_f(s,\chi)$. $\square$

**B.7. Reciprocals and Partial Euler products on the 1-line**

Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. In this section we will be establishing a precise estimate to the reciprocal partial Euler products for the finite Hecke $L$-function $L_f(s,\chi)$, on the vertical line $\mathrm{Re}(s)=1$.

B.7.1. The Dirichlet polynomials of $L'_f(s,\chi)/L_f(s,\chi)$ on the 1-line. Leading to the analysis of partial Euler products and their reciprocals, for $L_f(s,\chi)$, we need to study the Dirichlet polynomials of the Dirichlet series that sums to $L'_f(s,\chi)/L_f(s,\chi)$.

B.7.1.1. *Logarithmic derivatives of finite Hecke $L$-functions.* We consider the following Dirichlet series:

$$
\sum_{0\ne I\subset\mathcal{O}_F}\frac{\Lambda_{F,\chi}(I)}{N(I)^s} \tag{B.7.1.1}
$$

which for $\mathrm{Re}(s)>1$ converges absolutely to $-L'_f(\chi,s)/L_f(s,\chi)$. Recall that $\Lambda_{F,\chi}(I)=\chi(I)\Lambda_F(I)$, where $\Lambda_F$ is the von Mangoldt function for $F$ as defined in (B.6.1.13) (and $\chi(I)=0$ if $I$ is not coprime to the conductor of $\chi$). In particular, $\Lambda_{F,\chi}$ is nonzero only on prime powers $\mathfrak{p}^k$ with $k\ge 1$.

$^{29}$This should be spelled out in some more precision/detail.

## PDF page 644

**644** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

B.7.1.2. *A version of Perron's Formula from Titchmarsh.* We recall the following result from [T2, Ch. III]:

Lemma B.7.1.1. *Let $\{a_n\}_{n\ge 1}$ be a sequence of complex numbers such that:*

$$
f(s):=\sum_{n\ge 1}\frac{a_n}{n^s} \tag{B.7.1.2}
$$

*is absolutely convergent over $\mathbf{C}_{>1}$. Assume:*

(1) *$a_n=O(\psi(n))$ as $n\to+\infty$, where $\psi:\mathbf{N}\to\mathbf{R}_{>0}$ is a non-decreasing function,*

(2) *there exists $\alpha>0$ such that*

$$
\sum_{n\ge 1}\frac{|a_n|}{n^{\sigma}} = O_{\alpha}\left(\frac{1}{(\sigma-1)^{\alpha}}\right) \tag{B.7.1.3}
$$

*as $\sigma\to 1^+$, the implied constant depending on $\alpha$ and the $O$-constant in (1).*

*Let $c>0$ be a fixed real number and consider $s=\sigma+iT$ with $\sigma>1-c$. If $x\in\mathbf{R}_{>0}$ is not an integer and $N$ is the integer nearest to $x$, we have for $T\ge 1$:*

$$
\sum_{1\le n<x}\frac{a_n}{n^s} = \frac{1}{2\pi i}\int_{c-iT}^{c+iT}f(s+w)\frac{x^w}{w}\,\mathrm{d}w + O\left(\frac{x^c}{T(\sigma+c-1)^{\alpha}}\right) + O\left(\frac{\psi(2x)x^{1-\sigma}\log(x)}{T}\right) + O\left(\frac{\psi(N)x^{1-\sigma}}{T|x-N|}\right) \tag{B.7.1.4}
$$

*where the implied constants are independent of $x$, $\sigma$ and $T$ and only depend on $\alpha$ and the $O$-constant in (1).*

*If $x\in\mathbf{R}_{>0}$ is an integer, we have:*

$$
\sum_{1\le n\le x-1}\frac{a_n}{n^s}+\frac{a_x}{2x^s} = \frac{1}{2\pi i}\int_{c-iT}^{c+iT}f(s+w)\frac{x^w}{w}\,\mathrm{d}w + O\left(\frac{x^c}{T(\sigma+c-1)^{\alpha}}\right) + O\left(\frac{\psi(2x)x^{1-\sigma}\log(x)}{T}\right) + O\left(\frac{c\psi(x)x^{-\sigma}}{T}\right) \tag{B.7.1.5}
$$

*where the implied constants are independent of $x$, $\sigma$ and $T$ and only depend on $\alpha$ and the $O$-constant in (1).*

Lemma B.7.1.1 is [T2, Ch. III, Lemma 3.12]. It is a version of Perron's formula whose classical form is [T1, Ch. IX, §9.42]. It rests on the calculus of residues, and specifically on the calculation of $(2\pi i)^{-1}\int_{c-i\infty}^{c+i\infty}(x/m)^w\,\mathrm{d}w/w$ (as $\lim_{t\to+\infty}\int_{c-it}^{c+it}$) being $1$ if $m<x$, $0$ if $m>x$, and $1/2$ if $m=x$.

Proof of Lemma B.7.1.1. We know $f(s)=\sum_{m\ge 1}a_mm^{-s}$ has abscissa of absolute convergence $\sigma_a\le 1$. Let $\sigma$ and $c$ be real numbers, $c>0$, such that $\sigma+c>\sigma_a$, for $\sigma:=\mathrm{Re}(s)$. Let $T,x\ge 1$ be real numbers. If $x$ is not an integer then we have

$$
\sum_{1\le m<x}\frac{a_m}{m^s} = \frac{1}{2\pi i}\int_{c-iT}^{c+iT}f(s+w)\frac{x^w}{w}\,\mathrm{d}w + O\left(\frac{x^c}{T}\sum_{m\ge 1}\frac{|a_m|}{m^{\sigma+c}|\log(x/m)|}\right) \tag{B.7.1.6}
$$

where the $O$-constant is $1/\pi$.

The formula in (B.7.1.6) follows from [QQ, Ch. 4, Thm. 4.2.3], applied as follows. We choose the coefficients $a_m$ in loc. cit. to be $a_mm^{-s}$, in which case the abscissa of absolute convergence $\sigma_a$ in loc. cit. is $\sigma_a-\sigma$. The positive real number $\rho$ in loc. cit. is $c$, and the $s$-variable of integration is $w$ in (B.7.1.6). With these notational changes, (B.7.1.6) is [QQ, Ch. 4, (4.2.5)] up to recognizing the $O$-constant as $1/\pi$, which emerges from the method of proof.

If $m<x/2$ or $m>2x$, we have $|\log(x/m)|>A:=\log(2)>0$, so the parts of the sum $\sum_{m\ge 1}\frac{|a_m|}{m^{\sigma+c}|\log(x/m)|}$ indexed by these integers are $O(\sum_{m\ge 1}|a_m|m^{-\sigma-c})$, the implied constant being $1/\log(2)$. By (B.7.1.3), this is $O(1/(\sigma+c-1)^{\alpha})$, the implied constant depending on $\alpha$ and the $O$-constant in (1): this gives the first O-term in (B.7.1.4).

In the range $N<m\le 2x$, the relevant estimate is contained at the top of [T2, Ch. III, p. 62], and the implied constant can be taken to be an absolute constant times the implied constant in $a_n=O(\psi(n))$

## PDF page 645

**B.7. RECIPROCALS AND PARTIAL EULER PRODUCTS ON THE 1-LINE** · **645**

(ultimately because $\log(1+t)\ge t/2$ for $0<t\le 1$). This gives the second $O$-term in (B.7.1.4). For the same reason, the implied constant in the estimate

$$
\frac{|a_N|}{N^{\sigma+c}|\log(x/N)|} = O\left(\frac{\psi(N)x^{1-\sigma-c}}{|x-N|}\right)
$$

depends only on the one in assumption (1) on $a_N$.

The same reasoning applies to the range $x/2\le m<N$, by writing $m=N-r$ where $1\le r\le N-x/2$. We therefore have

$$
\log\left(\frac{x}{m}\right) \ge \log\left(\frac{N-1/2}{N-r}\right) = \log\left(1+\frac{r-1/2}{N-r}\right) \ge \frac12\left(\frac{r-1/2}{N-r}\right) \ge \frac12\,\frac{r}{N} \ge \frac13\,\frac{r}{x}.
$$

The part of the sum $\sum_{m\ge 1}\frac{|a_m|}{m^{\sigma+c}|\log(x/m)|}$ indexed by the integers $m$ in that range is therefore

$$
O\left(\frac{\psi(x)}{x^{-1+\sigma+c}}\sum_{1\le r\le N-x/2}\frac{1}{r}\right)
$$

where the implied constant is absolute, leading to another contribution to the error term $O\left(\frac{\psi(2x)x^{1-\sigma}\log(x)}{T}\right)$ in (B.7.1.4).

For $x$ not an integer, we deduce that all of the implied constants in (B.7.1.4) are as desired. Now assuming $x$ is an integer, as asserted in [T2, Ch. III, p. 62] the same method applies to the sum $\sum_{1\le n<x-1/2}a_nn^{-s}$, where $N=x-1$, since the line integral estimate

$$
\frac{a_x}{2\pi ix^s}\int_{c-iT}^{c+iT}\frac{\mathrm{d}w}{w} = \frac{a_x}{2\pi ix^s}\log\left(\frac{c+iT}{c-iT}\right) = \frac{a_x}{2\pi ix^s}\{\pi i+O(1/T)\} = \frac{a_x}{2x^s} + O\left(\frac{\psi(x)x^{-\sigma}}{T}\right) \tag{B.7.1.7}
$$

has implied constant in the second-to-last expression equal to $c/\pi$ and so in the final error term the implied constant is the one in hypothesis (1) times $c/\pi$. Combining (B.7.1.4) with (B.7.1.7) yields (B.7.1.5) by observing that

$$
O\left(\frac{\psi(N)(x-1/2)^{1-\sigma}}{T|x-1/2-N|}\right) = O\left(\frac{\psi(x-1)(x-1/2)^{1-\sigma}}{T|x-1/2-x+1|}\right) = O\left(\frac{\psi(x)x^{1-\sigma}}{T}\right) = O\left(\frac{\psi(2x)x^{1-\sigma}\log(x)}{T}\right)
$$

by the assumption on $\psi$ being non-decreasing, with all the implied constants depending only on $\alpha$ and the one in (1). $\square$

B.7.1.3. *Convergence and oscillation of the Dirichlet polynomials of $L'_f(s,\chi)/L_f(s,\chi)$.* By closely following the method in [T2, Ch.3,§3.14], we now prove the following:

Theorem B.7.1.2 (Convergence and oscillation on the 1-line). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Fix a compact subset $K\subset 1+i\mathbf{R}$.*

(1) *Assume $\chi|_{C^1_F}$ is trivial, so $\chi=|\cdot|^{-it_0}_F$ for some $t_0\in\mathbf{R}$. Assume $1+it_0\notin K$, pick $b>0$, and let $J_b\subset\mathbf{R}$ be the union of $\mathbf{Z}$ and the set of real numbers $x$ whose distance $d(x,\mathbf{Z})$ from $\mathbf{Z}$ is at least $b$.*

*For $s\in 1+i(\mathbf{R}-\{t_0\})$ and $x>1$ we have*

$$
\sum_{0\ne I\subset\mathcal{O}_F:N(I)\le x}\frac{\Lambda_{F,\chi}(I)}{N(I)^s} = -\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{x^{1+it_0-s}}{1+it_0-s} + f_x(s) \tag{B.7.1.8}
$$

*where $f_x(s)$ is an analytic function of $s\in 1+i\mathbf{R}$ such that $\lim_{x\to+\infty,x\in J_b}f_x(s)=0$ uniformly in such $s\in K$. Moreover, for $s=1+it_0$:*

$$
\sum_{0\ne I\subset\mathcal{O}_F:N(I)\le x}\frac{\Lambda_{F,\chi}(I)}{N(I)^{1+it_0}} = \log(x)+O(1). \tag{B.7.1.9}
$$

## PDF page 646

**646** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

(2) *Assume $\chi|_{C^1_F}$ is non-trivial. For $s\in 1+i\mathbf{R}$ we have that for $x>1$,*

$$
\sum_{0\ne I\subset\mathcal{O}_F:N(I)\le x}\frac{\Lambda_{F,\chi}(I)}{N(I)^s} = -\frac{L'_f(s,\chi)}{L_f(s,\chi)} + f_x(s) \tag{B.7.1.10}
$$

*where $f_x(s)$ is an analytic function of $s\in 1+i\mathbf{R}$ such that $\lim_{x\to+\infty,x\in J_b}f_x(s)=0$ uniformly in such $s\in K$.*

Proof. (1) : We take $a_n:=\sum_{I\subset\mathcal{O}_F:N(I)=n}\Lambda_{F,\chi}(I)$ in Lemma B.7.1.1, with $\alpha=1$ in (B.7.1.3). We therefore obtain by Lemma B.6.1.4 for $s\in 1+i(\mathbf{R}-\{t_0\})$ and $T\ge 1$ that

$$
\sum_{0\ne I\subset\mathcal{O}_F:N(I)\le x}\frac{\Lambda_{F,\chi}(I)}{N(I)^s} = -\frac{1}{2\pi i}\int_{c-iT}^{c+iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w + O\left(\frac{x^c}{Tc}\right) + O_F\left(\frac{\log(x)^2}{T}\right) + \begin{cases} O_F\left(\frac{\log x}{T\,d(x,\mathbf{Z})}\right), & x\notin\mathbf{Z} \\ O_F\left(\frac{c\log x}{Tx}\right), & x\in\mathbf{Z} \end{cases} \tag{B.7.1.11}
$$

because we can choose $\psi(x)\ll_F\log(x)$: the implied constants in (B.7.1.11) only depend on $\alpha$ and $\chi$ by Lemma B.7.1.1.

We now perform a contour-shift to $\int_{-\delta-iT}^{-\delta+iT}$ (with $\delta>0$ to be chosen) via the Residue Theorem for the integrand $-(\zeta'_F(s-it_0+w)/\zeta_F(s-it_0+w))(x^w/w)$ using the counterclockwise rectangle in Figure 4. We'll pick $\delta$ to ensure the rectangle is contained inside a classical zero-free region for $w\mapsto\zeta_F(s-it_0+w)$. Estimates for the integrals over the top, bottom, and left sides of the rectangle will then yield what we need.

$$
-\delta+iT \qquad c+iT
$$

$$
-\delta \qquad 0 \qquad c
$$

$$
-\delta-iT \qquad c-iT
$$

Figure 4. A rectangle oriented counterclockwise for shifting a vertical contour of integration

We have

$$
-\frac{1}{2\pi i}\int_{c-iT}^{c+iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w - \frac{1}{2\pi i}\int_{-\delta-iT}^{c-iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w
$$

$$
+ \frac{1}{2\pi i}\int_{-\delta-iT}^{-\delta+iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w + \frac{1}{2\pi i}\int_{-\delta+iT}^{c+iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w
$$

$$
= -\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{x^{1+it_0-s}}{1+it_0-s}
$$

where the final expression is the sum of the residues at the two poles of the integrand: the pole at $w=0$ with residue $-\zeta'_F(s-it_0)/\zeta_F(s-it_0)$ and the pole at $w=1+it_0-s$ (nonzero since $s\ne 1+it_0$) with residue $x^{1+it_0-s}/(1+it_0-s)$.

## PDF page 647

**B.7. RECIPROCALS AND PARTIAL EULER PRODUCTS ON THE 1-LINE** · **647**

Choose $C>0$ small enough so that

$$
\eta(t):=\frac{C}{\log(A_{F,\chi}(|t|+3))}
$$

satisfies $\eta(\mathbf{R}_{\ge 0})\subset(0,1/2]$ holds, and choose $\alpha\in(0,1)$. Then Proposition B.6.1.1 and Theorem B.6.1.3 give that $\zeta_F(s-it_0)$ has no zeros in the region $\sigma>1-\eta(|t-t_0|)$, and uniformly in the region $\sigma\ge 1-\alpha\eta(|t-t_0|)$ with $|t-t_0|\ge 1$ the logarithmic derivative of $\zeta_F$ satisfies

$$
\frac{\zeta'_F(\sigma+it-it_0)}{\zeta_F(\sigma+it-it_0)}\ll_{\alpha,F}(\log|t-t_0|)^2.
$$

We now take $T\ge 2+|t_0|+|t|$ and choose $\delta:=\alpha\eta(|T-t_0|)$, so $\delta$ has magnitude on the order of $1/\log|T-t_0|$. The contour in Figure 4 is contained in the classical zero-free region for $\zeta_F(s-it_0)$.

Let $A_F=A_{F,\alpha}$ be an upper bound on $|\zeta'_F/\zeta_F|$ over the compact overlap of the classical zero-free region $\sigma\ge 1-\alpha\eta(|t|)$ with the vertical strip $|t|\le 1$. Since $T\ge 2+|t_0|+|t|$, we have

$$
\left|\int_{-\delta-iT}^{-\delta+iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w\right| \le \int_{-1}^{1}A_F\frac{x^{-\delta}\,\mathrm{d}u}{\sqrt{\delta^2+u^2}} + \left(\int_{-T-t_0}^{-1}+\int_{1}^{T-t_0}\right)\frac{x^{-\delta}(\log(u+t))^2}{\sqrt{\delta^2+u^2}}\,\mathrm{d}u
$$

$$
\le (A_F+(\log(T+|t_0|+|t|))^2)x^{-\delta}\int_{-T-t_0}^{T-t_0}\frac{\mathrm{d}u}{\sqrt{\delta^2+u^2}}.
$$

where the final integral can be rewritten as $\int_{-(T+t_0)/\delta}^{(T-t_0)/\delta}\mathrm{d}v/\sqrt{1+v^2}$.

Since $\int \mathrm{d}v/\sqrt{1+v^2}=\log(v+\sqrt{1+v^2})=\log|v|+O(1)$ (implicit constant at most $\log(1+\sqrt{2})$), we get the upper bound

$$
(A_F+(\log(T+|t|+|t_0|))^2)x^{-\delta}\cdot 2(\log(T+|t_0|)+B) = O_{F,\alpha}((\log(T+|t|+|t_0|))^3x^{-\delta})
$$

(using that $T+|t_0|\ge 2+2|t_0|\ge 2$). To summarize, we have an estimate for integrating along the left side of the contour in Figure 4:

$$
\int_{-\delta-iT}^{-\delta+iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w\ll_{\alpha,F}x^{-\delta}(\log(T+|t|+|t_0|))^3 \tag{B.7.1.12}
$$

for $x\ge 1$.

Along the top and bottom sides of the rectangle we have the estimates

$$
\int_{-\delta+iT}^{c+iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w\ll_{\alpha}\frac{(\log|T+t-t_0|)^2}{T}\int_{-\delta}^{c}x^u\,\mathrm{d}u = O_{\alpha,F}\left(\frac{x^c(\log|T+t-t_0|)^2}{T\log(x)}\right) \tag{B.7.1.13}
$$

for $x>1$, and:

$$
\int_{-\delta-iT}^{c-iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w\ll_{\alpha}\frac{(\log|T+t-t_0|)^2}{T}\int_{-\delta}^{c}x^u\,\mathrm{d}u = O_{\alpha,F}\left(\frac{x^c(\log|T+t-t_0|)^2}{\log(x)T}\right). \tag{B.7.1.14}
$$

We define

$$
f_x(s):=\sum_{0\ne I\subset\mathcal{O}_F:N(I)\le x}\frac{\Lambda_{F,\chi}(I)}{N(I)^s} + \frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} - \frac{x^{1+it_0-s}}{1+it_0-s} \tag{B.7.1.15}
$$

## PDF page 648

**648** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

for $s\in 1+i(\mathbf{R}-\{t_0\})$. As a function of $s$, $f_x(s)$ is analytic and it has a removable singularity at $s=1+it_0$. The Residue Theorem calculation and (B.7.1.11) show

$$
f_x(s) = \frac{1}{2\pi i}\left(\int_{-\delta-iT}^{c-iT} - \int_{-\delta-iT}^{-\delta+iT} - \int_{-\delta+iT}^{c+iT}\frac{\zeta'_F(s-it_0+w)}{\zeta_F(s-it_0+w)}\frac{x^w}{w}\,\mathrm{d}w\right) + O\left(\frac{x^c}{Tc}\right) + O_F\left(\frac{(\log x)^2}{T}\right)
$$

$$
+ \begin{cases} O_F\left(\frac{\log x}{T|x-N|}\right), & x\notin\mathbf{Z} \\ O_F\left(\frac{c\log x}{Tx}\right), & x\in\mathbf{Z}. \end{cases}
$$

Now choose $c=1/\log(x)$ and $T=(\log(x))^3$, so

$$
\delta = \frac{\alpha C}{B+\log(T-t_0+3)}
$$

for some constants $B,C>0$. Plugging these into (B.7.1.11), (B.7.1.13), and (B.7.1.14), (compare with [T2, Ch. III, §3.13, p. 63]), we claim $f_x(s)\to 0$ as $x\to+\infty$ with $x$ varying through $J_b$ and $s=1+it$ for $t$ in an arbitrary but fixed compact subset of $\mathbf{R}-\{t_0\}$. This requires some additional work for the decay of the upper bound in (B.7.1.14) as $x\to+\infty$. That bound is

$$
O_{F,t_0,K}((\log T)^3x^{-\delta}) = O_{F,t_0,K}\left(\frac{(\log(\log x))^3}{x^{M/\log(T)}}\right) = O_{F,t_0,K}\left(\frac{(\log(\log x))^3}{x^{M'/\log(\log x)}}\right)
$$

for constants $M$ and $M'$ depending on $t_0$ and $\alpha$. Thus, we just need to verify $\log(\log x)/x^{A/\log(\log x)}\to 0$ as $x\to+\infty$ for any $A>0$. For $y=\log(x)\to+\infty$, this is

$$
\frac{logy}{e^{Ay/\log(y)}} \le \frac{\log(y)}{e^{Ay^{1-\varepsilon}}} \to 0
$$

for any $\varepsilon>0$. This gives the desired decay on $f_x(s)$.

We may write

$$
\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} - \frac{x^{1+it_0-s}}{1+it_0-s} = \frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} - \frac{1}{1+it_0-s} + \frac{1}{1+it_0-s} - \frac{x^{1+it_0-s}}{1+it_0-s} \tag{B.7.1.16}
$$

and observe that both functions

$$
\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} - \frac{1}{1+it_0-s},\quad \frac{1}{1+it_0-s} - \frac{x^{1+it_0-s}}{1+it_0-s}
$$

extend by continuity across the singularity $s=1+it_0$ to analytic functions over $1+i\mathbf{R}$. Upon letting $s$ tend to $1+it_0$ in (B.7.1.8) we obtain$^{30}$ (B.7.1.9) using L'Hopital's rule. The implied constant in (B.7.1.9) is absolute and amounts to the sum of $\|f_x(s)\|_u$ from (B.7.1.8) and the limit as $s\to 1+it_0$ over $1+i\mathbf{R}$ of the leftmost function in (B.7.1.16).

(2) : The same method, resting on Proposition B.6.1.1, gives (B.7.1.10) upon observing that the integrand

$$
\frac{L'_f(s+w\chi)}{L_f(s+w,\chi)}\frac{x^w}{w} \tag{B.7.1.17}
$$

as a function of $w$ has only one pole, at $w=0$, whose residue is $L'_f(s,\chi)/L_f(s,\chi)$ (in particular, no pole $w=1-s$ when $s\ne 1$). $\square$

B.7.2. Euler products on the 1-line. In this section, we analyze the Euler product for the finite Hecke $L$-function $L_f(s,\chi)$, on the 1-line, i.e. the vertical line $\{\mathrm{Re}(s)=1\}$.

$^{30}$Maybe something needs to be said about this process escaping from any choice of compact $K$ in (1)?

## PDF page 649

**B.7. RECIPROCALS AND PARTIAL EULER PRODUCTS ON THE 1-LINE** · **649**

B.7.2.1. *Mode of convergence of partial Euler products on subsets of the 1-line.* Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. In this subsection we analyze the mode of convergence of reciprocal partial Euler products of the finite Hecke $L$-function $L(s,\chi)$ on the line $\sigma=1$ in $\mathbf{C}$.

Theorem B.7.2.1 (Euler products on the 1-line - I). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_{\chi}$ be the finite set of finite places at which $\chi$ is ramified.*

(1) *If $\chi|_{C^1_F}$ is trivial (so $\chi=|\cdot|^{-it_0}_F$ for a unique real number $t_0$) then for every compact $K\subset\mathbf{R}-\{t_0\}$ and $s\in 1+iK$ and $M$ the smallest integer $\ge x$, for every $\varepsilon>0$ there exists a real number $x_0>1$ (depending on $K$ and $\varepsilon$) such that for all $x\ge x_0$ with $d(x,\mathbf{Z})\ge b>0$ we have on $1+iK$ that:*

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p}^m)\ge x}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} = -\frac{g_{M-1}(s)}{\log(M-1)} \tag{B.7.2.1}
$$

$$
+ F_x(s) - \sum_{n\ge x}g_{n-1}(s)\left(\frac{1}{\log(n)}-\frac{1}{\log(n-1)}\right).
$$

*where the series in the left (defined in Remark B.7.2.2 below) converges uniformly on $1+iK$, the functions $g_n(s)$ for $n\ge x$ are defined as*

$$
g_n(s):=-\frac{1-n^{1+it_0-s}}{1+it_0-s}, \tag{B.7.2.2}
$$

*and the function $F_x(s)$ is continuous over $1+iK$ and satisfies $\|F_x|_{1+iK,u}|\le 2\varepsilon/\log(x)$ for $x\ge x_0$.*

(2) *Fix a compact subset $K\subset\mathbf{R}$. If $\chi|_{C^1_F}$ is non-trivial then for every $s\in iK$ and $M$ the smallest integer $\ge x$, for every $\varepsilon>0$ there exists a real number $x_0>1$ (depending on $K$ and $\varepsilon$) such that for all $s\in 1+iK$ and $x\ge x_0$ we have:*

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p}^m)\ge x}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} = F_x(s) \tag{B.7.2.3}
$$

*where the series in the left (defined in Remark B.7.2.2 below) converges uniformly over $1+iK$ and the function $F_x(s)$ is continuous over $1+iK$ with $\|F_x\|_{1+iK,u}<2\varepsilon/\log(x)$ for all $x\ge x_0$.*

Remark B.7.2.2. In (B.7.2.1) and (B.7.2.3), the sum over $\mathfrak{p}$'s on the left side means by definition

$$
\sum_{n\ge x}\left(\sum_{N(\mathfrak{p}^m)=n}\frac{\chi(\mathfrak{p}^m)}{m}\right)\frac{1}{n^s}.
$$

Proof. We set $b_n:=\sum_{0\ne I\subset\mathcal{O}_F:N(I)=n}\chi(I)\Lambda_F(I)/n^s$, and $a_n:=1/\log(n)$ for $n>1$, and $a_0=a_1:=0$. Upon defining

$$
B_x:=\sum_{0\le k\le x}b_k,
$$

for any real number $X>0$ and $N:=\lfloor X\rfloor$ the largest integer satisfying $\le X$, partial summation gives

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p}^m)\le X}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} = \sum_{\mathfrak{p}:N(\mathfrak{p}^m)\le X}\frac{\chi(\mathfrak{p}^m)\log N\mathfrak{p}}{N(\mathfrak{p}^m)^s\log(N(\mathfrak{p}^m))} = \sum_{0\le n\le X}a_nb_n \tag{B.7.2.4}
$$

$$
= a_NB_N - \sum_{0\le n\le N-1}B_n(a_{n+1}-a_n). \tag{B.7.2.5}
$$

## PDF page 650

**650** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

In particular, applying this to $X=M-1$ for $M=\lceil x\rceil$ the smallest integer $\ge x$ and subtracting it from (B.7.2.4) yields

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:x\le N(\mathfrak{p}^m)\le X}\sum_{m\ge 1}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} = \sum_{M\le n\le N}a_nb_n \tag{B.7.2.6}
$$

$$
= a_NB_N-a_{M-1}B_{M-1}-\sum_{x\le n\le X}B_{n-1}(a_n-a_{n-1}). \tag{B.7.2.7}
$$

(1) : From Theorem B.7.1.2, for every real number $\varepsilon>0$, there exists a large enough real number $x_0>1$ such that for every $x>x_0$ we have from (B.7.1.8) that

$$
B_x = \sum_{0\ne I\subset\mathcal{O}_F:N(I)\le x}\frac{\Lambda_{F,\chi}(I)}{N(I)^s} = -\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{x^{1+it_0-s}}{1+it_0-s} + f_x(s) \tag{B.7.2.8}
$$

where $f_x(s)$ is an analytic function over $1+i\mathbf{R}$ satisfying $\|f_x\|_{1+iK,u}\le\varepsilon$ when $d(x,\mathbf{Z})\ge b>0$ or $x\in\mathbf{Z}$.

The real number $x_0$ depends only on $\varepsilon$ and $K$ and on a choice of $\alpha\in(0,1)$ made at the beginning as per the proof of Theorem B.7.1.2(1), but not on $s\in 1+i\mathbf{R}$. We deduce that for every $X>x>x_0$ and $N=\lfloor X\rfloor$, $M=\lceil x\rceil\ge 2$, by (B.7.2.6):

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:x\le N(\mathfrak{p}^m)\le X}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} = \frac{1}{\log(N)}\left\{-\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{N^{1+it_0-s}}{1+it_0-s} + f_N(s)\right\} \tag{B.7.2.9}
$$

$$
- \frac{1}{\log(M-1)}\left\{-\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{(M-1)^{1+it_0-s}}{1+it_0-s} + f_{M-1}(s)\right\}
$$

$$
- \sum_{x\le n\le X}\left\{-\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{(n-1)^{1+it_0-s}}{1+it_0-s} + f_{n-1}(s)\right\}\left(\frac{1}{\log(n)}-\frac{1}{\log(n-1)}\right).
$$

For every integer $m\ge x_0$, each of the analytic functions over $1+i(\mathbf{R}-\{t_0\})$:

$$
H_m(s):=\frac{1}{\log(m)}\left\{-\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{m^{1+it_0-s}}{1+it_0-s} + f_m(s)\right\} \tag{B.7.2.10}
$$

extends to an analytic function over $1+i\mathbf{R}$, since we may write

$$
H_m(s)=\frac{1}{\log(m)}\{h(s)+g_m(s)+f_m(s)\} \tag{B.7.2.11}
$$

where

$$
h(s):=-\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{1}{1+it_0-s},\quad g_m(s):=-\frac{1-m^{1+it_0-s}}{1+it_0-s} \tag{B.7.2.12}
$$

and $h$ extends to an analytic function across the removable singularity at $s=1+it_0$, as does the function $g_m$, and $f_m(s)$ is analytic over $1+i\mathbf{R}$ as per Theorem B.7.1.2.

As $N\to+\infty$, $f_N(s)\to 0$ uniformly over $1+iK$, and $(1/\log(N))h\to 0$ uniformly on the compact subsets of $1+i\mathbf{R}$. The function $(1/\log(N))g_N$ tends to zero uniformly on $1+iK$ as $N\to+\infty$ since it even tends to zero uniformly on all subsets of the form $1+i((-\infty,t_0-A]\cup[t_0+A,+\infty))$ for every real number $A>0$. (At $s=1+it_0$, it is exactly $-1$.)

We now analyze the sum

$$
\sum_{x\le n\le X}\left\{-\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{(n-1)^{1+it_0-s}}{1+it_0-s} + f_{n-1}(s)\right\}\left(\frac{1}{\log(n)}-\frac{1}{\log(n-1)}\right)
$$

## PDF page 651

**B.7. RECIPROCALS AND PARTIAL EULER PRODUCTS ON THE 1-LINE** · **651**

as $X\to+\infty$. We write

$$
\sum_{x\le n\le X}\left\{-\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)} + \frac{(n-1)^{1+it_0-s}}{1+it_0-s} + f_{n-1}(s)\right\}\left(\frac{1}{\log(n)}-\frac{1}{\log(n-1)}\right) \tag{B.7.2.13}
$$

$$
= h(s)\left(\frac{1}{\log(N)}-\frac{1}{\log(M-1)}\right) + \sum_{x\le n\le X}g_{n-1}(s)\left(\frac{1}{\log(n)}-\frac{1}{\log(n-1)}\right)
$$

$$
+ \sum_{x\le n\le X}f_{n-1}(s)\left(\frac{1}{\log(n)}-\frac{1}{\log(n-1)}\right).
$$

For $x\ge x_0+1$, we have $\|f_n(s)\|_u\le\varepsilon$ for $s\in 1+i\mathbf{R}$ for all $n\ge x$, and so the series $\sum_{n\ge x}f_{n-1}(s)(1/\log(n)-1/\log(n-1))$ is absolutely and uniformly convergent to a bounded analytic function $F_x(s)$ over $1+i\mathbf{R}$ such that $F_x(s)\to 0$ as $x\to+\infty$, uniformly over $1+i\mathbf{R}$. Indeed, we have $|F_x(s)|\le\varepsilon/\log(x)$ for every $s\in 1+i\mathbf{R}$.

As $N\to+\infty$, the functions $(1/\log(N)-1/\log(M-1))h(s)$ tend to $-h(s)/\log(M-1)$ uniformly on $1+iK$. Since the $|g_n|$'s are uniformly bounded on $1+iK$ for $n\ge x$, the series $\sum_{n\ge x}g_{n-1}(s)(1/\log(n)-1/\log(n-1))$ also converges uniformly over $1+iK$.

We may therefore send $X\to+\infty$ in (B.7.2.13) and deduce from (B.7.2.9) the following identity on $1+iK$:

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p}^m)\ge x}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} = -\frac{1}{\log(M-1)}\left\{-\frac{\zeta'_F(s-it_0)}{\zeta_F(s-it_0)}+\frac{(M-1)^{1+it_0-s}}{1+it_0-s}+f_{M-1}(s)\right\} \tag{B.7.2.14}
$$

$$
+\frac{h(s)}{\log(M-1)} - F_x(s) - \sum_{n\ge x}g_{n-1}(s)\left(\frac{1}{\log(n)}-\frac{1}{\log(n-1)}\right)
$$

where the left side is defined in Remark B.7.2.2. Upon renaming $-f_{M-1}(s)/\log(M-1)-F_x(s)$ as $F_x(s)$, and noting that $|f_{M-1}(s)/\log(M-1)|\le\varepsilon/\log(x)$ for $s\in 1+iK$ and $M:=\lceil x\rceil$ big enough, we see that part (1) is established.

(2) : The same method as in the proof of (1) gives (B.7.2.3) upon applying Theorem B.7.1.2(2) in place of Theorem B.7.1.2(1), and upon renaming $-f_{M-1}(s)/\log(M-1)-F_x(s)$ as $F_x(s)$. $\square$

*B.7.2.2. Uniform convergence away from the singularity.*

Corollary B.7.2.3 (Uniform convergence away from the singularity - I). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_{\chi}$ be the finite set of finite places at which $\chi$ is ramified. As $x\to\infty$, the functions*

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p})<x}\frac{\chi(\mathfrak{p})}{N(\mathfrak{p})^s} \tag{B.7.2.15}
$$

*of $s$ converge locally uniformly over $1+i\mathbf{R}$ if $\chi|_{C^1_F}$ is non-trivial, and locally uniformly over $1+i(\mathbf{R}-\{t_0\})$ if $\chi=|\cdot|^{-it_0}_F$ for $t_0\in\mathbf{R}$ (the case $\chi|_{C^1_F}=1$).*

Proof. We may write, for every real number $X>1$:

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p})<X}\frac{\chi(\mathfrak{p})}{N(\mathfrak{p})^s} = \sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p}^m)<X}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} - \sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p}^m)<X}\sum_{m\ge 2}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} \tag{B.7.2.16}
$$

where, as $X\to+\infty$, the partial sums

$$
\sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p}^m)<X}\sum_{m\ge 2}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}}
$$

converge absolutely and uniformly over $1+i\mathbf{R}$.

## PDF page 652

**652** · **CHAPTER B. PREPARATIONS FROM ANALYTIC NUMBER THEORY**

From (B.7.2.16) and Theorem B.7.2.1, we deduce that the partial sums in (B.7.2.15) converge in the desired manner because for $x<X$ we have

$$
G_X(s)-G_x(s) = \sum_{N(\mathfrak{p}^m)\ge x}\frac{\chi(\mathfrak{p})}{N(\mathfrak{p})^s} - \sum_{N(\mathfrak{p}^m)\ge X}\frac{\chi(\mathfrak{p})}{N(\mathfrak{p})^s}
$$

with each sum defined as in Remark B.7.2.2. $\square$

B.7.2.3. *Partial Euler products on the 1-line.* Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_{\chi}$ be the finite set of finite places of $F$ at which $\chi$ is ramified. Let $x>1$ be an integer. We define

$$
E_{f,x}(s,\chi):=\prod_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p})<x}(1-\chi(\mathfrak{p})N(\mathfrak{p})^{-s}). \tag{B.7.2.17}
$$

Theorem B.7.2.4 (Euler products on the 1-line - II). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_{\chi}$ be the finite set of finite places at which $\chi$ is ramified.*

(1) *If $\chi|_{C^1_F}$ is trivial, so $\chi=|\cdot|^{-it_0}_F$ for a unique real number $t_0$, for a compact subset $K\subset\mathbf{R}-\{t_0\}$ and every $\varepsilon>0$ there exists $x_0>1$ and for every $x\ge x_0$ a bounded continuous function $F_x$ on $K$ satisfying $\|F_x\|_u\le 2\varepsilon/\log(x)$, such that*

$$
E_{f,x}(1+it,\chi)L_f(1+it,\chi) = \exp(F_x(t)+G_x(t)+H_x(1+it)) \tag{B.7.2.18}
$$

*for every $t\in K$, where $G_x(t)$ is the analytic function over $\mathbf{R}-\{t_0\}$ defined as*

$$
G_x(t):=\frac{1-(M-1)^{i(t_0-t)}}{i\log(M-1)(t-t_0)} + \sum_{n\ge x}\frac{1-(n-1)^{i(t_0-t)}}{i(t_0-t)}\left(\frac{1}{\log(n)}-\frac{1}{\log(n-1)}\right) = O_K\left(\frac{1}{\log(x)}\right) \tag{B.7.2.19}
$$

*with $M\ge 2$ the least integer $\ge x$, the series in (B.7.2.19) converging uniformly on $K$, and*

$$
H_x(s):=-\sum_{N\mathfrak{p}<x,N(\mathfrak{p}^m)\ge x}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p}^m)^s} = O\left(\sum_{m\ge 2,N(\mathfrak{p}^m)\ge x}\frac{1}{mN(\mathfrak{p}^m)^s}\right)
$$

*bounded by the tail of the Dirichlet series $\sum_{m\ge 2,\mathfrak{p}}1/(mN(\mathfrak{p}^m)^s)$ that is absolutely convergent on $\{\sigma>1/2\}$ (so $H_x(1+it)\to 0$ uniformly on $\mathbf{R}$ as $x\to\infty$).*

*In particular, we have*

$$
\lim_{x\to+\infty}E_{f,x}(s,\chi)L_f(s,\chi) = 1 \tag{B.7.2.20}
$$

*uniformly over $1+iK$.*

(2) *If $\chi|_{C^1_F}$ is non-trivial, for any compact subset $K\subset\mathbf{R}$ and $\varepsilon>0$ there exists $x_0>1$ and for every $x\ge x_0$ a bounded continuous function $F_x$ on $K$ satisfying $\|F_x\|_u\le 2\varepsilon/\log(x)$ such that*

$$
E_{f,x}(1+it,\chi)L_f(1+it,\chi) = \exp(F_x(t)-H_x(1+it)) \tag{B.7.2.21}
$$

*for every $t\in K$. In particular, we have*

$$
\lim_{x\to+\infty}E_{f,x}(s,\chi)L_f(s,\chi) = 1 \tag{B.7.2.22}
$$

*uniformly over $1+iK$.*

Proof. Over $\mathbf{C}_{>0}$,

$$
\log(1-\chi(\mathfrak{p})N(\mathfrak{p})^{-s})^{-1} = \sum_{m\ge 1}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}}
$$

## PDF page 653

**B.7. RECIPROCALS AND PARTIAL EULER PRODUCTS ON THE 1-LINE** · **653**

where the series is absolutely convergent. We will use Theorem B.7.2.1 to deduce

$$
\log(E_{f,x}(s,\chi)L_f(s,\chi)) = \sum_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p})\ge x}\sum_{m\ge 1}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} = \sum_{N(\mathfrak{p}^m)\ge x}\frac{\chi(\mathfrak{p}^m)}{mN(\mathfrak{p})^{ms}} - H_x(1+it) \tag{B.7.2.23}
$$

as functions over $1+i(\mathbf{R}-\{t_0\})$ when $\chi=|\cdot|^{-it_0}_F$ and over $1+i\mathbf{R}$ if $\chi|_{C^1_F}$ is non-trivial.

The identity in (B.7.2.23) holds over the half-plane $\mathbf{C}_{>1}$ of absolute convergence of the Dirichlet series in the right side of (B.7.2.23), and by Theorem B.7.2.1 the right side converges as a Dirichlet series on $\sigma=1$ (away from $1+it_0$ in part (1)). Thus, by Abel's Theorem for Dirichlet series and continuity of the left side of (B.7.2.23) on $\sigma\ge 1$ we see (B.7.2.23) holds pointwise on the region $\sigma\ge 1$. $\square$

*B.7.2.4. Convergence of partial Euler products on the 1-line away from the singularity.*

Corollary B.7.2.5 (Convergence of partial Euler products on the 1-line). *Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character. Let $S_{\chi}$ be the finite set of finite places at which $\chi$ is ramified.*

*The partial Euler product*

$$
\prod_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p})<x}(1-\chi(\mathfrak{p})N(\mathfrak{p})^{-s})^{-1} \tag{B.7.2.24}
$$

*converges to $L_f(s,\chi)$ locally uniformly over $1+i\mathbf{R}$ if $\chi|_{C^1_F}\ne 1$, and locally uniformly over $1+i(\mathbf{R}-\{t_0\})$ if $\chi=|\cdot|^{-it_0}_F$ for $t_0\in\mathbf{R}$ (the case $\chi|_{C^1_F}=1$).*

Proof. Indeed, the partial Euler product in (B.7.2.24) is the reciprocal of $E_{f,x}(s,\chi)$ from (B.7.2.17), and hence $E_x\to 1/L_f$ locally uniformly by Theorem B.7.2.4 because $L_f(s,\chi)$ is non-vanishing on $\sigma=1$. Reciprocating then gives the result. $\square$

Remark B.7.2.6. Let $F$ be a number field, $\chi\in\widehat{C_F}$ a continuous character of the form $|\cdot|^{-it_0}_F$ for $t_0\in\mathbf{R}$. We have

$$
\prod_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p})<x}(1-\chi(\mathfrak{p})N(\mathfrak{p})^{-1-it_0}) = \prod_{\mathfrak{p}\subset\mathcal{O}_F:N(\mathfrak{p})<x}\left(1-\frac{1}{N(\mathfrak{p})}\right) = \frac{e^{-\gamma}}{\bar\mu_1(C^1_F)\log(x)}(1+o_x(1)) \tag{B.7.2.25}
$$

as $x\to+\infty$. This is Mertens' Theorem for the number field $F$.

The estimate in (B.7.2.25) follows from (B.7.1.9) of Theorem B.7.1.2. The argument to deduce (B.7.2.25) from (B.7.1.9) is the same as in the proof of [HW, p. 351, Thm. 429]; see also [GL, Thm. 1,(C1)].

Remark B.7.2.7. For $\chi\in\widehat{C_F}$ of the form $\chi=|\cdot|^{-it_0}_F$ for $t_0\in\mathbf{R}$, the reciprocal partial Euler products $E_{f,x}(s,\chi)$ converge to $1/L_f(s,\chi)$ pointwise over $1+i\mathbf{R}$, and locally uniformly on $1+i(\mathbf{R}-\{t_0\})$.

The convergence over any interval containing $t_0$ in its interior is not uniform. Indeed, the partial products indexed by the integers $x\le n\le N$ contributing in the limit to $e^{-G_x(t)}$ oscillate too much and can only be kept bounded by a uniform constant when $t$ is kept within $(t_0-A,t_0+A)$ as $A$ decreases towards zero at least as fast as $1/\log(N)$.

## PDF page 654
