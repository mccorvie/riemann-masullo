## PDF page 381

**CHAPTER 8**

**Periodic Orbits and Fixed Points**

8.1. On Orbital Supports - I 381

8.2. Stack-theoretic Periodic Orbits and Fixed Points 384

8.3. On Orbital Supports - II 387

8.4. Orbital Traces 389

8.5. The big picture 394

Let $F$ be a number field.

In this section we collect the main results of this Chapter and explain them through the lens of Theorem 7.1.2.3, which was the starting point of the Chapter itself. We also compute the support of the distributions that comprise the dual Schauder bases of the absolute bases that we found on the subquotients $\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})$.

The supports will be loci within the $S$-adeles, for any finite set of places of $F$ containing all the Archimedean places, and they will be stable under the continuous left-translation action by $\mathcal{O}_{F,S}^{\times}$ and $\mathrm{GL}_1(\mathbf{A}_{F,S})^1$.

Since such distributional basis elements are obtained from an eigendistribution through derivation of uniformly bounded above order, their supports only enter through their topological quotient stacks, which we compute explicitly: they are either fat points (equipped with a canonical concept of multiplicity, much like the closed point of a formal unit disc over a discrete field) or periodic orbits: quotient stacks whose coarse space is a loop with a natural length inherited form the Haar measure on the $S$-ideles, of $\log N(\mathfrak{p}_v)|$ for each finite place $v \in S$.

This shows how exactly predictions of Deninger turn out to feature and play a role within this work.

**8.1. On Orbital Supports - I**

The following Theorem uses Theorem 7.5.0.1 as an input, and it should be thought of as a refinement of Theorem 7.3.1.6: it informs us on the existence of absolute Schauder bases on the $p$-primary Orbital Subquotients

$$
\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}}),\ \mathscr{E}_{S,S_\infty}(\chi|_{J^1_{F,S}})
$$

defined in (7.3.1.5) and (7.3.4.6) that lift to elements of $\mathcal{S}(\mathbf{A}_{F,S})$ supported over certain specific loci within the $S$-adeles.

This enables us to compute the support of the tempered distributions on $\mathbf{A}_{F,S}$ that are the images of the dual basis elements in $\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})'_{\beta}$.

The computation of their supports will lead to the finding of the periodic orbits and fixed points whose existence and role was alluded to in the previous subsection, and will enable us to “organize” the nuclear Fréchet spaces by rethinking them as Fréchet bundles on a certain topological quotient stack to be defined below, each of whose subquotients are supported each on a stack-theoretic periodic orbit, respectively on a stack-theoretic fixed point.

**381**

## PDF page 382

**382** · **CHAPTER 8. PERIODIC ORBITS AND FIXED POINTS**

We will conclude this Chapter by explaining the geometric meaning of the Paley-Wiener Levels, and of Theorem 7.3.3.4, which asserts that in the (sole) case of the subquotients:

$$
\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}})
$$

i.e. only for $p$ a finite prime, and not for the Archimedean places, the absolute Orbital Schauder Bases and their dual bases are inherited by the corresponding subquotients and their strong duals of the Paley-Wiener Levels:

$$
\mathscr{E}^{\mathrm{ABS}}_{S',S_p,X}(\chi|_{J^1_{F,S'}}),\ \widetilde{\mathscr{E}}_{S',S_p,Y}(\chi|_{J^1_{F,S'}})
$$

from (7.3.3.5) and (7.3.3.6).

**Theorem 8.1.0.1 (On Orbital Supports - I).** *Let $F$ be a number field, $\chi \in \widehat{C_F}$ a continuous character. Let $S$ be a finite set of places of $F$ containing all the Archimedean places. Assume $\chi$ is unramified outside $S$, and $\mathrm{Pic}(\mathcal{O}_{F,S}) = 1$.*

(1) *Let $p$ be a prime number such that $S_p \subset S$. The canonical continuous linear map:*

(8.1.0.1)

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_p(\mathbf{A}_{F,S}))/\mathrm{PV}_{S,S_p}\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_p(\mathbf{A}_F)) \to \mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))/\mathrm{PV}_{S,S_p}\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))
$$

*where $\mathcal{S}_p(\mathbf{A}_{F,S}) \subset \mathcal{S}(\mathbf{A}_{F,S})$ is the closed subspace:*

(8.1.0.2)

$$
\mathcal{S}_p(\mathbf{A}_{F,S}) := \mathcal{S}_{00}(\mathbf{A}_{F,S_\infty}) \otimes_{\pi} \bigotimes_{v \in S_f - S_p} \mathcal{S}(F_v^{\times}) \otimes_{\pi} \bigotimes_{v \in S_p} \mathcal{S}(F_v)
$$

*is a linear topological isomorphism.*

(2) *Let $v \in S$ be a finite place. The canonical continuous linear map:*

(8.1.0.3)

$$
\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_v(\mathbf{A}_{F,S}))/\mathrm{PV}_v\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_p(\mathbf{A}_{F,S})) \to \mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))/\mathrm{PV}_v\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))
$$

*where $\mathcal{S}_v(\mathbf{A}_{F,S}) \subset \mathcal{S}(\mathbf{A}_{F,S})$ is the closed subspace:*

(8.1.0.4)

$$
\mathcal{S}_v(\mathbf{A}_{F,S}) := \mathcal{S}_{00}(\mathbf{A}_{F,S_\infty}) \otimes_{\pi} \mathcal{S}(F_v) \otimes_{\pi} \bigotimes_{w \in S_f - \{v\}} \mathcal{S}(F_w^{\times})
$$

*is a linear topological isomorphism.*

Proof. We choose a continuous homomorphic section $\tau$ to the idelic norm, with image contained within $\mathrm{GL}_1(\mathbf{A}_{F,S}) \times \{1\} \subset \mathrm{GL}_1(\mathbf{A}_F)$.

(1) : Under the stated assumptions on $\overline{\pi}_S$, by Theorem 6.2.1.1(2):

$$
\overline{\pi}_S : \mathrm{H}_{0,\mathrm{cont}}(\chi|_{J^1_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S})) \to \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^1_F}, \mathcal{S}(\mathbf{A}_F))
$$

is a linear topological isomorphism. By Theorem 5.4.1.1, we deduce that $L_S$ from (5.1.1.2) induces a linear topological embedding:

(8.1.0.5)

$$
U_S : \mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf{A}_{F,S})) \to A\mathcal{S}(\mathbf{C}_{>0}) \times A\mathcal{S}(\mathbf{C}_{>0})
$$

where, upon defining:

$$
\Lambda(s,\chi) := ((s+ix_0)(s+ix_0-1))^{\delta_{\chi}} L(s,\chi)
$$

for $x_0 \in \mathbf{R}$ the unique real number such that $\chi(\tau(t)) = t^{ix_0}$ as smooth functions of $t \in \mathbf{R}_{>0}$, with $\delta_{\chi} = 0$ if $\chi|_{C^1_F} \neq 1$, and $\delta_{\chi} = 1$ otherwise, the range of $U_S$ is identified with the closed subspace of pairs $(\phi_0,\psi_0) \in A\mathcal{S}(\mathbf{C}_{>0}) \times A\mathcal{S}(\mathbf{C}_{>0})$ such that $(\phi,\psi)$ satisfies $\phi(s) = \rho_S(\chi_S|\cdot|^s_{F,S})\psi(1-s)$.

The unique analytic continuation of $\phi_0$ to a meromorphic function $\Phi(s)$ on the complex $s$-plane with poles located at the poles of $\rho_S$, i.e. over the subset $\mathcal{U}_S$, with multiplicity bounded above by the multiplicity

## PDF page 383

**8.1. ON ORBITAL SUPPORTS - I** · **383**

function $m_S$ of $\mathcal{U}_S$ (see (7.2.2.2) and (3.3.1.3)), is contained in the linear subspace of $\mathscr{M}(\Omega(J_{F,S})(\chi_S|_{J^1_{F,S}}))$:

(8.1.0.6)

$$
\frac{1}{L_{\Sigma_F-S}(\chi,s)} \cdot (\Lambda(s,\chi)\mathscr{O}(\mathbf{C}) \cap A\mathcal{S}(\mathbf{C})) \subset \mathscr{M}(\Omega(J_{F,S})(\chi_S|_{J^1_{F,S}}))
$$

where:

(8.1.0.7)

$$
L_{\Sigma_F-S}(\chi,s) := \prod_{v \in S_f} L_v(\chi_v|\cdot|^s_v)^{-1} \cdot L_f(s,\chi)
$$

where $L_f(s,\chi)$ is the finite Hecke $L$-function (see (3.2.1.7) from Definition 3.2.1.4), and where for each finite place $v \in S_f \subset S$, $L_v(\chi_v|\cdot|^s_v)$ is the Euler factor at $v$ of the Hecke $L$-function $L(s,\chi)$.

Upon writing:

$$
L_S(\chi,s) := \prod_{v \in S} L_v(\chi_v|\cdot|^s_v)
$$

we observe that we have:

$$
\frac{\Lambda(s,\chi)}{L_{\Sigma_F-S}(\chi,s)} = L_S(\chi,s)
$$

as meromorphic functions on the complex $s$-plane.

Let $\phi \in \mathscr{O}(\mathbf{C})$ be such that $\Lambda(s,\chi)\phi(s) \in A\mathcal{S}(\mathbf{C})$, and such that

(8.1.0.8)

$$
\frac{\Lambda(s,\chi)}{L_{\Sigma_F-S}(\chi,s)}\phi(s) = \Phi(s).
$$

Then, since $\Phi$ is Schwartz uniformly on every open vertical strip of bounded width of $\mathbf{C}-i\mathbf{R}$, since $\rho_S(\chi|\cdot|^s_{F,S})$ and all of its meromorphic derivatives grow at most polynomially uniformly on such vertical strips by Proposition 3.3.1.5, and since $\frac{\Lambda(s,\chi)}{L_{\Sigma_F-S}(\chi,s)} = L_S(\chi,s)$ is bounded and holomorphic, as are all of its derivatives, on all such vertical strips, we deduce that we have, as linear subspaces of $\mathscr{M}(\Omega(J_{F,S})(\chi_S|_{J^1_{F,S}}))$:

(8.1.0.9)

$$
\frac{1}{L_{\Sigma_F-S}(\chi,s)} \cdot (\Lambda(s,\chi)\mathscr{O}(\mathbf{C}) \cap A\mathcal{S}(\mathbf{C})) = L_S(\chi,s)A\mathcal{S}(\mathbf{C}).
$$

By Theorem 7.5.0.1, we have:

(8.1.0.10)

$$
\Lambda(s,\chi)\mathscr{O}(\mathbf{C}) \cap A\mathcal{S}(\mathbf{C}) + \prod_{v \in S_p} L_v(\chi_v|\cdot|^s_v)^{-1} A\mathcal{S}(\mathbf{C}) = A\mathcal{S}(\mathbf{C}).
$$

Let $\phi \in A\mathcal{S}(\mathbf{C})$ be the element satisfying (8.1.0.8).

Then

$$
\Phi(s) = L_S(\chi,s)\phi(s) = L_S(\chi,s)\Lambda(s,\chi)u(s) + \prod_{v \in S_p} L_v(\chi_v|\cdot|^s_v)^{-1} L_S(\chi,s)v(s)
$$

for $u,v \in \mathscr{O}(\mathbf{C})$ with $\Lambda(s,\chi)u(s) \in A\mathcal{S}(\mathbf{C})$, and $v \in A\mathcal{S}(\mathbf{C})$.

The meromorphic functions $L_S(\chi,s)\Lambda(s,\chi)u(s)$ and $L_S(\chi,s)v(s)$ are in the range of the linear operator $L_S$ from (5.1.1.4), and since $L_S$ is injective, we deduce that we have that the generic element of $\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf{A}_{F,S}))$ can be written as the sum of an element of $\mathrm{PV}_{S_p}\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf{A}_{F,S}))$ and an element of the linear subspace of $\mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf{A}_{F,S}))$ linearly generated by the images under $\Phi_{F,S,\chi_S|_{J^1_{F,S}}}$ of those Schwartz-Bruhat functions $f \in \mathcal{S}_0(\mathbf{A}_{F,S})$ such that

$$
Z_S(f,\chi|\cdot|^s_{F,S}) = L_S(\chi,s)\Lambda(s,\chi)u(s)
$$

for some $u \in \mathscr{O}(\mathbf{C})$ such that $\Lambda(s,\chi)u(s) \in A\mathcal{S}(\mathbf{C})$.

We observe that $\Phi_{F,S,\chi_S|_{J^1_{F,S}}}(f)$ is contained within the closed subspace:

$$
\Phi_{F,S,\chi_S|_{J^1_{F,S}}}(\mathcal{S}_{\infty}(\mathbf{A}_{F,S_\infty}) \otimes_{\pi} \bigotimes_{v \in S_f} \mathcal{S}(F_v)) \subset \mathrm{H}_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}}, \mathcal{S}_0(\mathbf{A}_{F,S})).
$$

## PDF page 384

**384** · **CHAPTER 8. PERIODIC ORBITS AND FIXED POINTS**

Indeed, we have:

$$
L(\pi_S(f),\chi|\cdot|_F^s)=Z_S(f,\chi_S|\cdot|_{F,S}^s)L_{\Sigma_F-S}(\chi,s)=L_S(\chi,s)\Lambda(s,\chi)L_{\Sigma_F-S}(\chi,s)\phi(s)=\Lambda(s,\chi)^2u(s)
$$

which is indeed an element of

$$
\bar\pi_S(\Phi_{F,S,\chi_S|_{J^1_{F,S}}}(\mathcal S_\infty(\mathbf A_{F,S_\infty})\otimes_\pi\bigotimes_{v\in S_f}\mathcal S(F_v)))
$$

by Theorem 7.3.4.1.

This shows that the continuous linear operator in (8.1.0.1) is surjective, hence open by [NB, Thm.14.4.5(a)], being source and target Fréchet spaces. It is also injective, since, as an application of the Asymptotic Residue Theorem, which applies by Lemma 7.1.1.1, we have:

$$
\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}},\mathcal S_p(\mathbf A_{F,S}))\cap \mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}},\mathcal S(\mathbf A_{F,S}))=\mathrm{PV}_{S,S_p}\mathrm H_{0,\mathrm{cont}}(\chi_S|_{J^1_{F,S}},\mathcal S_p(\mathbf A_{F,S})).
$$

Part (2) follows from the same method discussed for (1) upon using Theorem 7.5.0.1 for $S_0=\{v\}$. $\square$

We will be concluding the Chapter by describing the supports of the dual basis elements of the absolute Schauder bases within the orbital quotients

$$
\mathscr{E}_{S,S_p}(\chi|_{J^1_{F,S}}),\quad \mathscr{E}_{S,S_\infty}(\chi|_{J^1_{F,S}})
$$

defined in (7.3.1.5) from Definition 7.3.1.3 and (7.3.4.3) from Notation 7.3.4.1, respectively.

Describing such supports is the scope of Theorem 8.3.0.1. While it will not be used throughout the rest of this work, we will be using it below throughout the remainder of this section, to explain how expectations formulated by Deninger fit within this treatise.

**8.2. Stack-theoretic Periodic Orbits and Fixed Points**

We begin by introducing some terminology and notation:

DEFINITION 8.2.0.1. Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places. We denote by $S_f$ the subset of $S$ of the finite places of $F$ contained in $S$.

We define:

(1) The subset of the $S$-adeles:

$$
Z_{F,S}:=\{e_1:=1\}\cup\{e_v\}_{v\in S}\subset \mathbf A_{F,S} \tag{8.2.0.1}
$$

and the subset of the global adeles:

$$
Z_F:=\{e_1:=1\}\cup\{e_v\}_{v\in\Sigma_F}\subset \mathbf A_F \tag{8.2.0.2}
$$

where $e_v\in\mathbf A_{F,S}$ in (8.2.0.1) is the $S$-adele whose $v$-indexed coordinate is 0, and whose $v'$-indexed coordinate is 1 for all $v'\in S-\{v\}$, and $e_v\in\mathbf A_F$ from (8.2.0.2) is the global adele whose $v$-indexed coordinate is 0, and whose $v'$-indexed coordinate is 1 for all $v'\in\Sigma_F-\{v\}$. We endow both $Z_S$ and $Z_F$ with the respective subspace topologies.

(2) The subsets of the $S$-adeles:

$$
D_{S,1}:=\mathbf A_{F,S}^\times,\quad D_{S,v}:=\mathrm{GL}_1(\mathbf A_{F,S})\cdot e_v \tag{8.2.0.3}
$$

endowed with the subspace topology, and the subsets of the global adeles:

$$
D_1:=\mathbf A_F^\times,\quad D_v:=\mathrm{GL}_1(\mathbf A_F)\cdot e_v \tag{8.2.0.4}
$$

endowed with the subspace topology inherited from $\mathbf A_F$.

## PDF page 385

**8.2. STACK-THEORETIC PERIODIC ORBITS AND FIXED POINTS** · **385**

(3) The subsets:

$$
D_{F,S}:=D_{S,1}\cup\bigcup_{v\in S}D_{S,v}\subset\mathbf A_{F,S},\quad D_F:=D_1\cup\bigcup_{v\in\Sigma_F}D_v\subset\mathbf A_F \tag{8.2.0.5}
$$

equipped with the respective subspace topologies.

The continuous actions of $\mathrm{GL}_1(\mathbf A_{F,S})$ on $\mathbf A_{F,S}$ and $\mathrm{GL}_1(\mathbf A_F)$ on $\mathbf A_F$ by left-translation, stabilize the subsets introduced in (8.2.0.6), (8.2.0.7) and (8.2.0.8) of Definition 8.2.0.1, inducing continuous actions by left-translation on each of them, respectively.

We discuss some preparations around $D_{F,S}$ and $D_F$. We first need the following subspaces of $D_{F,S}$ and $D_F$, respectively:

DEFINITION 8.2.0.2. Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places. We denote by $S_f$ the subset of $S$ of the finite places of $F$ contained in $S$.

We define:

(1) the subsets of the $S$-adeles:

$$
D^1_{S,1}:=\{g\in\mathbf A_{F,S}^\times:|g|_{F,S}=1\},\quad D^1_{S,v}:=\mathrm{GL}_1(\mathbf A_{F,S})^1\cdot e_v \tag{8.2.0.6}
$$

endowed with the subspace topology, and the subsets of the global adeles:

$$
D^1_1:=\{g\in\mathbf A_F^\times:|g|_F=1\},\quad D^1_v:=\mathrm{GL}_1(\mathbf A_F)^1\cdot e_v \tag{8.2.0.7}
$$

endowed with the subspace topology inherited from $\mathbf A_F$.

(2) The subsets:

$$
D^1_{F,S}:=D^1_{S,1}\cup\bigcup_{v\in S}D^1_{S,v}\subset\mathbf A_{F,S},\quad D^1_F:=D^1_1\cup\bigcup_{v\in\Sigma_F}D^1_v\subset\mathbf A_F \tag{8.2.0.8}
$$

equipped with the respective subspace topologies.

We begin by describing the topology on $D^1_{F,S}$ and $D^1_F$.

LEMMA 8.2.0.3. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing the Archimedean places. Then:*

(1) *The subspace topology on $D^1_{F,S}$ inherited from $\mathbf A_{F,S}$ agrees with the quotient topology inherited from the product topology on $\mathrm{GL}_1(\mathbf A_{F,S})^1\times Z_{F,S}$ under the continuous surjective map $\mathrm{GL}_1(\mathbf A_{F,S})^1\times Z_{F,S}\to D^1_{F,S}$.*

(2) *The subspace topology on $D^1_F$ inherited from $\mathbf A_F$ agrees with the quotient topology inherited from the product topology on $\mathrm{GL}_1(\mathbf A_F)^1\times Z_F$ under the continuous surjective map $\mathrm{GL}_1(\mathbf A_F)^1\times Z_F\to D^1_F$.*

*Both $D^1_{F,S}$ and $D^1_F$ are Hausdorff, metrizable, second-countable, perfectly normal, separable, locally compact, $\sigma$-compact and paracompact.*

PROOF. (1) : The map $\mathrm{GL}_1(\mathbf A_{F,S})^1\times Z_{F,S}\to D^1_{F,S}$ is continuous and surjective. The pre-images in $\mathrm{GL}_1(\mathbf A_{F,S})^1\times Z_{F,S}$ of $D^1_{S,1}$ and $D^1_{S,v}$ are, for each $v\in S$, $\mathrm{GL}_1(\mathbf A_{F,S})^1\times\{1\}$ and $\mathrm{GL}_1(\mathbf A_{F,S})^1\times\{e_v\}$, respectively.

Each $D^1_{S,1}$ and $D^1_{S,v}$, for every $v\in S$, is closed in $D^1_{F,S}$. To see this, we proceed as follows. For $D^1_{S,1}$, we observe that $\mathrm{GL}_1(\mathbf A_{F,S})^1$ is closed in $\mathbf A_{F,S}$, and hence in $D^1_{F,S}$.

For $v\in S$, we observe that the stabilizer of $e_v\in\mathbf A_{F,S}$ in $\mathrm{GL}_1(\mathbf A_{F,S})^1$ is $\mathcal O_{F_v}^\times$, embedded through the $v$-indexed “coordinate” insertion homomorphism, an injective homomorphism with closed image. Since $|\mathcal O_{F_v}^\times|_{F,S}=1$, then $D^1_{S,v}$ is the subset of $\mathbf A_{F,S}$ given by those $S$-adeles $x\in\mathbf A_{F,S}$, $x=(x_w)_{w\in S}$, such that $x_v=0$, and $\prod_{w\in S-\{v\}}|x_w|_w=1$, both of which are closed conditions.

By [Bou-GT, Ch.I,§5.1,Prop.2,p.51], it is therefore enough to show that each $D^1_{S,1}$ and $D^1_{S,v}$ is equipped with the quotient topology. This is indeed the case, because the idelic topology on $\mathrm{GL}_1(\mathbf A_{F,S})^1$ and the subspace topology inherited from $\mathbf A_{F,S}$ agree.

## PDF page 386

**386** · **CHAPTER 8. PERIODIC ORBITS AND FIXED POINTS**

(2) : The map $\mathrm{GL}_1(\mathbf A_F)^1\times Z_F\to D^1_F$ is continuous and surjective. The pre-images in $\mathrm{GL}_1(\mathbf A_F)^1\times Z_F$ of $D^1_1$ and $D^1_v$ are, for each place $v$ of $F$, $\mathrm{GL}_1(\mathbf A_F)^1\times\{1\}$ and $\mathrm{GL}_1(\mathbf A_F)^1\times\{e_v\}$, respectively.

Each $D^1_1$ and $D^1_v$ is equipped with the quotient topology, because the idelic topology on $\mathrm{GL}_1(\mathbf A_F)^1$ and the subspace topology inherited from $\mathbf A_F$ agree by [CF, Ch.II,§16,Lemma,p.69].

$D^1_1$ is closed in $D^1_F$, since it is closed in $\mathbf A_F$. For each place $v$ of $F$, the subset $D^1_v$ of $\mathbf A_F$ is the intersection of the closed subset $H_v:=\{x\in\mathbf A_F:x_v=0\}$, with the subset $\Gamma_v\subset\mathbf A_F$ such that its projection $\overline\Gamma_v$ onto $\widehat\prod_{w\in\Sigma_F-\{v\}}(F_w,\mathcal O_{F_w})$ is the subset of those elements $(x_w)_{w\ne v}$ such that all but finitely many of the $x_w$ is in $\mathcal O_{F_w}^\times$, and $\prod_{w\ne v}|x_w|_w=1$. $\overline\Gamma_v$ is therefore closed, and the continuous surjective map $\Gamma_v\to\overline\Gamma_v$ is bijective, hence a homeomorphism. We deduce that $\Gamma_v$ is closed in $\mathbf A_F=\widehat\prod_{w\in\Sigma_F-\{v\}}(F_w,\mathcal O_{F_w})\times F_v$, and hence so is $\Gamma_v\cap H_v=D^1_v$.

Since $\{D^1_v\}_{v\in\Sigma_F}\cup\{D^1_1\}$ is a locally finite cover of $D^1_F$ by closed subsets, then by [Bou-GT, Ch.I,§5.1,Prop.2,p.51] we deduce that $D^1_F$ is equipped with the quotient topology induced by the continuous surjective map $\mathrm{GL}_1(\mathbf A_F)^1\times Z_F\to D^1_F$, since $D^1_1$ and $D^1_v$ is.

$D^1_{F,S}$ and $D^1_F$ are Hausdorff, metrizable and second-countable, since they are subspaces of $\mathbf A_{F,S}$, respectively $\mathbf A_F$, both Hausdorff, metrizable and second-countable. They are therefore separable, perfectly normal and paracompact. They are countable unions of Hausdorff quotients of $\mathrm{GL}_1(\mathbf A_{F,S})^1$, respectively $\mathrm{GL}_1(\mathbf A_F)^1$, and they are therefore $\sigma$-compact, since $\mathrm{GL}_1(\mathbf A_{F,S})^1$ and $\mathrm{GL}_1(\mathbf A_F)^1$ both are. Since each point $x$ of $D^1_{F,S}$, respectively $D^1_F$, is contained in some $D^1_{S,1}$, $D^1_{S,v}$, $D^1_1$, or $D^1_v$, respectively, and each of these is a locally compact space, then $x$ has a compact neighborhood, and since $D^1_{F,S}$ and $D^1_F$ are Hausdorff, they are locally compact and $\sigma$-compact. $\square$

PROPOSITION 8.2.0.4. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. We let $\tau_S:\mathbf R_{>0}\to\mathrm{GL}_1(\mathbf A_{F,S})$ be a choice of continuous homomorphic section to the $S$-idelic norm, and $\tau:\mathbf R_{>0}\to\mathrm{GL}_1(\mathbf A_F)$ a choice of continuous homomorphic section to the idelic norm.*

*We define, for every finite place $v\in S$ and $\mathfrak p_v$ the unique prime ideal of $\mathcal O_F$ associated to $v$:*

$$
\tau_S([1,N(\mathfrak p_v)))\cdot e_v\subset\mathbf A_{F,S} \tag{8.2.0.9}
$$

*and for every finite place $v$ of $F$ and $\mathfrak p_v$ the unique prime ideal of $\mathcal O_F$ associated to $v$:*

$$
\tau([1,N(\mathfrak p_v)))\cdot e_v\subset\mathbf A_F \tag{8.2.0.10}
$$

*each equipped with the subspace topology. Then:*

(1) *For every $x\in D_{S,v}$ there exists $g\in\mathrm{GL}_1(\mathbf A_{F,S})$, unique up to multiplication by $\mathcal O_{F_v}^\times\subset\mathrm{GL}_1(\mathbf A_{F,S})$, such that $g^{-1}x\in\tau_S([1,N(\mathfrak p_v)))\cdot e_v$.*

(2) *For every $x\in D_v$ there exists $g\in\mathrm{GL}_1(\mathbf A_F)$, unique up to multiplication by $\mathcal O_{F_v}^\times\subset\mathrm{GL}_1(\mathbf A_F)$, such that $g^{-1}x\in\tau([1,N(\mathfrak p_v)))\cdot e_v$.*

PROOF. (1) : $D_{S,v}$ is homeomorphic to the quotient of $\mathrm{GL}_1(\mathbf A_{F,S})$ by the stabilizer of $e_v$, which is $F_v^\times\subset\mathrm{GL}_1(\mathbf A_{F,S})$ embedded through the $v$-indexed “coordinate”. $D_{S,v}$ is therefore continuously bijective to $\tau_S([1,N(\mathfrak p_v)))\cdot\mathrm{GL}_1(\mathbf A_{F,S})^1\cdot e_v$, and since the stabilizer of $e_v$ in $\mathrm{GL}_1(\mathbf A_{F,S})^1$ is $\mathcal O_{F_v}^\times$, (1) follows.

(2) : $D_v$ is homeomorphic to the quotient of $\mathrm{GL}_1(\mathbf A_F)$ by the stabilizer of $e_v$, which is $F_v^\times\subset\mathrm{GL}_1(\mathbf A_F)$ embedded through the $v$-indexed “coordinate”. (2) therefore follows upon observing that the stabilizer of $e_v$ in $\mathrm{GL}_1(\mathbf A_F)^1$ is $\mathcal O_{F_v}^\times$. $\square$

PROPOSITION 8.2.0.5. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. For every Archimedean place $v\in S$, the action of $\mathrm{GL}_1(\mathbf A_{F,S})^1$ on $D_{S,v}$ is transitive. For every Archimedean place $v$ of $F$, the action of $\mathrm{GL}_1(\mathbf A_F)^1$ on $D_v$ is transitive.*

(1) *If $v$ is real, then every point of $D_{S,v}$, respectively of $D_v$, is stabilized by $\{\pm 1\}$ as a subgroup of $\mathrm{GL}_1(\mathbf A_{F,S})$, respectively $\mathrm{GL}_1(\mathbf A_F)$, embedded injectively as the subgroup of the units of $F_v^\times$.*

## PDF page 387

**8.3. ON ORBITAL SUPPORTS - II** · **387**

(2) *If $v$ is complex, then every point of $D_{S,v}$, respectively $D_{v}$, is stabilized by $\mathrm{U}(1)$ as a subgroup of $\mathrm{GL}_{1}(\mathbf{A}_{F,S})$, respectively $\mathrm{GL}_{1}(\mathbf{A}_{F})$, embedded injectively as the subgroup of the units of $F_{v}^{\times}$.*

Proof. Since $v$ is Archimedean, we may choose a continuous homomorphic section $\tau_{v}$ to the $S$-idelic, respectively idelic norm, and hence $\tau_{v}(\mathbf{R}_{>0})\cdot\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}$ acts on $D_{S,v}$ only through $\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}$. Simiarly for $\tau_{v}(\mathbf{R}_{>0}) \cdot \mathrm{GL}_{1}(\mathbf{A}_{F})^{1}$ acting on $D_{v}$ only through $\mathrm{GL}_{1}(\mathbf{A}_{F})^{1}$. Since $D_{S,v}$ is the orbit of $e_{v}$ under the continuous action of $\mathrm{GL}_{1}(\mathbf{A}_{F,S})$ on $\mathbf{A}_{F,S}$, as is $D_{v}$ of $e_{v}$ under the continuous action of $\mathrm{GL}_{1}(\mathbf{A}_{F})^{1}$ on $\mathbf{A}_{F}$, we deduce that $\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}$, respectively $\mathrm{GL}_{1}(\mathbf{A}_{F})^{1}$, acts transitively on $D_{S,v}$, respectively $D_{v}$.

Such actions factor through the quotients of $\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}$, respectively $\mathrm{GL}_{1}(\mathbf{A}_{F})^{1}$, by the stabilizers of $e_{v}$, which are $\{\pm 1\} \subset F_{v}^{\times}$ if $v$ is real, and $\mathrm{U}(1)$ if $v$ is complex.

$\square$

PROPOSITION 8.2.0.6. *Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Let $v_{0}$ be an Archimedean place contained in $S$. We let $\tau_{S,v_{0}}:\mathbf{R}_{>0} \to \mathrm{GL}_{1}(\mathbf{A}_{F,S})$ be the choice of continuous homomorphic section to the $S$-idelic norm based at the $v_{0}$-indexed factor of $\mathrm{GL}_{1}(\mathbf{A}_{F,S})$, and $\tau_{v_{0}}:\mathbf{R}_{>0} \to \mathrm{GL}_{1}(\mathbf{A}_{F})$ the choice of continuous homomorphic section to the idelic norm based at the $v_{0}$-indexed factor of $\mathrm{GL}_{1}(\mathbf{A}_{F})$, as per Definition A.2.2.5.*

*(1) The closure within $D_{F,S}$ of $\tau_{S,v_{0}}(\mathbf{R}_{>0}) \subset D_{S,1}$ is $\tau_{S,v_{0}}(\mathbf{R}_{>0}) \cup \{e_{v_{0}}\}$.*

*(2) The closure within $D_{F}$ of $\tau_{v_{0}}(\mathbf{R}_{>0}) \subset D_{1}$ is $\tau_{v_{0}}(\mathbf{R}_{>0}) \cup \{e_{v_{0}}\}$.*

Proof. In either case, $\tau_{v_{0}}(\mathbf{R}_{>0}) \cup \{e_{v_{0}}\}$ is homeomorphic to $[0,+\infty)$, a complete metric subspace of the metrizable spaces $D_{F,S}$, respectively $D_{F}$, and, as such, sequentially closed, hence closed, being the ambient second-countable, hence sequential, by Lemma 8.2.0.3.

*$\square$*

**8.3. On Orbital Supports - II**

Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal{O}_{F,S}) = 1$.

Let $\chi \in \widehat{C_{F}}$ be a continuous character, and define $\chi_{S}$ the unique continuous character of $J_{F,S}$ obtained from $\chi$ by descending the restriction of $\chi$ to $C_{F,S}$ to $J_{F,S}$ by $\widehat{\mathcal{O}}^{\times}_{\Sigma_{F}-S}$-invariance.

The following Theorem describes the loci of $\mathbf{A}_{F,S}$, modulo the continuous left-translation action of $\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}$, over which the Orbital subquotients of $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$ from (7.3.1.5) and (7.3.4.3) are supported.

Theorem 8.3.0.1 (On Orbital Supports - II). *Let $F$ be a number field, $S$ a finite set of finite places of $F$ containing all the Archimedean places. Assume $\mathrm{Pic}(\mathcal{O}_{F,S}) = 1$. Let $\chi \in \widehat{C_{F}}$ be a continuous character. Assume $\chi$ is unramified outside $S$.*

*Assume $S$ is saturated.*

*We denote by $\chi_{S}$ the unique continuous character of $J^{1}_{F,S}$ obtained from $\chi$ by descending the restriction of $\chi$ to $C_{F,S}$ by $\widehat{\mathcal{O}}^{\times}_{\Sigma_{F}-S}$-invariance.*

*Let $\mathscr{E}$ denote either of the Orbital subquotients of $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$:*

$$
\mathscr{E}_{S,S_{p}}(\chi|_{J^{1}_{F,S}}), \quad \mathscr{E}_{S,S_{\infty}}(\chi|_{J^{1}_{F,S}})
$$

*from (7.3.1.5), respectively (7.3.4.3), for $p$ a prime number such that $S_{p} \subset S$.*

*For every tempered distribution $T$ on $\mathbf{A}_{F,S}$ in the linear image of the continuous adjoint of the quotient map*

$$
\mathcal{S}(\mathbf{A}_{F,S}) \to \mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S})) \to \mathscr{E}
$$

*and every $f \in \mathcal{S}(\mathbf{A}_{F,S})$, there exists $f_{0} \in \mathcal{S}(\mathbf{A}_{F,S})$ such that*

$$
\langle T, f\rangle_{\mathcal{S}(\mathbf{A}_{F,S})^{\prime}_{\beta},\mathcal{S}(\mathbf{A}_{F,S})} = \langle T, f_{0}\rangle_{\mathcal{S}(\mathbf{A}_{F,S})^{\prime}_{\beta},\mathcal{S}(\mathbf{A}_{F,S})} \tag{8.3.0.1}
$$

## PDF page 388

**388** · **CHAPTER 8. PERIODIC ORBITS AND FIXED POINTS**

*and the support of $f_{0}$ is entirely contained within:*

(1) *The union of the closed subsets:*

$$
H_{S,S_{p}} := \bigcup_{v\in S_{p}} \{x \in\mathbf{A}_{F,S} : x_{v} = 0, x_{w} \neq 0 \text{ for all } w \in S-\{v\}\} \subset \mathbf{A}_{F,S} \tag{8.3.0.2}
$$

if $\mathscr{E} = \mathscr{E}_{S,S_{p}}(\chi_{S}|_{J^{1}_{F,S}})$. The topological quotient stack:

$$
[H_{S,S_{p}}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}] \tag{8.3.0.3}
$$

*is $2$-isomorphic to the quotient stack:*

$$
\coprod_{v\in S_{p}}[\mathbf{R}_{>0}/F_{v}^{\times}] \tag{8.3.0.4}
$$

*where $F_{v}^{\times}$ acts on $\mathbf{R}_{>0}$ by left translation through the $S$-idelic norm, with $\mathcal{O}_{F_{v}}^{\times}$ inertia. Its coarse space is the topological disjoint union of compact Hausdorff loops:*

$$
\coprod_{v\in S_{p}}\mathbf{R}_{>0}/N(\mathfrak{p}_{v})^{\mathbf{Z}} \tag{8.3.0.5}
$$

*where $\mathfrak{p}_{v} \subset \mathcal{O}_{F}$ is the unique prime ideal corresponding to the finite place $v \in S_{p}$.*

(2) *The union of the closed subsets:*

$$
H_{S,S_{\infty}}:= \bigcup_{v\in S_{\infty}} \{x \in\mathbf{A}_{F,S} : x_{v} = 0, x_{w} \neq 0 \text{ for all } w \in S-\{v\}\} \subset \mathbf{A}_{F,S} \tag{8.3.0.6}
$$

if $\mathscr{E} = \mathscr{E}_{S,S_{\infty}}(\chi_{S}|_{J^{1}_{F,S}})$. The topological quotient stack:

$$
[H_{S,S_{\infty}}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}] \tag{8.3.0.7}
$$

*is $2$-isomorphic to the quotient stack:*

$$
\coprod_{v\in S_{\infty}}BU_{v} \tag{8.3.0.8}
$$

*where $U_{v} \subset F_{v}^{\times}$ is the compact subgroup $\ker(|\cdot|_{v})$, and $BU_{v}$ is its topological classifying stack. Its coarse space is the disjoint union of $r_{1} + r_{2}$ points, one per each Archimedean place of $F$.*

Proof. (1) : By Theorem 8.1.0.1(1), the continuous functionals in $\mathscr{E}_{S,S_{p}}(\chi_{S}|_{J^{1}_{F,S}})^{\prime}_{\beta}$ map under the continuous adjoint to the quotient map $\mathcal{S}(\mathbf{A}_{F,S}) \to \mathscr{E}_{S,S_{p}}(\chi_{S}|_{J^{1}_{F,S}})$ to the image of a unique continuous functional on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{p}(\mathbf{A}_{F,S}))$, where $\mathcal{S}_{p}(\mathbf{A}_{F,S}) \subset \mathcal{S}(\mathbf{A}_{F,S})$ is the closed subspace defined in (8.1.0.4). This means that, for each such $T$ and for every $f \in \mathcal{S}(\mathbf{A}_{F,S})$, there exists $f_{1} \in \mathrm{PV}_{S,S_{p}}\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$ such that $f -f_{1} \in \mathcal{S}_{p}(\mathbf{A}_{F,S})$, and $T(f -f_{1}) = T(f)$.

The elements of $\mathcal{S}_{p}(\mathbf{A}_{F,S})$ are supported on $H_{S,S_{p}}$. The remaining assertions in (1) follow from Proposition 8.2.0.4 and the observation that we have, as topological subspaces of $\mathbf{A}_{F,S}$:

$$
H_{S,S_{p}} = \bigcup_{v\in S_{p}} D_{S,v}
$$

where $D_{S,v}$ was defined in (8.2.0.6) from Definition 8.2.0.1(2).

(2) : The continuous dual of $\mathscr{E}_{S,S_{\infty}}(\chi_{S}|_{J^{1}_{F,S}})$ is comprised of continuous functionals on $\mathrm{PV}_{S,S_f} \mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$ that vanish on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S}))$.

The elements of $\mathrm{PV}_{S,S_f} \mathcal{S}(\mathbf{A}_{F,S})$ are supported over $H_{S,S_{\infty}}$. The remaining assertions of (2) follow from Proposition 8.2.0.5, upon observing that we have, as topological subspaces of $\mathbf{A}_{F,S}$:

$$
H_{S,S_{\infty}}= \bigcup_{v\in S_{\infty}} D_{S,v}
$$

## PDF page 389

8.4.
ORBITAL TRACES
389

where $D_{S,v}$ is defined in (8.2.0.6) from Definition 8.2.0.1(2).
$\Box$

8.4. Orbital Traces

Let $F$ be a number field, $S$ a finite set of places of $F$ containing all the Archimedean places, and such
that $\mathrm{Pic}(\mathcal{O}_{F,S}) = 1$. Assume $S$ is saturated.

We let $\chi \in \widehat{C_{F}}$ be a continuous character, unramified outside $S$.

We let $\chi_{S}$ be the unique continuous character of $J_{F,S}$ obtained by descending the restriction of $\chi$ to $C_{F,S}$
by $\widehat{\mathcal{O}}^{\times}_{\Sigma_{F}-S}$-invariance.

We return to Theorem 7.1.2.3, which was the starting point of this Chapter.

The strong recurrence on vertical strips of bounded width, of the finite partial reciprocal Euler products
of the finite Hecke $L$-function (see Lemma 7.1.1.1 and Proposition B.5.3.3, ultimately an application of the
Kronecker-Weyl Theorem; see Theorem B.5.2.1), led to the asymptotic expansion: We reorganize the statement
as follows: let $f \in \mathcal{S}(\mathbf{A}_{F,S})$ be any Schwartz-Bruhat function. Then, for all $g \in J_{F,S}$ as $|g|_{F,S} \to 0^{+}$, we have,
for any real number $A > 0$:

$$\Phi_{F,S,\chi_{S}|_{J^{1}_{F,S}}}(f)(g) =$$
$$\sum_{v \in S_{\infty}} \sum_{m \in \mathbf{N}_{>0}, m < A} \sum_{1 \le k \le m_{S}(f,c_{v,m,\chi})} \frac{(-1)^{k-1} a_{k-1}(f,c_{v,m,\chi})}{(k-1)!} (\log|g|_{F,S})^{k-1} \chi|g|^{m+it_{v}}_{F,S} \tag{8.4.0.1}$$
$$+ \sum_{p: S_{p} \subset S_{f}-S_{\chi}} \sum_{v \in S_{p}} \sum_{m \in \mathbf{Z}} \sum_{1 \le k \le m_{S}(f,c_{v,m,\chi})} \frac{(-1)^{k-1} a_{k-1}(f,c_{v,m,\chi})}{(k-1)!} (\log|g|_{F,S})^{k-1} \chi|\cdot|^{-\frac{2\pi i m}{\log(q_{v})}+it_{v}}_{F,S} \tag{8.4.0.2}$$
$$+ O_{A}(|g|^{A}_{F,S}) \tag{8.4.0.3}$$

which we have reorganized in light of Theorem 7.3.1.6, to highlight the absolute convergence of the sums
indexed by each prime number $p$ such that $S_{p} \subset S$, a consequence of the Theorem.

As a consequence of Theorem 8.3.0.1 and Theorem 7.3.4.1(4) and (5), is that for $v \in S$ a finite place, we
can find Schwartz-Bruhat functions $f$ supported entirely over
$$\{x \in \mathbf{A}_{F,S} : x_{v} = 0, x_{w} \neq 0 \text{ for all } w \in S-\{v\}\} \subset \mathbf{A}_{F,S}$$
and such that their own asymptotic expansion as $|g|_{F,S} \to 0^{+}$ takes the form:

$$\Phi_{F,S,\chi_{S}|_{J^{1}_{F,S}}}(f)(g) = \frac{(-1)^{k-1} a_{k-1}(f,c_{v,m,\chi})}{(k-1)!} (\log|g|_{F,S})^{k-1} \chi|g|^{m+it_{v}}_{F,S} + O_{A}(|g|^{A}_{F,S}) \tag{8.4.0.4}$$

with $v \in S_{\infty}$ fixed and $m < A$, and:

$$\Phi_{F,S,\chi_{S}|_{J^{1}_{F,S}}}(f)(g) = \frac{(-1)^{k-1} a_{k-1}(f,c_{v,m,\chi})}{(k-1)!} (\log|g|_{F,S})^{k-1} \chi|\cdot|^{-\frac{2\pi i m}{\log(q_{v})}+it_{v}}_{F,S} + O_{A}(|g|^{A}_{F,S}) \tag{8.4.0.5}$$

for $v \in S_{f}$ at which $\chi$ is unramified, with $q_{v} := N(\mathfrak{p}_{v})$ where $\mathfrak{p}_{v} \subset \mathcal{O}_{F}$ is the unique prime ideal corresponding
to the finite place $v$ of $F$.

A consequence of Theorem 8.3.0.1 and hence of Theorem 8.1.0.1, is that we may organize the nuclear
Fréchet space
$$\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$$

## PDF page 390

390
CHAPTER 8.
PERIODIC ORBITS AND FIXED POINTS

and its suquotients $\mathscr{E}_{S,S_{\infty}}(\chi_{S}|_{J^{1}_{F,S}})$ and $\mathscr{E}_{S,S_{p}}(\chi_{S}|_{J^{1}_{F,S}})$ according to the following symbolism:

(8.4.0.6)

```latex
\begin{tikzcd}
\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S})) \arrow[r] \arrow[d] & \mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S})) \arrow[r] \arrow[d] & \mathscr{E}_{S,S_{\infty}}(\chi_{S}|_{J^{1}_{F,S}}) \times \prod^{\prime}_{p:S_{p}\subset S} \mathscr{E}_{S,S_{p}}(\chi_{S}|_{J^{1}_{F,S}}) \arrow[d] \\
{[D_{S,1}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}]} \arrow[r, "j"'] \arrow[d, "\simeq"'] & {[D_{F,S}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}]} & \coprod^{\prime}_{v \in S} [D_{S,v}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}] \arrow[d, "\simeq"] \arrow[l, "i"] \\
\underline{J_{F,S}/J^{1}_{F,S}} &  & \left(\coprod_{v \in S_{\infty}} BU_{v}\right) \coprod \left(\coprod_{p:S_{p}\subset S} \coprod^{\prime}_{v \in S_{p}} [\mathbf{R}_{>0}/F^{\times}_{v}]\right)
\end{tikzcd}
```

The top row in (8.4.0.6) is a short exact sequence (on the left and in the middle), both linearly and
topologically. This is the content of Proposition 5.3.4.4 and Proposition 5.3.4.5.

The row below it, indicates which loci of the quotient stack $[D_{F,S}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}]$ each nuclear Fréchet
space is supported on.

The Orbital quotients $\mathscr{E}_{S,S_{\infty}}(\chi_{S}|_{J^{1}_{F,S}})$, respectivey $\mathscr{E}_{S,S_{p}}(\chi_{S}|_{J^{1}_{F,S}})$ (where we omit mentioning the continuous
character $\chi_{S}$, identifying the $\chi_{S}$-isotype of each such subquotient), are thought of as being supported over the
fat points $BU_{v}$ for each Archimedean place $v \in S_{\infty}$, respectively over the periodic orbits $[\mathbf{R}_{>0}/F^{\times}_{v}]$ (whose
coarse spaces are, respectively, a loop $\mathbf{R}_{>0}/N(\mathfrak{p}_{v})^{\mathbf{Z}}$, for each finite place $v \in S$.

We now look into the effect of the $S$-idelic Mellin transform $L_{S}$ (see (5.1.1.2)) on the diagram in (8.4.0.6).
It turns it into the following divisor exact sequence:

(8.4.0.7)

```latex
\begin{tikzcd}
L_{S}\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S})) \arrow[r] \arrow[d] & L_{S}\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S})) \arrow[r] \arrow[d] & L_{S}\mathscr{E}_{S,S_{\infty}}(\chi_{S}|_{J^{1}_{F,S}}) \times \prod^{\prime}_{p:S_{p}\subset S} L_{S}\mathscr{E}_{S,S_{p}}(\chi_{S}|_{J^{1}_{F,S}}) \arrow[d] \\
\Omega(J_{F,S})(\chi_{S}|_{J^{1}_{F,S}}) \arrow[r, "j"'] & X_{S}(\chi_{S}|_{J^{1}_{F,S}}) & \mathcal{U}_{S_{\infty}} \coprod (\coprod^{\prime}_{p:S_{p}\subset S} \mathcal{U}_{S_{p}}) \arrow[l, "i"]
\end{tikzcd}
```

where $\Omega(J_{F,S})(\chi_{S}|_{J^{1}_{F,S}})$ is the connected component parametrized by $\chi_{S}|_{J^{1}_{F,S}}$ of the Riemann surface $\Omega(J_{F,S})$ of
$S$-idelic quasi-characters, $X_{S}(\chi_{S}|_{J^{1}_{F,S}})$ is a topological completion whose boundary is the divisor $\mathcal{U}_{S_{\infty}} \coprod (\coprod^{\prime}_{p:S_{p}\subset S} \mathcal{U}_{S_{p}})$,
where each divisor $\mathcal{U}_{S_{\infty}}$, respectively $\mathcal{U}_{S_{p}}$, is defined in (5.3.4.13) from Proposition 5.3.4.5, respectively (7.2.2.1).

The Second Structure Theorem (see Theorem 5.4.1.1), provides an explicit description of the nuclear
Fréchet spaces in the top row of (8.4.0.7) in terms of spaces of meromorphic functions on $\Omega(J_{F,S})(\chi_{S}|_{J^{1}_{F,S}})$,
Schwartz uniformly on the vertical strips of bounded width of the complex $s$-plane not containint $i\mathbf{R}$ in their
interior, and satisfying the $S$-local functional equation from (3.3.1.2) of Theorem 3.3.1.1.

The product of the principal part continuous functionals factors through the top horizontal arrow in
(8.4.0.7).

The $S$-local function spaces and their supporting geometric objects, whether it be the quotient stacks
$[D_{F,S}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}]$ on the backward side of the Mellin transform, or the extended topological space $X_{S}(\chi_{S}|_{J^{1}_{F,S}})$,
its open sub-domain $\Omega(J_{F,S})(\chi_{S}|_{J^{1}_{F,S}})$ and complementary boundary divisor, on the forward side of the Mellin
transform, coalesce together into the global ones, to give the following global analogs of the diagrams in
(8.4.0.6) and (8.4.0.7):

## PDF page 391

8.4.
ORBITAL TRACES
391

(8.4.0.8)

```latex
\begin{tikzcd}
\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^{1}_{F}}, \mathcal{S}_{00}(\mathbf{A}_{F})) \arrow[r] \arrow[d] & \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^{1}_{F}}, \mathcal{S}(\mathbf{A}_{F})) \arrow[r] \arrow[d] & \mathscr{E}_{S_{\infty}}(\chi|_{C^{1}_{F}}) \times \prod^{\prime}_{p} \mathscr{E}_{S_{p}}(\chi|_{C^{1}_{F}}) \arrow[d] \\
{[D_{F,1}/\mathrm{GL}_{1}(\mathbf{A}_{F})^{1}]} \arrow[r, "j"'] \arrow[d, "\simeq"'] & {[D_{F}/\mathrm{GL}_{1}(\mathbf{A}_{F})^{1}]} & \coprod^{\prime}_{v \in \Sigma_{F}} [D_{F,v}/\mathrm{GL}_{1}(\mathbf{A}_{F})^{1}] \arrow[d, "\simeq"] \arrow[l, "i"] \\
\underline{C_{F}/C^{1}_{F}} &  & \left(\coprod_{v \in S_{\infty}} BU_{v}\right) \coprod \left(\coprod_{p} \coprod^{\prime}_{v \in S_{p}} [\mathbf{R}_{>0}/F^{\times}_{v}]\right)
\end{tikzcd}
```

where now the coproduct $\coprod_{p} \coprod_{v \in S_{p}} [\mathbf{R}_{>0}/F^{\times}_{v}]$ is indexed by all prime numbers, and its coarse space is a
countable disjoint union of loops $\coprod_{p} \coprod_{v \in S_{p}} \mathbf{R}_{>0}/N(\mathfrak{p}_{v})^{\mathbf{Z}}$ organized according to splitting patterns.

The global idelic Mellin transform turns the diagram in (8.4.0.8) into the following:

(8.4.0.9)

```latex
\begin{tikzcd}
L\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^{1}_{F}}, \mathcal{S}_{00}(\mathbf{A}_{F})) \arrow[r] \arrow[d] & L\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^{1}_{F}}, \mathcal{S}(\mathbf{A}_{F})) \arrow[r] \arrow[d] & L\mathscr{E}_{S_{\infty}}(\chi|_{C^{1}_{F}}) \times \prod^{\prime}_{p} L\mathscr{E}_{S_{p}}(\chi|_{C^{1}_{F}}) \arrow[d] \\
\Omega(C_{F})(\chi|_{C^{1}_{F}}) \arrow[r, "j"'] & X(\chi|_{C^{1}_{F}}) & \mathcal{U}_{S_{\infty}} \coprod (\coprod^{\prime}_{p} \mathcal{U}_{S_{p}}) \arrow[l, "i"]
\end{tikzcd}
```

where $X(\chi|_{C^{1}_{F}})$ is a completion of the connected component $\Omega(C_{F})(\chi|_{C^{1}_{F}})$ with boundary divisor $\mathcal{U}_{S_{\infty}} \coprod (\coprod_{p} \mathcal{U}_{S_{p}})$.

In all four diagrams (8.4.0.6), (8.4.0.7), (8.4.0.8) and (8.4.0.9), the notation $\coprod^{\prime}$ denotes the coproduct
over only those places at which $\chi_{S}$, respectively $\chi$, is unramified.

Remark 8.4.0.1. The topological spaces $X_{S}(\chi_{S}|_{J^{1}_{F,S}})$ and $X(\chi|_{C^{1}_{F}})$ can be assembled together into families
parametrized by the discrete character groups $\widehat{J^{1}_{F,S}}$, respectively $\widehat{C^{1}_{F}}$:
$$p_{S} : \mathcal{X}_{S} \to \widehat{J^{1}_{F,S}}, \quad p : \mathcal{X} \to \widehat{C^{1}_{F}}.$$
The boundaries of $X_{S}(\chi_{S}|_{J^{1}_{F,S}})$ and $X(\chi|_{C^{1}_{F}})$ also relativize over $\widehat{J^{1}_{F,S}}$, respectively $\widehat{C^{1}_{F}}$.

The vertical arrows in (8.4.0.6), (8.4.0.7), (8.4.0.8), respectively (8.4.0.9), are not morphisms, but rather
merely refer to the intuition, guided by Theorem 8.1.0.1 and Theorem 7.3.4.1(4), that each nuclear Fréchet space
in the top row of each diagram respectively, should be thought of as a Fréchet bundle over the corresponding
quotient stack in the bottom row, respectively topological space/divisor.

The idelic Mellin transform, both $S$-local and global, sets up a correspondence between closed substacks of
the quotient stacks $[D_{F,S}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}]$, respectively boundary divisors of $X_{S}(\chi_{S}|_{J^{1}_{F,S}})$, and $[D_{F}/\mathrm{GL}_{1}(\mathbf{A}_{F})^{1}]$,
respectively boundary divisors of $X(\chi|_{C^{1}_{F}})$.

We now refocus on the $S$-local Fréchet spaces in the diagram from (8.4.0.6).

They all carry compatible continuous left-translation actions by $J_{F,S}$, and hence by convolution under the
convolution algebra $\mathcal{D}(J_{F,S})$.

We denote by $E$ any of the three Fréchet spaces in the top row of (8.4.0.6).

For each $\varphi \in \mathcal{D}(J_{F,S})$:
$$A(\varphi) : E \to E$$
defined as $u \mapsto A(\varphi)(u) := \int_{J_{F,S}} \varphi(g) u(g^{-1}x) \, \mathrm{d}\overline{\mu}_{S}(g)$ is a continuous linear endomorphism, which, on $E =$
$\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S}))$, admits an integral kernel, namely
$$\varphi(xy^{-1}) : J_{F,S} \times J_{F,S} \to \mathbf{C}$$

## PDF page 392

392
CHAPTER 8.
PERIODIC ORBITS AND FIXED POINTS

by identifying $\Phi_{F,S}(\mathcal{S}_{00}(\mathbf{A}_{F,S}))$, equipped with the quotient topology inherited from $\mathcal{S}_{00}(\mathbf{A}_{F,S})$, with a copy
of the regular representation of $J_{F,S}$ on $\mathcal{S}_{\mathrm{E}}(J_{F,S})$.

We now assume $\varphi$ is supported over the closed semigroup $J^{\ge 1}_{F,S}$ of $S$-idele classes of $S$-idelic norm at least
$1$.

Then $\varphi(1) = 0$ by smoothness of $\varphi$, and hence the kernel of $A(\varphi)$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S}))$ vanishes
along the diagonal.

We will now proceed with a discussion aimed at fostering intuition for certain constructions and arguments
to be carried out in Chapter 6 and Chapter 7.

While $A(\varphi)$ is not a nuclear operator on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S}))$, nor on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$, it is
so on most of the Orbital subquotients, namely, it is so on $\mathscr{E}_{S,S_{p}}(\chi_{S}|_{J^{1}_{F,S}})$ for every prime $p$ such that $S_{p} \subset S$,
by Theorem 7.4.2.1.

It also has a convergent matrix trace on $\mathscr{E}_{S,S_{\infty}}(\chi_{S}|_{J^{1}_{F,S}})$ (this is where we use the assumption on the
support on $\varphi$, through Theorem 7.4.3.2).

While not nuclear, it has a trace even on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S}))$, which is zero by the above observation
on the integral kernel of $A(\varphi)$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S}))$.

The effect the continuous left-translation action of $J^{\ge 1}_{F,S}$ is, in a way, “small” and controlled along the
diagonal over $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S}))$, and mostly concentrated over the orbital subquotients, on each of
which its trace is computable explicitly, for each test function $\varphi \in \mathcal{D}(J_{F,S})$ supported over $J^{\ge 1}_{F,S}$.

We note that the quotient stacks $BU_{v} \simeq [D_{S,v}/F^{\times}_{v}]$, for each Archimedean place $v \in S$, are now promoted
to “basins of attraction” by the condition on the support that we have imposed on test functions. Namely, on
the level of coarse spaces, the continuous left-translation action by $J_{F,S}$ on the (non-Hausdorff) coarse space
of the quotient stack $[D_{F,S}/\mathrm{GL}_{1}(\mathbf{A}_{F,S})^{1}]$, promotes the finitely many points underlying the stacks $BU_{v}$, to
attractive limit points under the action of $\mathbf{R}^{\ge 1}_{>0} \simeq J^{\ge 1}_{F,S}/J^{1}_{F,S}$.

The quotient stacks $[D_{S,v}/F^{\times}_{v}] \simeq [\mathbf{R}_{>0}/F^{\times}_{v}]$ for each non-Archimedean place $v \in S$, are instead promoted
to periodic orbits: namely, on the level of coarse spaces, the continuous left-translation action by $J^{\ge 1}_{F,S}$ preserves
them.

The trace of $A(\varphi)$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$ will be defined and computed rigorously only in Chapter 7.

We can proceed heuristically and combine the calculations performed in Theorem 7.4.2.1 and Theorem
7.4.3.2, to infer that its value will be:
$$\mathrm{Trace}(A(\varphi)) = \sum_{p:S_{p}\subset S} \sum_{\varepsilon_{p}} N(\chi_{S}|\cdot|^{\varepsilon_{p}}_{F,S}) \int_{J_{F,S}} \varphi(g) \chi_{S}(g) |g|^{\varepsilon_{p}}_{F} \, \mathrm{d}\overline{\mu}_{S}(g) \tag{8.4.0.10}$$
$$+ \sum_{z} N(\chi_{S}|\cdot|^{z}_{F,S}) \int_{J_{F,S}} \varphi(g) \chi_{S}(g) |g|^{z}_{F} \, \mathrm{d}\overline{\mu}_{S}(g) \tag{8.4.0.11}$$
where $\varepsilon_{p}$ varies over the poles of $\prod_{v \in S_{p}} L_{v}(\chi_{v}|\cdot|^{s}_{v})$, for each prime $p$ such that $S_{p} \subset S$, and $z$ varies over
the poles of the $\Gamma$-factor of the Hecke $L$-function $L(s,\chi)$, $N(\chi_{S}|\cdot|^{\varepsilon_{p}}_{F,S})$ and $N(\chi_{S}|\cdot|^{z}_{F,S})$ being the respective
multiplicity functions.

The reader will now recognize, through the lens of the Poisson Summation Formula (in its form from
Proposition B.4.1.2) and the Asymptotic Residue Theorem (see Theorem B.3.2.1 and Theorem B.4.2.2), the
geometric side of Weil’s Explicit Formulas, namely:
$$\sum_{v \in S_{f}-S_{\chi}} \sum_{m>0} \frac{\log N(\mathfrak{p}_{v})}{N(\mathfrak{p}_{v})^{m/2}} \{\chi(\mathfrak{p}^{m}_{v}) \varphi(N(\mathfrak{p}_{v})^{m}) + \overline{\chi}(\mathfrak{p}^{m}_{v}) \varphi(N(\mathfrak{p}_{v})^{-m})\} \tag{8.4.0.12}$$
$$- \sum_{v \in S_{\infty}} \int^{+\infty}_{0} \left\{ \frac{N_{v}\phi(1)}{x} - (\phi(e^{x})e^{s_{v}x} + \phi(e^{-x})e^{-s_{v}x}) \frac{e^{(\frac{2}{N_{v}}-\frac{1}{2})x}}{1-e^{-\frac{2}{N_{v}}x}} \right\} \mathrm{d}x \tag{8.4.0.13}$$

## PDF page 393

8.4.
ORBITAL TRACES
393

which agrees with the right side of (8.4.0.10) applied to $\varphi|\cdot|^{-1/2}_{F,S}$.

We further refer the reader to [Den, Thm.1.7(4)], where Deninger formulated expectations that a trace-
theoretic interpretation to Weil’s Explicit Formulas for Hecke $L$-functions could be taking the form presented,
so far only heuristically, in (8.4.0.10).

We have so far learned that the continuous left-translation action of $J_{F,S}$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$ is,
when restricted to an action of the closed semigroup $J^{\ge 1}_{F,S}$, traceable, in a sense to be made rigorous within the
next two Chapters, and the Orbital Schauder bases identified throughout this Chapter enable us to compute
the trace explicitly.

We now explain how the Paley-Wiener levels fit into this scenario.

It is a consequence of the classical Paley-Wiener Theorem, that the intersection of
$$\mathrm{PW}_{S,X}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}(\mathbf{A}_{F,S^{\prime}}))$$
with $S^{\prime} = S \cup S_{0}$ for some saturated finite set of finite places $S_{0}$ of $F$, with $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}_{00}(\mathbf{A}_{F,S}))$, is
trivial for all large enough $X > 0$. This is so, because the only Schwartz-Bruhat function $f \in \mathcal{S}(\mathbf{A}_{F,S_{\infty}})$ whose
$S_{\infty}$-adelic Fourier transform is compactly supported, and that vanishes at any of the hyperplanes $\{x_{v} = 0\}$,
$v \in S_{\infty}$, with infinite order, is constant with value zero.

We may therefore complete the diagram in (8.4.0.6) into the following:

(8.4.0.14)

```latex
\begin{tikzcd}
0 \arrow[r] \arrow[d] & \mathrm{PW}_{S,X}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}(\mathbf{A}_{F,S^{\prime}})) \arrow[r] \arrow[d] & \mathscr{E}_{S^{\prime},S_{\infty}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}) \times \prod^{\prime}_{p:S_{p}\subset S^{\prime}} \mathscr{E}^{\mathrm{ABS}}_{S^{\prime},S_{p},X}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}) \arrow[d] \\
\mathrm{H}_{0,\mathrm{cont}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}_{00}(\mathbf{A}_{F,S^{\prime}})) \arrow[r] \arrow[d] & \mathrm{H}_{0,\mathrm{cont}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}(\mathbf{A}_{F,S^{\prime}})) \arrow[r] \arrow[d] & \mathscr{E}_{S^{\prime},S_{\infty}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}) \times \prod^{\prime}_{p:S_{p}\subset S^{\prime}} \mathscr{E}_{S^{\prime},S_{p}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}) \arrow[d] \\
{[D_{S^{\prime},1}/\mathrm{GL}_{1}(\mathbf{A}_{F,S^{\prime}})^{1}]} \arrow[r, "j"'] \arrow[d, "\simeq"'] & {[D_{F,S^{\prime}}/\mathrm{GL}_{1}(\mathbf{A}_{F,S^{\prime}})^{1}]} & \coprod^{\prime}_{v \in S^{\prime}} [D_{S^{\prime},v}/\mathrm{GL}_{1}(\mathbf{A}_{F,S^{\prime}})^{1}] \arrow[d, "\simeq"] \arrow[l, "i"] \\
\underline{J_{F,S^{\prime}}/J^{1}_{F,S^{\prime}}} &  & \left(\coprod_{v \in S_{\infty}} BU_{v}\right) \coprod \left(\coprod_{p:S_{p}\subset S^{\prime}} \coprod^{\prime}_{v \in S_{p}} [\mathbf{R}_{>0}/F^{\times}_{v}]\right)
\end{tikzcd}
```

for all large enough $X > 0$.

The content of Theorem 7.3.3.4 is that the Orbital subquotients
$$\mathscr{E}^{\mathrm{ABS}}_{S^{\prime},S_{p},X}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}})$$
inherit the Orbital Schauder bases from $\mathscr{E}_{S^{\prime},S_{p}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}})$ for all $X > 0$ large enough, and the directed union
of the $\mathrm{PW}_{S,X}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}(\mathbf{A}_{F,S^{\prime}}))$ is sequentially dense within $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}(\mathbf{A}_{F,S^{\prime}}))$.

This means that the Paley-Wiener levels retain knowledge of the trace of $A(\varphi)$ asymptotically as $X \to +\infty$,
missing exactly the closed subspace $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}_{00}(\mathbf{A}_{F,S^{\prime}}))$ which is the main cause of the non-nuclearity
of $A(\varphi)$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}(\mathbf{A}_{F,S^{\prime}}))$.

We are going to use the Paley-Wiener levels, in their invariant form (see Definition 7.3.2.3), in the next
two Chapters, to define and compute the trace of $A(\varphi)$ rigorously, doing so with respect to coarser normed
topologies on the ambient $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}_{00}(\mathbf{A}_{F,S^{\prime}}))$, than its intrinsic nuclear Fréchet space topology.

A choice of test function $\varphi \in \mathcal{D}(C_{F})$, which we again assume supported over the closed semigroup $C^{\ge 1}_{F}$,
induces a test function $\varphi_{S} \in \mathcal{D}(J_{F,S})$ for all large enough $S$. Indeed, for $S$ any finite set of places of $F$
containing all the Archimedean places, such that $\chi$ is unramified outside $S$, and with $\mathrm{Pic}(\mathcal{O}_{F,S}) = 1$, we have
that $\varphi$ is $k$-invariant for $k \subset C_{F}$ a compact subgroup with open compactly generated orthogonal $k^{\perp} \subset \widehat{C_{F}}$.

## PDF page 394

394
CHAPTER 8.
PERIODIC ORBITS AND FIXED POINTS

In particular, $\varphi$ is invariant under the compact subgroup given by the image in $C_{F}$ of $\widehat{\mathcal{O}}^{\times}_{\Sigma_{F}-S^{\prime}} \subset \mathrm{GL}_{1}(\mathbf{A}_{F})$
for all large enough $S^{\prime}$. Upon replacing $S^{\prime}$ with a larger set $S^{\prime}$ if necessary, so as to have that $\chi$ is unramified
outside $S^{\prime}$ and $\mathrm{Pic}(\mathcal{O}_{F,S^{\prime}}) = 1$, we may descend $\varphi$ to a unique $\varphi_{S^{\prime}} \in \mathcal{D}(J_{F,S^{\prime}})$ and $A(\varphi_{S^{\prime}})$ acts on
$$\mathrm{H}_{0,\mathrm{cont}}(\chi_{S^{\prime}}|_{J^{1}_{F,S^{\prime}}}, \mathcal{S}(\mathbf{A}_{F,S^{\prime}}))$$
compatibly with the action of $A(\varphi)$ on the global $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^{1}_{F}}, \mathcal{S}(\mathbf{A}_{F}))$ under the transition operator $\overline{\pi}_{S^{\prime}}$,
which, under the above conditions on $S^{\prime}$, is a linear topological isomorphism.

We conclude this Chapter by observing that as $S$ grows to encompass all places of $F$, the trace of $A(\varphi_{S})$
stabilizes in finite time, i.e. for all large enough finite sets of finite places $S^{\prime}$ of $F$ containing all the Archimedean
places, the trace of $A(\varphi_{S^{\prime}})$ remains constant with respect to $S^{\prime}$. The largeness of $S^{\prime}$ depends on the character
$\chi$ and on the support of the test function $\varphi \in \mathcal{D}(C_{F})$.

We are led to eyeball the following situation: the continuous operator $A(\varphi)$ on $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^{1}_{F}}, \mathcal{S}(\mathbf{A}_{F}))$ is
traceable. Its trace will be defined rigorously in the next two Chapters, for then to be computed in Chapter 7.
Its trace is concentrated at the $S$-local level, on the orbital subquotients of $\mathrm{H}_{0,\mathrm{cont}}(\chi_{S}|_{J^{1}_{F,S}}, \mathcal{S}(\mathbf{A}_{F,S}))$, for
$S$ large enough.

The Paley-Wiener levels approximate the orbital subquotients from within, filling them in asymptotically,
and they inhert the full Orbital Schauder bases on the primary Orbital quotients.

At the global level, the topologically short exact sequence:
$$0 \to \mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^{1}_{F}}, \mathcal{S}_{0}(\mathbf{A}_{F})) \to \mathcal{S}_{\mathrm{E}}(C_{F})(\chi|_{C^{1}_{F}}) \to \mathscr{H}_{F}(\chi|_{C^{1}_{F}}) \to 0$$
leads to computing the trace of $A(\varphi)$ by computing the trace of operators induced by the continuous
left-translation action of $C_{F}$ on the spectral subquotient $\mathscr{H}_{F}(\chi|_{C^{1}_{F}})$ (see Theorem 7.4.1.1).

This is a first look into the elements that enter the trace calculation in Chapter 7. The idea is to perform
it not within the nuclear Fréchet spaces from above, but rather within normed completions, whose topology is
much coarser.

The mere fact that the trace calculation can be performed with respect to such coarser topologies, is
what puts constraints on the zeros that are allowed to contribute to the spectral side of the trace formula:
only some of the point-evaluation functionals from (7.1.4.6) of Theorem 7.1.4.2, will remain continuous with
respect to coarser normed topologies, and only those, will be contributing to the spectral side.

It turns out that the coarsest possible normed completion of $\mathrm{H}_{0,\mathrm{cont}}(\chi|_{C^{1}_{F}}, \mathcal{S}_{0}(\mathbf{A}_{F}))$ which enables the
trace calculation, is a Sobolev completion of degree $2[F:\mathbf{Q}]$. We will be studying these Sobolev completions
in the next Chapter.

The Orbital Schauder bases on the Paley-Wiener levels will remain in place after such normed completions,
turning into Markushevich bases. They will enable us to reduce the trace calculation into a calculation to be
done $S$-locally only, as opposed to globally, and this is where the choice of Sobolev degree $2[F:\mathbf{Q}]$ is forced
on us: it ensures the orbital Schauder bases on the absolute and invariant Paley-Wiener levels, are inherited
by the normed completions, at least in the weaker sense of Markushevich bases, insofar as all the continuous
dual basis elements remain continuous on the Sobolev completions.

8.5. The big picture
