---
title: The complexity of deciding isomorphism safe improvements under arbitrary principal preferences
date: 2026-08-16 00:00:00 +0000
math: true
how_written: >-
  I posed the high-level problem and suggested the models try to prove Proposition 12 in its current form. (They initially proved a much weaker result.) I somewhat carefully verified the results, especially Section 3 and 4, but mostly didn't check the proofs line by line. The results are mostly intuitive. I also had a few models triple-check the correctness of the results.
---

**Summary.** Let ISI be the problem of deciding, given explicit normal-form games $$G$$ (default) and $$G'$$ (new) and an explicitly represented preference relation $$R$$, whether (a) the reduced games $$\bar G$$ and $$\bar G'$$ are isomorphic and (b) *every* isomorphism $$\varphi\colon \bar G \to \bar G'$$ satisfies $$(\varphi(y), y) \in R$$ for every outcome $$y$$ of $$\bar G$$. (Here $$\bar\Gamma$$ denotes the maximal reduction of $$\Gamma$$ by iterated elimination of strictly dominated strategies.)

**Main theorem.** ISI is complete, under polynomial-time reductions, for $$\mathrm{D(GI)}$$, the second level of the difference (Boolean) hierarchy over graph isomorphism:

$$
\mathrm{D(GI)} = \{L : \exists\ \text{polynomial-time computable } f,g\ \forall z:\ z \in L \iff f(z) \in \mathrm{GI} \wedge g(z) \notin \mathrm{GI}\},
$$

where $$\mathrm{GI}$$ is identified with its language of yes-instances (pairs of isomorphic graphs). Equivalently, ISI is interreducible with the four-graph problem $$\{(X,X',Y,Y') : X \cong X' \wedge Y \not\cong Y'\}$$. Hardness holds already for two-player common-payoff games having neither duplicate strategies nor strategies weakly or strictly dominated by distinct pure or mixed strategies; it also holds with a single principal whose utility takes only two values and with exactly one pair of outcomes outside $$R$$.

In particular, ISI is both GI-hard and coGI-hard. So, unlike the Pareto case, ISI is not GI-complete unless the class of problems reducible to GI is closed under complement. At the same time it stays close to GI from above: it lies in $$\mathrm{DP}$$, it is decidable with two nonadaptive GI-oracle queries (hence, e.g., in quasipolynomial time), NP- or coNP-hardness — even under Turing reductions — would collapse the polynomial hierarchy to $$\Sigma_2^p$$ (Theorem 10), and $$\mathrm{ISI} \in \mathrm{P}$$ iff $$\mathrm{GI} \in \mathrm{P}$$.

Context in the literature: deciding whether a given candidate is a safe improvement is GI-complete in the coupled Pareto case (Sauerberg and Oesterheld, 2026); the quantifier collapse behind that result fails for arbitrary $$R$$, while §6 studies the Aut-invariant regime — of which payoff-defined preferences are an important subclass — in which the collapse is restored. Safe improvement w.r.t. arbitrary preferences over finite, *explicitly represented* binary constraint structures is coNP-complete under a satisfiability promise (Oesterheld and Conitzer, 2025); with isomorphism-*generated* constraints the complexity thus lands strictly in between, under standard assumptions.

---

## 1. Problem statement

**Games and reduction.** A (finite, $$n$$-player) game is $$\Gamma = (A, u)$$ with $$A = A_1 \times \cdots \times A_n$$, each $$A_i$$ a finite nonempty strategy set, and $$u_i\colon A \to \mathbb{Q}$$ given as explicit payoff tables. Elements of $$A$$ are *outcomes*. Following Sauerberg and Oesterheld (2026), we write $$\bar\Gamma$$ for the unique maximal reduction of $$\Gamma$$ under iterated elimination of pure strategies strictly dominated by another pure strategy of the same player; this is order-independent (Gilboa et al., 1990; Apt, 2004), and $$\bar\Gamma$$ is again a nonempty product game. The reduction is always computable in polynomial time: each round compares pairs of a player's strategies directly on the explicit payoff tables and either eliminates a strategy or halts, so there are at most $$\sum_i (\vert A_i\vert  - 1)$$ rounds. (The same holds when strict dominance by mixed strategies is allowed, each dominance check then being a single linear program; see Conitzer and Sandholm, 2005.)

**Isomorphism.** Following Oesterheld and Conitzer (2022), an isomorphism between same-player-count games $$\Gamma = (A, u)$$ and $$\Gamma' = (A', u')$$ is a tuple $$\Phi = (\Phi_i)_{i \le n}$$ of bijections $$\Phi_i\colon A_i \to A'_i$$ such that there exist $$\lambda \in \mathbb{R}_{>0}^n$$, $$c \in \mathbb{R}^n$$ with

$$
u_i(a) = \lambda_i \, u'_i(\Phi(a)) + c_i \qquad \text{for all players } i \text{ and outcomes } a,
$$

where $$\Phi(a) := (\Phi_1(a_1), \dots, \Phi_n(a_n))$$. So isomorphisms are player-preserving and preserve each player's utility up to a player-specific positive affine transformation.

**Preferences.** The principals' preferences are an arbitrary binary relation $$R \subseteq A' \times A$$, given explicitly as a 0/1 matrix over pairs of outcomes of the two input games; $$(x, y) \in R$$ means "outcome $$x$$ of $$G'$$ is at least as good as outcome $$y$$ of $$G$$". A special case of interest: $$R$$ induced by explicit utility functions $$w_j$$ on the tagged disjoint union $$A \sqcup A'$$ of principals $$j = 1, \dots, m$$, via $$(x,y) \in R \iff w_j(x) \ge w_j(y)$$ for all $$j$$. (Tagging means $$w_j$$ may assign different values to an outcome depending on which game it is read in; when the games share outcomes one may of course also use a uniform $$w_j$$.) Our hardness results use a single principal with a two-valued $$w$$, so nothing hinges on the representation of preferences.

**The decision problem.**

> **ISI** (isomorphism safe improvement). *Input:* explicit games $$G$$ ("default") and $$G'$$ ("new") with the same number of players; explicit $$R \subseteq A' \times A$$. *Question:* do both of the following hold?
> **(a)** There exists an isomorphism $$\bar G \to \bar G'$$.
> **(b)** For every isomorphism $$\Phi\colon \bar G \to \bar G'$$ and every outcome $$y$$ of $$\bar G$$: $$(\Phi(y), y) \in R$$.

*Remark (relation to the SPI literature).* In the coupled Pareto case the principals' preferences are determined by the games' own payoffs: in the disarmament setting of Sauerberg and Oesterheld (2026), for instance, $$G'$$ is $$G$$ with some actions deleted, $$u'$$ is the corresponding restriction of $$u$$, and $$(x, y) \in R$$ iff $$u'(x) \ge u(y)$$ componentwise. Lemma 4 of Oesterheld and Conitzer (2022) shows all isomorphisms between two fixed games share the same $$(\lambda, c)$$, so the payoff vector of $$\Phi(y)$$ — and with it the Pareto comparison at $$y$$ — is the same for every isomorphism: one Pareto-improving isomorphism implies all are, the $$\forall$$ in (b) collapses to $$\exists$$, and deciding whether a *given* candidate is an SPI is GI-complete (Sauerberg and Oesterheld, 2026, Thm. 3.2). For arbitrary $$R$$ the collapse fails — Lemma 1 below pins only the constants $$(\lambda_i, c_i)$$, not $$\Phi$$ itself — and, as we show, the complexity genuinely rises. Proposition 12 (§6) isolates the mechanism in general form (Aut-invariant preferences); Proposition 13 specializes it to preferences defined by the players' payoffs.

## 2. Background: the GI cone and its difference hierarchy

Throughout, *reduction* means polynomial-time mapping reduction (sometimes called many-one reduction): $$L \le^p L'$$ iff there is a polynomial-time computable $$f$$ with $$z \in L \iff f(z) \in L'$$ for all $$z$$. Hardness and completeness are with respect to $$\le^p$$; a few statements involve the more general polynomial-time *Turing* reductions (deciding $$L$$ by a polynomial-time algorithm with oracle access to $$L'$$), and these are always named explicitly. A *graph* is a pair $$K = (V(K), E(K))$$ with $$V(K)$$ a finite set of vertices and $$E(K)$$ a set of two-element subsets of $$V(K)$$; so all graphs here are finite and undirected, and loops and parallel edges are excluded by construction. A *colored graph* is a graph together with a map $$\chi_K$$ assigning each vertex a color. We identify $$\mathrm{GI}$$ with the graph-isomorphism language — the set of pairs of isomorphic graphs — and $$\mathrm{coGI}$$ with its complement. The *cone* of GI is the class $$\{L : L \le^p \mathrm{GI}\}$$ of all problems that reduce to GI (a class of languages; GI itself is complete for it). Define

$$
\mathrm{D(GI)} := \{\, L : \exists\ \text{polynomial-time computable } f, g\ \forall z:\ z \in L \iff f(z) \in \mathrm{GI} \wedge g(z) \notin \mathrm{GI} \,\}.
$$

This is the second level of the difference hierarchy over the cone of GI in the sense of Cai et al. (1988); it is the GI-analogue of $$\mathrm{DP} = \{L_1 \cap L_2 : L_1 \in \mathrm{NP},\ L_2 \in \mathrm{coNP}\}$$ (Papadimitriou and Yannakakis, 1984). $$\mathrm{D(GI)}$$ is closed under $$\le^p$$, and the four-graph problem

$$
\mathrm{4GI} := \{(X, X', Y, Y') : X \cong X' \wedge Y \not\cong Y'\}
$$

is complete for it (membership: project to the two pairs; hardness: map $$z \mapsto (f(z), g(z))$$).

We use two standard facts about GI in the main proofs.

**(F1)** Colored (vertex-labeled) graph isomorphism, where isomorphisms must map each vertex to a vertex of the same color, is interreducible with GI (Köbler et al., 1993). Colors may be arbitrary strings — ours will be tuples of rationals. To apply the standard reduction, one first replaces the strings by integers $$1, \dots, k$$, using one and the same renaming for both graphs of the instance (say, ranking all color strings that occur in either graph lexicographically); a per-graph renaming could identify distinct colors of the two graphs and thereby change which vertex maps count as color-preserving.
**(F2)** GI has polynomial-time computable *any-ary* AND- and OR-functions: given instances $$I_1, \dots, I_k$$, one can compute in polynomial time a single instance that is in $$\mathrm{GI}$$ iff all (resp. some) $$I_j$$ are; likewise for colored GI (Chang and Kadin, 1995). The any-arity is load-bearing below: we take ORs of polynomially many instances.

## 3. Upper bound: ISI ∈ D(GI)

Throughout this section, fix an input $$z = (G, G', R)$$ and let $$\bar G = (\bar A, u)$$, $$\bar G' = (\bar A', u')$$ be the reduced games, computed in polynomial time (we reuse $$u, u'$$ for the restricted payoff functions). Let $$\bot$$ denote a fixed pair of non-isomorphic graphs (e.g. $$(K_1, K_2)$$); where a colored instance is expected, its vertices are treated as uniformly colored.

**Lemma 1 (rigidity of the affine constants).** For each player $$i$$, let $$V_i$$ and $$V'_i$$ be the multisets of values of $$u_i$$ on outcomes of $$\bar G$$ and of $$u'_i$$ on outcomes of $$\bar G'$$. Then: (i) if both $$V_i$$ and $$V'_i$$ are constant, player $$i$$'s condition is satisfied by every tuple of bijections (call $$i$$ *free*); (ii) if exactly one of them is constant, no isomorphism $$\bar G \to \bar G'$$ exists; (iii) if both are non-constant, every isomorphism $$\bar G \to \bar G'$$ has the same, uniquely determined constants

$$
\lambda_i = \frac{\max V_i - \min V_i}{\max V'_i - \min V'_i} > 0, \qquad c_i = \min V_i - \lambda_i \min V'_i .
$$

*Proof.* An isomorphism $$\Phi$$ is in particular a bijection of outcome sets, so $$V_i = \lambda_i V'_i + c_i$$ as multisets (the outcome multisets are nonempty since strategy sets are nonempty and reduction keeps them so). (i) Constants $$k_i, k'_i$$ are matched by $$\lambda_i := 1$$, $$c_i := k_i - k'_i$$. (ii) An affine image of a constant multiset is constant, and conversely $$u'_i = (u_i \circ \Phi^{-1} - c_i)/\lambda_i$$ transfers constancy back. (iii) Since $$t \mapsto \lambda_i t + c_i$$ is strictly increasing, it matches minima and maxima: $$\min V_i = \lambda_i \min V'_i + c_i$$ and $$\max V_i = \lambda_i \max V'_i + c_i$$; subtracting gives the displayed values, using $$\max V'_i > \min V'_i$$. $$\square$$

**Normalization.** If case (ii) occurs for some player, output $$(f, g) := (\bot, \bot)$$ and halt (correct: (a) fails). Otherwise, for each non-free player $$i$$ replace $$u'_i$$ on $$\bar G'$$ by $$\hat u'_i := \lambda_i u'_i + c_i$$ with the constants of Lemma 1(iii), and record which players are free.

**Lemma 2.** The replacement does not change the set of isomorphisms $$\bar G \to \bar G'$$; and after it, every isomorphism preserves every non-free player's utility exactly $$(\lambda_i = 1, c_i = 0)$$.

*Proof.* For any bijection tuple $$\Phi$$ and any $$\mu_i > 0, d_i$$: $$u_i = \mu_i (u'_i \circ \Phi) + d_i \iff u_i = (\mu_i/\lambda_i)(\hat u'_i \circ \Phi) + (d_i - \mu_i c_i / \lambda_i)$$, and $$\mu_i/\lambda_i > 0$$; the parameter transformation is bijective, so the isomorphism conditions w.r.t. $$u'$$ and w.r.t. $$\hat u'$$ are equivalent. For the second claim: by construction, $$\min \hat V'_i = \lambda_i \min V'_i + c_i = \min V_i$$ and likewise $$\max \hat V'_i = \max V_i$$, and $$\hat V'_i$$ is non-constant. Hence, for any isomorphism of the normalized games with constants $$\alpha_i > 0$$, $$e_i$$, Lemma 1(iii) gives

$$
\alpha_i = \frac{\max V_i - \min V_i}{\max \hat V'_i - \min \hat V'_i} = 1, \qquad e_i = \min V_i - \min \hat V'_i = 0. \qquad \square
$$

**Encoding games as colored graphs.** For the reduced default game $$\bar G$$, let $$\mathrm{Enc}(\bar G)$$ be the colored graph with: a *strategy vertex* $$s_{i,b}$$ for each player $$i$$ and $$b \in \bar A_i$$, colored $$(\mathsf{str}, i)$$; an *outcome vertex* $$o_a$$ for each outcome $$a \in \bar A$$, colored $$(\mathsf{out}, \tilde v(a))$$, where $$\tilde v(a)$$ is the tuple of the non-free players' utilities $$u_i(a)$$, written as canonical reduced fractions; and edges $$\{o_a, s_{i, a_i}\}$$ for all $$a$$ and $$i$$. Define $$\mathrm{Enc}(\bar G')$$ the same way over the same color palette, using the normalized utilities $$\hat u'_i$$ of the non-free players. $$\mathrm{Enc}$$ has $$\vert \bar A\vert  + \sum_i \vert \bar A_i\vert $$ vertices and $$n\vert \bar A\vert $$ edges: polynomial size, with polynomial-bit-length colors (the constants of Lemma 1 are ratios of input numbers).

**Lemma 3 (faithfulness).** Color-preserving graph isomorphisms $$\mathrm{Enc}(\bar G) \to \mathrm{Enc}(\bar G')$$ correspond exactly to game isomorphisms $$\bar G \to \bar G'$$: the correspondence sends $$\Phi$$ to the map $$s_{i,b} \mapsto s_{i, \Phi_i(b)}$$, $$o_y \mapsto o_{\Phi(y)}$$, and every color-preserving isomorphism arises this way from a unique $$\Phi$$. In particular, the image of the outcome vertex $$o_y$$ under any color-preserving isomorphism is $$o_{\Phi(y)}$$ for the corresponding $$\Phi$$.

*Proof.* (⇐) Given an isomorphism $$\Phi$$, the described vertex map is a bijection, preserves strategy colors (player-preservation) and outcome colors (Lemma 2: exact preservation for non-free players), and preserves adjacency both ways since $$o_y \sim s_{i,b} \iff b = y_i \iff \Phi_i(b) = \Phi_i(y_i)$$.
(⇒) Colors force a color-preserving isomorphism $$\psi$$ to map player-$$i$$ strategy vertices bijectively to player-$$i$$ strategy vertices — giving bijections $$\Phi_i\colon \bar A_i \to \bar A'_i$$ — and outcome vertices to outcome vertices. The vertex $$o_y$$ is adjacent to exactly one strategy vertex per player, namely $$s_{i, y_i}$$; its image is an outcome vertex adjacent to exactly the $$s_{i, \Phi_i(y_i)}$$, and the unique outcome vertex with that neighborhood is $$o_{\Phi(y)}$$ (here we use that $$\bar A'$$ is a full product, so $$\Phi(y) \in \bar A'$$, and that an outcome vertex is determined by its neighborhood; two outcome vertices may share a color — harmless, as neighborhoods separate them). Color preservation at outcome vertices gives $$\tilde v(y) = \tilde v'(\Phi(y))$$, i.e. exact preservation for non-free players; free players impose no condition; so $$\Phi$$ is a game isomorphism by Lemma 2, and $$\psi$$ is exactly the map induced by $$\Phi$$. The degenerate cases are covered: for $$n = 1$$, outcome vertices are pendant on strategy vertices and the argument is unchanged; if all players are free, all outcome vertices share one color and a colored isomorphism exists iff $$\vert \bar A_i\vert  = \vert \bar A'_i\vert $$ for all $$i$$, which is exactly when a game isomorphism exists. $$\square$$

**Lemma 4 (pinning).** For $$x \in \bar A'$$, $$y \in \bar A$$, define the pinned instance $$P_{x,y}$$: if the colors of $$o_y$$ in $$\mathrm{Enc}(\bar G)$$ and $$o_x$$ in $$\mathrm{Enc}(\bar G')$$ differ, $$P_{x,y} := \bot$$; otherwise, recolor both vertices with the same fresh color $$\star$$. Then $$P_{x,y}$$ is a yes-instance of colored GI iff there is an isomorphism $$\Phi\colon \bar G \to \bar G'$$ with $$\Phi(y) = x$$.

*Proof.* If the colors differ then $$\tilde v(y) \ne \tilde v'(x)$$, and by Lemma 3 no isomorphism maps $$y$$ to $$x$$; and $$\bot \notin \mathrm{GI}$$. Otherwise: a color-preserving isomorphism of the pinned pair must map $$o_y \mapsto o_x$$ (singleton $$\star$$-classes) and, since $$\tilde v(y) = \tilde v'(x)$$, restoring the original colors turns it into a color-preserving isomorphism of the unpinned pair mapping $$o_y \mapsto o_x$$ — by Lemma 3 this is induced by a game isomorphism $$\Phi$$ with $$\Phi(y) = x$$. Conversely, the encoding of any such $$\Phi$$ is a pinned isomorphism. $$\square$$

**Theorem 5 (membership).** $$\mathrm{ISI} \in \mathrm{D(GI)}$$. Moreover, ISI is decidable with two nonadaptive queries to a GI oracle, with acceptance pattern (yes, no).

*Proof.* Define $$f(z) :=$$ the plain-GI instance obtained from the pair $$(\mathrm{Enc}(\bar G), \mathrm{Enc}(\bar G'))$$ via (F1). By Lemma 3, $$f(z) \in \mathrm{GI} \iff$$ condition (a).

Condition (b) fails iff there exist $$x \in \bar A'$$, $$y \in \bar A$$ with $$(x, y) \notin R$$ and some isomorphism mapping $$y$$ to $$x$$. There are at most $$\vert \bar A'\vert  \cdot \vert \bar A\vert $$ such pairs — polynomially many. Let $$g(z) :=$$ the plain-GI instance obtained by combining all pinned instances $$\{P_{x,y} : (x,y) \notin R,\ x \in \bar A',\ y \in \bar A\}$$ with the any-ary OR-function (F2) and converting via (F1); if the set is empty, $$g(z) := \bot$$. By Lemma 4 and (F2), $$g(z) \in \mathrm{GI} \iff \neg$$(b).

Then $$z \in \mathrm{ISI} \iff f(z) \in \mathrm{GI} \wedge g(z) \notin \mathrm{GI}$$. In particular, if no isomorphism exists at all, every pinned instance is negative, so $$g(z) \notin \mathrm{GI}$$ — (b) holds vacuously — while $$f(z) \notin \mathrm{GI}$$ correctly forces NO. Both maps are polynomial-time, giving $$\mathrm{ISI} \in \mathrm{D(GI)}$$ and the two-query algorithm. $$\square$$

## 4. Lower bound: ISI is D(GI)-hard

The engine is a generic encoding of colored graphs into common-payoff games whose isomorphisms are exactly the color-preserving graph isomorphisms.

**Definition (graph games).** Fix a finite color set $$C$$ and an injective *level function* $$d\colon C \to \{2, 3, \dots\}$$. For a colored graph $$K$$ with colors $$\chi_K\colon V(K) \to C$$, let $$\mathcal{G}(K)$$ be the two-player game in which both players' strategy set is $$V(K)$$ and both players receive the common payoff

$$
M_K(v, w) \;=\; \begin{cases} d(\chi_K(v)) & \text{if } v = w,\\ 1 & \text{if } v \ne w,\ \{v,w\} \in E(K),\\ 0 & \text{otherwise.} \end{cases}
$$

$$M_K$$ is symmetric, with values in $$\{0, 1\} \cup d(C)$$.

**Lemma 6 (graph games are rigid and faithful).** Let $$K, L$$ be colored graphs over the same palette $$C$$ with level function $$d$$. Then:

(i) $$\mathcal{G}(K)$$ has no duplicate strategies and no strategy weakly or strictly dominated by any distinct pure or mixed strategy. Hence it is unchanged by iterated elimination of strictly dominated strategies, by iterated elimination of weakly dominated strategies, and by deletion of duplicate strategies; in particular, $$\overline{\mathcal{G}(K)} = \mathcal{G}(K)$$.
(ii) Suppose (H1) each of $$K, L$$ contains two distinct non-adjacent vertices, and (H2) the maximum level $$\max_v d(\chi(v))$$ present is the same in both, say $$D$$. Then the isomorphisms $$\mathcal{G}(K) \to \mathcal{G}(L)$$ are exactly the pairs $$\Phi_1 = \Phi_2 = \psi$$ where $$\psi\colon K \to L$$ is a color-preserving graph isomorphism; every such isomorphism has $$\lambda = (1,1)$$, $$c = (0,0)$$, and maps the outcome $$(s, t)$$ to $$(\psi(s), \psi(t))$$.

*Proof.* (i) Consider any row strategy $$v$$ and any mixed strategy $$\mu \ne \delta_v$$. At column $$v$$: row $$v$$ earns $$M_K(v,v) = d(\chi_K(v)) \ge 2$$, while every other row $$w \ne v$$ earns $$M_K(w, v) \le 1$$; hence $$\mathbb{E}_\mu[M_K(\cdot, v)] \le \mu(v)\, d(\chi_K(v)) + (1 - \mu(v)) \cdot 1 < d(\chi_K(v))$$. So no mixed (a fortiori no pure) strategy weakly or strictly dominates $$v$$, and distinct rows differ at their diagonal columns, so there are no duplicates. Columns are symmetric because $$M_K$$ is symmetric and payoffs are common.

(ii) Let $$(\Phi_1, \Phi_2)$$ be an isomorphism $$\mathcal{G}(K) \to \mathcal{G}(L)$$ with constants $$(\lambda_i, c_i)$$. The outcome map is a bijection $$V(K)^2 \to V(L)^2$$, so payoff multisets transform affinely; by (H1) the minimum value $$0$$ occurs in both games (an ordered pair of distinct non-adjacent vertices), and the maximum is $$D$$ in both (diagonal levels beat all off-diagonal values since $$D \ge 2 > 1$$, and (H2)); with common payoffs both players share the same value multiset, so Lemma 1(iii) gives $$\lambda_i = 1, c_i = 0$$, i.e. $$M_K(s,t) = M_L(\Phi_1(s), \Phi_2(t))$$ for all $$s, t$$. At $$t = s$$: $$M_K(s,s) \ge 2$$, and the only entries of $$M_L$$ exceeding $$1$$ are diagonal, so $$\Phi_1(s) = \Phi_2(s) =: \psi(s)$$. Then $$d(\chi_K(s)) = d(\chi_L(\psi(s)))$$ forces $$\chi_K = \chi_L \circ \psi$$ ($$d$$ injective), and for $$s \ne t$$, $$M_K(s,t) \in \{0,1\}$$ equals $$M_L(\psi(s), \psi(t))$$, so $$\psi$$ preserves adjacency and non-adjacency: a color-preserving graph isomorphism. Conversely, any such $$\psi$$ yields the game isomorphism $$(\psi, \psi)$$ with $$\lambda = 1, c = 0$$. $$\square$$

**The construction.** Fix the palette $$C = \{\mathsf{E}, \mathsf{B}, \mathsf{P}, \mathsf{Z}\}$$ with levels $$d(\mathsf{E}) = 2$$, $$d(\mathsf{B}) = 3$$, $$d(\mathsf{P}) = 4$$, $$d(\mathsf{Z}) = 5$$. For graphs $$H$$ (the "test part") and $$W, W'$$ (the "switch parts"), define the colored graph

$$
K(H; W, W') := H_{\mathsf{E}} \ \sqcup\ \mathrm{cone}_p(W) \ \sqcup\ \mathrm{cone}_q(W') \ \sqcup\ \{r\},
$$

where: $$H_{\mathsf{E}}$$ is a copy of $$H$$ with all vertices colored $$\mathsf{E}$$; $$\mathrm{cone}_p(W)$$ is a copy of $$W$$ with all vertices colored $$\mathsf{B}$$, plus a fresh apex $$p$$ colored $$\mathsf{P}$$ adjacent to every vertex of $$W$$; $$\mathrm{cone}_q(W')$$ is a copy of $$W'$$ with all vertices colored $$\mathsf{B}$$, plus a fresh apex $$q$$, also colored $$\mathsf{P}$$, adjacent to every vertex of $$W'$$; and $$r$$ is an isolated vertex colored $$\mathsf{Z}$$. No other edges. When two such graphs are used together below, they are taken to be vertex-disjoint, with the names $$p$$, $$q$$, $$r$$ reused for the corresponding vertices of each; in particular, the two games built from them share no outcomes. Note that (H1) holds ($$p, q$$ are distinct and non-adjacent) and the maximum level present is always $$5$$ (vertex $$r$$), so Lemma 6(ii) applies to every pair of such graphs. Since $$p$$ and $$q$$ share the color $$\mathsf{P}$$, color-preserving isomorphisms may exchange them; Lemma 7(ii) below determines exactly when one does.

![Figure 1](/assets/img/the-complexity-of-deciding-isomorphism-safe-improvements-under-arbitrary-principal-preferences-fig1.svg){: width="700" height="240" }
*The colored graph $$K(H; W, W')$$, schematically. The dashed regions carry copies of the input graphs $$H, W, W'$$ with their own (arbitrary) edges; each apex is adjacent to every vertex of its cone body; there are no other edges — in particular none between the four parts, and $$r$$ is isolated.*

**Plan.** We reduce an instance $$(X, X', Y, Y')$$ of $$\mathrm{4GI}$$ to ISI by taking $$G := \mathcal{G}(K(X; Y, Y'))$$ as the default game, $$G' := \mathcal{G}(K(X'; Y, Y'))$$ as the new game, and a preference relation with exactly one pair outside $$R$$, namely $$\big((q,q), (p,p)\big)$$; condition (b) then fails exactly if some isomorphism maps $$(p,p)$$ to $$(q,q)$$. The games are unchanged by reduction (Lemma 6(i)), and their isomorphisms are exactly the color-preserving graph isomorphisms $$\psi\colon K(X; Y, Y') \to K(X'; Y, Y')$$, acting on outcomes by $$(s,t) \mapsto (\psi(s), \psi(t))$$ (Lemma 6(ii)). The two graphs differ only in their test parts, so such a $$\psi$$ exists iff $$X \cong X'$$ — this settles condition (a) — and a $$\psi$$ exchanging the apexes $$p, q$$ exists iff in addition the cone bodies satisfy $$Y \cong Y'$$ (both claims are Lemma 7 below). The constructed instance is therefore a yes-instance iff $$X \cong X' \wedge Y \not\cong Y'$$. The isolated vertex $$r$$ has no role beyond securing (H2) for every pair of constructed graphs.

**Lemma 7.** For any graphs $$X, X', Y, Y'$$, let $$K_{\mathrm{old}} := K(X; Y, Y')$$ and $$K_{\mathrm{new}} := K(X'; Y, Y')$$. Then:
(i) $$K_{\mathrm{old}} \cong K_{\mathrm{new}}$$ (color-preservingly) $$\iff X \cong X'$$.
(ii) There is a color-preserving isomorphism $$\psi\colon K_{\mathrm{old}} \to K_{\mathrm{new}}$$ with $$\psi(p) = q$$ $$\iff X \cong X' \wedge Y \cong Y'$$.

*Proof.* Colors confine any color-preserving isomorphism $$\psi$$: $$\mathsf{E}$$-vertices map to $$\mathsf{E}$$-vertices (so $$\psi$$ restricts to an isomorphism $$X \to X'$$, as $$\mathsf{E}$$-vertices have edges only inside the test part); $$r \mapsto r$$; and $$\{p, q\} \to \{p, q\}$$. Since $$\psi(N(p)) = N(\psi(p))$$, and in both graphs $$N(p)$$ is the $$Y$$-copy while $$N(q)$$ is the $$Y'$$-copy: $$\psi(p) = p$$ forces $$\psi$$ to map the $$Y$$-cone body onto the $$Y$$-cone body and (then $$\psi(q) = q$$) the $$Y'$$-cone body onto the $$Y'$$-cone body — isomorphisms $$Y \cong Y$$, $$Y' \cong Y'$$, always available via the name-preserving bijections; $$\psi(p) = q$$ forces isomorphisms $$Y \cong Y'$$ and $$Y' \cong Y$$. (i) ⇒: restriction to the $$\mathsf{E}$$-part. ⇐: extend an isomorphism $$X \cong X'$$ by the name-preserving bijections on the cones and $$r$$. (ii) ⇒: as just argued, $$\psi(p) = q$$ gives $$Y \cong Y'$$, and the $$\mathsf{E}$$-part gives $$X \cong X'$$. ⇐: given $$h\colon Y \cong Y'$$ and $$e\colon X \cong X'$$, let $$\psi := e$$ on the test part, $$\psi(p) := q$$, $$\psi := h$$ on the $$Y$$-cone body, $$\psi(q) := p$$, $$\psi := h^{-1}$$ on the $$Y'$$-cone body, $$\psi(r) := r$$. $$\square$$

Note that Lemma 7 needs no assumptions on $$X, X', Y, Y'$$: they may be empty, of different sizes, disconnected, or complete. (If $$Y = Y' = \varnothing$$, the cones are bare apexes and swapping $$p, q$$ is available — consistent with $$Y \cong Y'$$.)

**Theorem 8 (hardness).** $$\mathrm{4GI} \le^p \mathrm{ISI}$$. Moreover, the produced instances have: two players; common agent payoffs with values in $$\{0, 1, 2, 3, 4, 5\}$$; no duplicate strategies and no strategies weakly or strictly dominated by distinct pure or mixed strategies; $$R$$ induced by a single principal's two-valued utility $$w$$; and exactly one pair of outcomes outside $$R$$.

*Proof.* Given $$(X, X', Y, Y')$$, construct:

$$
K_{\mathrm{old}} := K(X; Y, Y'), \quad K_{\mathrm{new}} := K(X'; Y, Y'), \qquad G := \mathcal{G}(K_{\mathrm{old}}), \quad G' := \mathcal{G}(K_{\mathrm{new}}).
$$

Both games contain outcomes named $$(p,p)$$ and $$(q,q)$$, each formed from its own apexes; the two outcome sets are disjoint. Define the principal's utility $$w$$ on $$A \sqcup A'$$ by: on the $$A$$ (default) side, $$w((p,p)) := 1$$ and $$w := 0$$ otherwise; on the $$A'$$ (new) side, $$w((q,q)) := 0$$ and $$w := 1$$ otherwise. Let $$R := \{(x, y) : w(x) \ge w(y)\}$$. Then the unique pair outside $$R$$ is $$(x^\star, y^\star) := \big((q,q),\, (p,p)\big)$$.

By Lemma 6(i), $$\bar G = G$$ and $$\bar G' = G'$$. By Lemma 6(ii) and Lemma 7(i), condition (a) holds iff $$X \cong X'$$. Condition (b) fails iff some isomorphism maps $$y^\star$$ to $$x^\star$$; by Lemma 6(ii) an isomorphism maps $$(p,p) \mapsto (\psi(p), \psi(p))$$, so this happens iff there is a color-preserving $$\psi\colon K_{\mathrm{old}} \to K_{\mathrm{new}}$$ with $$\psi(p) = q$$, which by Lemma 7(ii) happens iff $$X \cong X' \wedge Y \cong Y'$$. Hence

$$
(G, G', R) \in \mathrm{ISI} \iff (X \cong X') \wedge \neg(X \cong X' \wedge Y \cong Y') \iff X \cong X' \wedge Y \not\cong Y'.
$$

The construction is polynomial-time (the games have $$\vert V(K)\vert ^2$$ outcomes; $$R$$ is a polynomial-size 0/1 matrix). $$\square$$

**Theorem 9 (main).** ISI is $$\le^p$$-complete for $$\mathrm{D(GI)}$$; in particular $$\mathrm{ISI} \equiv^p \mathrm{4GI}$$.

*Proof.* Theorem 5, Theorem 8, and the $$\mathrm{D(GI)}$$-completeness of $$\mathrm{4GI}$$ (§2). $$\square$$

## 5. Consequences

**Theorem 10.** (i) $$\mathrm{ISI} \in \mathrm{DP}$$. (ii) $$\mathrm{GI} \le^p \mathrm{ISI}$$ and $$\mathrm{coGI} \le^p \mathrm{ISI}$$. (iii) If ISI is NP-hard or coNP-hard under polynomial-time Turing reductions — in particular if it is NP-, coNP-, or DP-complete — then $$\mathrm{PH} = \Sigma_2^p$$. (iv) $$\mathrm{GI} \in \mathrm{P} \iff \mathrm{ISI} \in \mathrm{P}$$; unconditionally, ISI is decidable in quasipolynomial time.

*Proof.* (i) $$z \in \mathrm{ISI} \iff f(z) \in \mathrm{GI} \wedge g(z) \notin \mathrm{GI}$$ (Theorem 5), and $$\mathrm{GI} \in \mathrm{NP}$$, so ISI is the intersection of an NP language with a coNP language. (ii) The map $$(X, X') \mapsto (X, X', C_6, C_3 \sqcup C_3)$$ reduces GI to $$\mathrm{4GI}$$, and $$(Y, Y') \mapsto (K_1, K_1, Y, Y')$$ reduces coGI to $$\mathrm{4GI}$$ (the appended fixed pair is non-isomorphic in the first case and isomorphic in the second); compose with Theorem 8. In the second case, condition (a) holds in every produced instance — the two constructed graphs are disjoint copies of $$K(K_1; Y, Y')$$ — so the coGI-hardness resides entirely in condition (b). (iii) NP-hardness under $$\le_T^p$$ gives $$\mathrm{NP} \subseteq \mathrm{P}^{\mathrm{ISI}} \subseteq \mathrm{P}^{\mathrm{GI}}$$ (Theorem 5). By the lowness theorem of Schöning (1988), $$\Sigma_2^{p,\mathrm{GI}} = \Sigma_2^p$$. Then every $$\Sigma_3^p$$-predicate $$\exists u\, \forall v\, Q(z, u, v)$$ with the inner $$\Sigma_1$$-part in $$\mathrm{NP} \subseteq \mathrm{P}^{\mathrm{GI}}$$ is decidable in $$\Sigma_2^{p, \mathrm{GI}}$$, so $$\Sigma_3^p \subseteq \Sigma_2^{p,\mathrm{GI}} = \Sigma_2^p$$, whence $$\mathrm{PH} = \Sigma_2^p$$. coNP-hardness gives the same, since $$\mathrm{P}^{\mathrm{ISI}}$$ is closed under complement; DP-hardness implies NP-hardness ($$\mathrm{SAT} \le^p \mathrm{SAT}\text{–}\mathrm{UNSAT}$$ by padding with a fixed unsatisfiable formula). (iv) If $$\mathrm{GI} \in \mathrm{P}$$, decide both queries of Theorem 5 in polynomial time; conversely $$\mathrm{ISI} \in \mathrm{P}$$ implies $$\mathrm{GI} \in \mathrm{P}$$ by (ii). For quasipolynomial time, evaluate $$f, g$$ and run the algorithm of Babai (2016) on both. $$\square$$

*Remark (finer upper bounds; safe to skip).* For readers who know the relevant classes: $$\mathrm{ISI} \in \mathrm{AM} \cap \mathrm{coAM}$$, since both conjuncts of the Theorem 5 characterization and both disjuncts of its negation are in AM ($$\mathrm{GI} \in \mathrm{NP} \cap \mathrm{coAM}$$ — Goldreich et al., 1991; Goldwasser and Sipser, 1986 — and AM is closed under union and intersection); and $$\mathrm{ISI} \in \mathrm{P}^{\mathrm{GI}} \subseteq \mathrm{SPP}$$, since $$\mathrm{GI} \in \mathrm{SPP}$$ (Arvind and Kurur, 2006) and SPP is self-low (Fenner et al., 1994), so ISI is low for $$\mathrm{PP}$$, $$\mathrm{C_=P}$$, and $$\mathrm{Mod}_k\mathrm{P}$$ (Fenner et al., 1994). The coAM bound gives an independent route to (iii) when the hardness is under $$\le^p$$, via "$$\mathrm{coNP} \subseteq \mathrm{AM}$$ collapses PH" (Boppana et al., 1987). None of this is used elsewhere in this note.

Given the coNP-completeness of safe improvement over finite, explicitly represented binary constraint structures under a satisfiability promise (Oesterheld and Conitzer, 2025), Theorem 10(iii) is a genuine contrast: replacing explicitly listed correspondence constraints by the isomorphism-generated ones *lowers* the complexity from coNP-complete to $$\mathrm{D(GI)}$$-complete, assuming PH does not collapse.

**Theorem 11 (exact position relative to the GI cone).** $$\mathrm{ISI} \le^p \mathrm{GI} \iff \mathrm{coGI} \le^p \mathrm{GI}$$; likewise $$\mathrm{ISI} \le^p \mathrm{coGI} \iff \mathrm{GI} \le^p \mathrm{coGI}$$. Hence ISI lies in the cone of GI iff that cone is closed under complement — an open question; a positive answer would in particular put graph non-isomorphism in NP.

*Proof.* First equivalence. (⇒) Compose $$\mathrm{coGI} \le^p \mathrm{ISI}$$ (Theorem 10(ii)) with $$\mathrm{ISI} \le^p \mathrm{GI}$$. (⇐) Given $$h$$ with $$I \notin \mathrm{GI} \iff h(I) \in \mathrm{GI}$$: $$z \in \mathrm{ISI} \iff f(z) \in \mathrm{GI} \wedge h(g(z)) \in \mathrm{GI} \iff \mathrm{AND}(f(z), h(g(z))) \in \mathrm{GI}$$, using the AND-function (F2).

Second equivalence. (⇒) Compose $$\mathrm{GI} \le^p \mathrm{ISI}$$ (Theorem 10(ii)) with $$\mathrm{ISI} \le^p \mathrm{coGI}$$. (⇐) Given $$k$$ with $$I \in \mathrm{GI} \iff k(I) \notin \mathrm{GI}$$:

$$
z \in \mathrm{ISI} \iff f(z) \in \mathrm{GI} \wedge g(z) \notin \mathrm{GI} \iff k(f(z)) \notin \mathrm{GI} \wedge g(z) \notin \mathrm{GI} \iff \mathrm{OR}(k(f(z)), g(z)) \notin \mathrm{GI},
$$

using the OR-function (F2); so $$z \mapsto \mathrm{OR}(k(f(z)), g(z))$$ reduces ISI to coGI.

Final claim: if $$\mathrm{coGI} \le^p \mathrm{GI}$$, then for any $$L \le^p \mathrm{GI}$$, the same reduction witnesses $$\overline{L} \le^p \mathrm{coGI}$$, and composing with $$\mathrm{coGI} \le^p \mathrm{GI}$$ gives $$\overline{L} \le^p \mathrm{GI}$$: the cone is closed under complement; conversely, closure under complement applied to $$\mathrm{GI}$$ itself gives $$\mathrm{coGI} \le^p \mathrm{GI}$$. And $$\mathrm{coGI} \le^p \mathrm{GI} \in \mathrm{NP}$$ would place graph non-isomorphism in NP. $$\square$$

So, under the standard working assumptions of this area (the GI cone not closed under complement; PH not collapsing), ISI is *strictly harder than game isomorphism under $$\le^p$$, yet far below NP-hardness*: a natural problem occupying the second level of the difference hierarchy over GI.

## 6. The Aut-invariant GI-complete regime

This section identifies a broad regime in which the general $$\mathrm{D(GI)}$$ predicate collapses all the way to a single GI instance. Aut-invariance already suffices for a polynomial-time mapping reduction; payoff-definedness is an important subclass for which an even simpler direct reduction is available.

**Definition (Aut-invariance).** Call $$R$$ *Aut-invariant in the second argument* (for the instance at hand) if

$$
(x,y) \in R \iff (x,\alpha(y)) \in R
\qquad\text{for all }\alpha \in \mathrm{Aut}(\bar G),\ x \in \bar A',\ y \in \bar A,
$$

and *Aut-invariant in the first argument* if

$$
(x,y)\in R \iff (\beta(x),y)\in R
\qquad\text{for all }\beta\in\mathrm{Aut}(\bar G'),\ x \in \bar A',\ y \in \bar A.
$$

Equivalently: invariance in the second argument says that each set $$\{y \in \bar A : (x,y) \in R\}$$ is a union of $$\mathrm{Aut}(\bar G)$$-orbits, and invariance in the first argument says that each set $$\{x \in \bar A' : (x,y) \in R\}$$ is a union of $$\mathrm{Aut}(\bar G')$$-orbits. Call $$R$$ *Aut-invariant* if it is Aut-invariant in at least one of its two arguments. The two conditions are not equivalent in general.

*A promise problem, not ISI itself.* Proposition 12 concerns not ISI but a somewhat different problem. A *promise problem* is a pair of disjoint sets of yes- and no-instances that need not together exhaust all inputs; a *promise-preserving mapping reduction* is a polynomial-time map sending yes-instances to yes-instances and no-instances to no-instances, with unconstrained behavior on all other inputs (a total language such as GI is the special case in which every input is a yes- or a no-instance). Write $$\mathrm{ISI}_{\mathrm{inv}}$$ for the promise problem whose promise class consists of the inputs whose $$R$$ is Aut-invariant; a promised input is a yes-instance if it lies in $$\mathrm{ISI}$$ and a no-instance otherwise. A reduction of $$\mathrm{ISI}_{\mathrm{inv}}$$ to GI is thus correct on Aut-invariant inputs and makes no claim about the rest; in particular it need not — and ours does not — test invariance, a condition of coGI type (it asserts the *non*existence of automorphisms carrying allowed pairs of $$R$$ to forbidden ones). A hardness reduction from GI, by contrast, must produce only promised outputs.

**Proposition 12 (invariance collapse and many-one reduction).** Suppose $$R$$ is Aut-invariant in the first or second argument. Then either every isomorphism $$\bar G \to \bar G'$$ is $$R$$-good or none is; consequently $$\mathrm{ISI} \iff \exists\,R\text{-good isomorphism}$$. Moreover, $$\mathrm{ISI}_{\mathrm{inv}}$$ is GI-complete under promise-preserving polynomial-time mapping reductions.

*Proof.* Isomorphisms compose and invert — the affine constants compose and invert while retaining positive scale — so any two isomorphisms $$\Phi,\Psi\colon\bar G\to\bar G'$$ are related both by $$\Psi=\Phi\circ\alpha$$ with $$\alpha:=\Phi^{-1}\Psi\in\mathrm{Aut}(\bar G)$$ and by $$\Psi=\beta\circ\Phi$$ with $$\beta:=\Psi\Phi^{-1}\in\mathrm{Aut}(\bar G')$$.

*Collapse.* Suppose $$\Phi$$ is good and $$\Psi$$ is any isomorphism. Under second-argument invariance: for any $$y$$, goodness of $$\Phi$$ at $$\alpha(y)$$ gives $$(\Phi(\alpha(y)),\alpha(y))=(\Psi(y),\alpha(y))\in R$$, and invariance replaces $$\alpha(y)$$ by $$y$$, yielding $$(\Psi(y),y)\in R$$. Under first-argument invariance: goodness of $$\Phi$$ at $$y$$ gives $$(\Phi(y),y)\in R$$, and invariance applied with $$\beta$$ yields $$(\beta(\Phi(y)),y)=(\Psi(y),y)\in R$$. Either way goodness is all-or-nothing across the isomorphism coset, proving the collapse and with it $$\mathrm{ISI}\iff\exists\,R\text{-good isomorphism}$$.

*Characterization.* The main idea of the reduction is that, on the promise class, ISI is equivalent to the conjunction of the two positive formulas

$$
\bigwedge_{x\in\bar A'}
\ \bigvee_{\substack{y\in\bar A\\(x,y)\in R}}
\bigl[P_{x,y}\text{ is a yes-instance}\bigr]
\tag{1}
$$

and

$$
\bigwedge_{y\in\bar A}
\ \bigvee_{\substack{x\in\bar A'\\(x,y)\in R}}
\bigl[P_{x,y}\text{ is a yes-instance}\bigr],
\tag{2}
$$

where $$P_{x,y}$$ is the pinned colored-GI instance of Lemma 4 and an empty disjunction is false. Specifically: ISI implies (1) and (2) for arbitrary $$R$$, while (1) implies ISI under second-argument invariance and (2) implies ISI under first-argument invariance. So on the promise class $$\mathrm{ISI}\iff(1)\wedge(2)$$, whichever of the two invariances happens to hold.

ISI $$\Rightarrow$$ (1) $$\wedge$$ (2): choose an isomorphism $$\Phi\colon\bar G\to\bar G'$$. For $$x\in\bar A'$$, let $$y:=\Phi^{-1}(x)$$; safety gives $$(x,y)=(\Phi(y),y)\in R$$, and $$\Phi$$ witnesses that $$P_{x,y}$$ is a yes-instance — the $$x$$-conjunct of (1). For $$y\in\bar A$$, the choice $$x:=\Phi(y)$$ proves the $$y$$-conjunct of (2) the same way.

(1) $$\Rightarrow$$ ISI under second-argument invariance: reduced games have nonempty outcome sets, so $$\bar A'\neq\varnothing$$; hence some yes pinned instance exists and therefore an isomorphism exists — condition (a). For condition (b), let $$\Psi\colon\bar G\to\bar G'$$ be an arbitrary isomorphism and let $$y_0\in\bar A$$; put $$x:=\Psi(y_0)$$. The $$x$$-conjunct of (1) supplies an outcome $$y_1\in\bar A$$ and an isomorphism $$\Phi$$ such that $$(x,y_1)\in R$$ and $$\Phi(y_1)=x$$. Then

$$
\alpha:=\Phi^{-1}\circ\Psi\in\mathrm{Aut}(\bar G)
\qquad\text{and}\qquad
\alpha(y_0)=\Phi^{-1}(x)=y_1,
$$

so invariance gives $$(x,y_0)\in R\iff(x,y_1)\in R$$; the latter holds, whence $$(\Psi(y_0),y_0)\in R$$.

(2) $$\Rightarrow$$ ISI under first-argument invariance is symmetric: $$\bar A\neq\varnothing$$ yields (a); given an arbitrary isomorphism $$\Psi$$ and $$y\in\bar A$$, the $$y$$-conjunct of (2) supplies $$x$$ and $$\Phi$$ with $$(x,y)\in R$$ and $$\Phi(y)=x$$, and $$\beta:=\Psi\circ\Phi^{-1}\in\mathrm{Aut}(\bar G')$$ satisfies $$\beta(x)=\Psi(y)$$, so invariance turns $$(x,y)\in R$$ into $$(\Psi(y),y)\in R$$.

*Reduction.* First perform the normalization of §3; if it detects that one side is constant and the other non-constant for some player, output $$\bot$$. Otherwise, convert each relevant $$P_{x,y}$$ to plain GI using (F1); build the $$\vert \bar A'\vert $$ OR-blocks of (1) and the $$\vert \bar A\vert $$ OR-blocks of (2) with the any-ary OR-function (F2), using $$\bot$$ for empty disjunctions; and combine all blocks into a single instance with the any-ary AND-function. This compiles $$(1)\wedge(2)$$; the map is the same whichever invariance holds, so the reduction never needs to determine which one it is. At most $$2\vert \bar A'\vert \vert \bar A\vert $$ pinned instances arise, so the map is polynomial-time. A separate conjunct for condition (a) is unnecessary because $$\bar A'\neq\varnothing$$ and any true inner disjunction already witnesses an isomorphism.

*Hardness.* GI-hardness holds already for the universally true $$R$$: the promise is then satisfied (in both arguments), and ISI is exactly game isomorphism of the reduced games, which is GI-complete for explicit normal-form games (Gabarró et al., 2011), including the player-preserving affine notion restricted to fully reduced games (Sauerberg and Oesterheld, 2026, extended version, Appendix E, Theorem E.1). Thus $$\mathrm{ISI}_{\mathrm{inv}}$$ is GI-complete under promise-preserving mapping reductions. Its NP membership, $$\mathrm{P}^{\mathrm{GI}}$$ membership, and Turing-GI-completeness follow immediately. $$\square$$

Proposition 12 shows that Aut-invariance alone suffices to compile the safety condition into one GI instance; there is no need to first find an isomorphism and then check it. Payoff-defined preferences remain important because their shared goodness verdict can be computed directly from the payoff tables, yielding a simpler reduction that avoids the pinned AND-of-OR construction.

Important applications include the payoff-comparison condition in the coupled Pareto case — subset games with the default game's utilities, $$\rho(a,b)=[a\ge b]$$ componentwise — and safe-$$u_1$$-improvements, $$\rho(a,b)=[a_1\ge b_1]$$. The direct reduction below recovers the GI upper bound for the isomorphism branch of the fixed-disarmament problems studied by Sauerberg and Oesterheld (2026). Their full SPI decision problem also includes the strict-improvement and polynomial-time simple-SPI checks.

**Proposition 13 (payoff-defined preferences: direct reduction).** Suppose $$R$$ is *payoff-defined*: $$(x,y)\in R\iff\rho(u'(x),u(y))$$ for all reduced outcomes, where $$u,u'$$ are the players' payoff-vector functions of the two games and $$\rho$$ is a polynomial-time evaluable predicate (given as part of the input, or as a promise about the explicit matrix). Then $$R$$ is Aut-invariant in both arguments. Moreover, ISI restricted to such instances reduces directly to GI and is GI-complete.

*Proof.* First, payoff-definedness implies Aut-invariance. If $$\alpha\in\mathrm{Aut}(\bar G)$$, Lemma 1 applied to $$\bar G$$ and itself forces $$\lambda_i=1,c_i=0$$ for every non-free player, while a free player's payoff is constant; hence $$u(\alpha(y))=u(y)$$ for every outcome $$y$$. Therefore $$\rho(u'(x),u(y))\iff\rho(u'(x),u(\alpha(y)))$$. The same argument for $$\mathrm{Aut}(\bar G')$$ gives first-argument invariance. Proposition 12 already yields the GI upper bound.

For the simpler direct reduction, apply Lemma 1 to the two reduced games. If some player is constant on one side only, output $$\bot$$. Otherwise, for every isomorphism $$\Phi$$ and reduced outcome $$y$$, the payoff vector of $$\Phi(y)$$ is forced independently of $$\Phi$$:

$$
u'_i(\Phi(y))=(u_i(y)-c_i)/\lambda_i
$$

for non-free players, and $$u'_i(\Phi(y))=k'_i$$, the constant value of $$u'_i$$ on $$\bar G'$$, for free players. Call this vector $$t(y)$$, and check for every reduced $$y$$ whether $$\rho(t(y),u(y))$$ holds. If all checks pass, then every isomorphism is $$R$$-good, so $$\mathrm{ISI}\iff$$ condition (a): output the game-isomorphism instance $$f(z)$$ of Theorem 5. If some check fails, then every isomorphism, if one exists, is bad at that $$y$$, while if none exists condition (a) fails; either way output $$\bot$$. With $$R$$ given as an explicit matrix plus the payoff-definedness promise, evaluate the check by looking up $$R(x,y)$$ for any reduced outcome $$x$$ with $$u'(x)=t(y)$$; if no such $$x$$ exists, no isomorphism can exist, so output $$\bot$$. GI-hardness follows by taking $$\rho$$ universally true. $$\square$$

Propositions 12 and 13 thus describe one nested GI-complete regime: payoff-defined preferences are Aut-invariant, while their extra structure permits a simpler direct reduction. Theorem 8 shows how the unrestricted problem escapes this regime. When $$Y\cong Y'$$, the outcomes $$(p,p)$$ and $$(q,q)$$ in the hardness construction lie in the same automorphism orbit of the reduced default game, yet the principal's utility $$w$$ separates them. The $$\mathrm{D(GI)}$$-hardness therefore works precisely by allowing preferences to split an automorphism orbit — the mechanism that Aut-invariance forbids. This identifies the source of the harder behavior in our construction, not a necessary-and-sufficient dichotomy over all possible restricted input families.

## 7. Relation to prior work

Oesterheld and Conitzer (2022) introduced SPIs and proved (their Theorem 9) that deciding the *existence* of a nontrivial SPI for a given game is NP-complete. Their hardness comes from subgraph isomorphism, through searching over candidate injections. Here the candidate is fixed, and the relevant condition quantifies universally over its isomorphisms. Their Lemma 4 is the quantifier collapse that keeps the *Pareto* fixed-candidate problem inside GI; our Lemma 1 isolates what that collapse does (pin $$(\lambda, c)$$) and does not do (pin $$\Phi$$).

Sauerberg and Oesterheld (2026) proved GI-completeness of deciding whether a given disarmament (action-removal) candidate is an SPI, and observed that the same proof applies to safe-$$u_1$$-improvements. Proposition 13 recovers the direct GI reduction for the payoff-defined isomorphism branch. Combining it with the polynomial-time strictness and simple-SPI checks yields the upper bound for the full fixed-disarmament decision problem. They also observed, for a related unilateral-remapping problem, that one may need to certify the *non*-existence of non-improving isomorphisms and left its complexity unclear — precisely the coGI ingredient that Theorem 8 shows is unavoidable in general.

Oesterheld and Conitzer (2025) generalized safe improvements to arbitrary preferences over finite, *explicitly represented* binary constraint structures and proved coNP-completeness under a satisfiability promise. The present problem replaces explicitly listed constraints by the implicitly generated set of all isomorphisms between two reduced games; the classification drops from coNP-complete to $$\mathrm{D(GI)}$$-complete (Theorem 10(iii) shows these differ unless PH collapses). Intuitively, isomorphism-generated constraint sets are highly structured — a coset of a permutation group — and cannot encode arbitrary coNP predicates, but they retain exactly enough freedom to encode one graph-isomorphism condition positively and one negatively.

The contrast with Lubiw's (1981) NP-completeness results is instructive. Lubiw's "isomorphism with restrictions" asks for an isomorphism satisfying constraints at *every* vertex simultaneously ($$\exists \varphi\, \forall v$$) and is NP-complete. The negation of our condition (b) has the shape $$\exists \varphi\, \exists y$$ — a single constrained pair suffices — which is why it stays GI-easy (one pinned instance per pair, OR-combined), and why ISI lands in the difference hierarchy over GI rather than at NP or coNP. Game isomorphism itself for explicit normal-form games is GI-complete (Gabarró et al., 2011), which anchors condition (a).

For the assumptions under which the isomorphism characterization of SPIs is the right one (representatives eliminate iteratively strictly dominated strategies and play fully reduced isomorphic games isomorphically), see Oesterheld and Conitzer (2022, §4); for symmetry-respecting equilibria and the complexity of game symmetries, see Tewolde et al. (2025).

## References

Apt, K. R. (2004). Uniform proofs of order independence for various strategy elimination procedures. *Contributions to Theoretical Economics* 4(1).

Arvind, V. and P. P. Kurur (2006). Graph isomorphism is in SPP. *Information and Computation* 204(5):835–852 (prelim. FOCS 2002).

Babai, L. (2016). Graph isomorphism in quasipolynomial time. *STOC 2016*, 684–697; analysis corrected Jan. 2017 (arXiv:1512.03547).

Boppana, R., J. Håstad, and S. Zachos (1987). Does co-NP have short interactive proofs? *Information Processing Letters* 25(2):127–132.

Cai, J., T. Gundermann, J. Hartmanis, L. Hemachandra, V. Sewelson, K. Wagner, and G. Wechsung (1988). The Boolean hierarchy I: structural properties. *SIAM Journal on Computing* 17(6):1232–1252.

Chang, R. and J. Kadin (1995). On computing Boolean connectives of characteristic functions. *Mathematical Systems Theory* 28(3):173–198.

Conitzer, V. and T. Sandholm (2005). Complexity of (iterated) dominance. *EC 2005*, 88–97.

Fenner, S., L. Fortnow, and S. Kurtz (1994). Gap-definable counting classes. *Journal of Computer and System Sciences* 48(1):116–148.

Gabarró, J., A. García, and M. Serna (2011). The complexity of game isomorphism. *Theoretical Computer Science* 412(48):6675–6695.

Gilboa, I., E. Kalai, and E. Zemel (1990). On the order of eliminating dominated strategies. *Operations Research Letters* 9(2):85–89.

Goldreich, O., S. Micali, and A. Wigderson (1991). Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems. *Journal of the ACM* 38(3):691–729.

Goldwasser, S. and M. Sipser (1986). Private coins versus public coins in interactive proof systems. *STOC 1986*, 59–68.

Köbler, J., U. Schöning, and J. Torán (1993). *The Graph Isomorphism Problem: Its Structural Complexity.* Birkhäuser.

Lubiw, A. (1981). Some NP-complete problems similar to graph isomorphism. *SIAM Journal on Computing* 10(1):11–21.

Oesterheld, C. and V. Conitzer (2022). Safe Pareto improvements for delegated game playing. *Autonomous Agents and Multi-Agent Systems* 36(2), art. 46 (prelim. AAMAS 2021).

Oesterheld, C. and V. Conitzer (2025). Choosing what game to play without selecting equilibria: inferring safe (Pareto) improvements in binary constraint structures. *TARK 2025*, EPTCS 437, 251–270 (arXiv:2511.21262).

Papadimitriou, C. and M. Yannakakis (1984). The complexity of facets (and some facets of complexity). *Journal of Computer and System Sciences* 28(2):244–259.

Sauerberg, N. and C. Oesterheld (2026). Promises made, promises kept: safe Pareto improvements via ex post verifiable commitments. *Proceedings of the AAAI Conference on Artificial Intelligence* 40(20):17231–17241 (arXiv:2505.00783).

Schöning, U. (1988). Graph isomorphism is in the low hierarchy. *Journal of Computer and System Sciences* 37(3):312–323.

Tewolde, E., B. H. Zhang, C. Oesterheld, T. Sandholm, and V. Conitzer (2025). Computing game symmetries and equilibria that respect them. *Proceedings of the AAAI Conference on Artificial Intelligence* 39(13):14148–14157 (arXiv:2501.08905).
