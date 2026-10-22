# Bulletproofs++ in this crate: specification

Status: §1–7 pinned: the weighted norm linear argument, arithmetic circuits, reciprocal form
circuits, range proofs and multi-asset transactions, the R1CS front end on BP++, and the
circuit builder shared by both backends.

Source: Eagen, Kanjalkar, Ruffing, Nick, *Bulletproofs++*, ePrint 2022/510 (version
2023-07-17). Where the paper is ambiguous this document decides; the reference
(`ref/bppp_ref.py`) and the Rust code (`src/bppp/`) implement this document, not each other.

## 1. Conventions

- Group: ristretto255. Scalars modulo
  $\ell = 2^{252} + 27742317777372353535851937790883648493$, encoded as 32 bytes little-endian;
  decoding accepts canonical encodings only. Points are compressed Ristretto (32 bytes).
- Vectors are zero-indexed and implicitly zero-padded on the right (generator vectors by the
  identity) wherever an operation needs equal lengths.
- Weighted inner product $\langle a, b\rangle_\mu = \sum_i a_i b_i \mu^{i+1}$ (weights start at
  $\mu^1$), $|a|^2_\mu = \langle a, a\rangle_\mu$.
- $[v]_0$, $[v]_1$: even and odd components of $v$; $|[v]_0| = \lceil |v|/2 \rceil$.
- Transcript: merlin. `domain_sep(x)` appends `x` under the label `dom-sep`; points are
  appended as their 32 bytes, integers with `append_u64`; a challenge is 64 squeezed bytes
  reduced modulo $\ell$ (as everywhere in this crate).
- Prover randomness is drawn with `Scalar::random` in the order each protocol lists; the test
  vectors depend on that order.
- The public provers (`circuit::prove`, `reciprocal::prove`, `prove_two_phase` and the front ends
  built on them) draw it, after absorbing the statement (dimensions, `G`, `H_0`, digest, inputs),
  from the transcript's RNG (`BpppTranscript::rng_builder`: merlin's `build_rng`, bound to
  everything absorbed so far, including the caller's own context), rekeyed with `"protocol"`
  (`circuit` or `reciprocal`), `"digest"` (§3.9, §4.4) and `"witness"` = SHA3-256 of the witness
  scalars (circuit: $w_L, w_R, w_O$, the inputs, their blindings; reciprocal: $w_D, w_L$, the
  elements of $w_O$ not in slot $l_R$, the inputs, the blindings — the late values are not known
  before $\alpha$; the tuple poles of §4.1 are hashed as 0, they are not known before $\eta$), then finalized with the caller's RNG, as BP's `TranscriptRng`. Defense in depth
  against a weak RNG: the same witness proven in another context gets other blindings. The vectors
  use the inner functions with explicit randomness.

## 2. Weighted norm linear argument (paper §4)

Public: $G$, $H \in \mathbb G^a$, $N \in \mathbb G^b$, $c \in \mathbb F^a$, $\rho \ne 0$,
$\mu = \rho^2$, and $C$. Witness: $l \in \mathbb F^a$, $n \in \mathbb F^b$ with

$$C = vG + \langle l, H\rangle + \langle n, N\rangle, \qquad v = \langle c, l\rangle + |n|^2_\mu .$$

The algebra, the rule for a norm vector of length 1 and the layout follow secp256k1-zkp's
norm argument (`src/modules/bppp`, the authors' implementation; layout from PR #352). §2.6 checks
this byte for byte.

### 2.1 Round

While the stop rule (§2.2) says to continue:

$$v_x = 2\rho^{-1}\langle [n]_0, [n]_1\rangle_{\mu^2} + \langle [c]_0, [l]_1\rangle + \langle [c]_1, [l]_0\rangle, \qquad v_r = |[n]_1|^2_{\mu^2} + \langle [c]_1, [l]_1\rangle$$

$$X = v_x G + \langle [l]_1, [H]_0\rangle + \langle [l]_0, [H]_1\rangle + \langle \rho [n]_1, [N]_0\rangle + \langle \rho^{-1}[n]_0, [N]_1\rangle$$

$$R = v_r G + \langle [l]_1, [H]_1\rangle + \langle [n]_1, [N]_1\rangle$$

Absorb $X$, $R$; $\gamma$ = challenge; $C' = C + \gamma X + (\gamma^2 - 1)R$. Then, if $a > 1$:
$c' = [c]_0 + \gamma[c]_1$, $l' = [l]_0 + \gamma[l]_1$, $H' = [H]_0 + \gamma[H]_1$. If $b > 1$:
$n' = \rho^{-1}[n]_0 + \gamma[n]_1$, $N' = \rho[N]_0 + \gamma[N]_1$, $\rho' = \mu$, $\mu' = \mu^2$.
A vector of length at most 1 is not folded, and while $b \le 1$ neither $\rho$ nor $\mu$ changes (the
norm relation is not folded); $X$ and $R$ then simply have no terms from it. An unpaired last
element of an odd-length vector is folded as if paired with zero (and the identity).

### 2.2 Stop rule

A round costs two points and removes $\lfloor a/2\rfloor + \lfloor b/2\rfloor$ scalars, so the
prover folds while $\lfloor a/2\rfloor + \lfloor b/2\rfloor \ge 3$ and then sends $l$ and $n$
(ties stop). This is the size-optimal layout of secp256k1-zkp PR #352; it equals that PR's closed
form for all lengths (unit test). The number of rounds $k$ and the final lengths follow from
$(a, b)$ alone: each round maps $(a, b) \mapsto (\lceil a/2\rceil, \lceil b/2\rceil)$. Lengths need
not be powers of two. (The paper's own rule, $a + b < 6$, differs only on ties; secp256k1-zkp
master folds down to single scalars and needs powers of two — the *legacy* layout, used only
for the cross-check in §2.6.)

### 2.3 Transcript

Standalone use (`prove`, `WnlaProof::verify`) first absorbs the statement:
`domain_sep("bppp-wnla-statement v1")`, point `"G"`, point `"C"`, scalar `"rho"`, and every
$c_i$ under `"c"`. The vector generators $H$, $N$ are the setup and are not absorbed; $G$ is,
since a prover who could pick it after the challenges could solve the check for it.

Then, in every use: `domain_sep("bppp-wnla v1")`, `u64 "l" = a`, `u64 "n" = b`; per round:
point `"X"`, point `"R"`, challenge `"gamma"`. $X$ and $R$ may be the identity (it happens for
sparse witnesses), unlike in the crate's inner-product argument.

Inside the circuit protocol the statement is **not** absorbed (`prove_unbound`,
`verification_scalars`, crate-internal): there $C$, $c$ and $\rho$ are functions of
commitments and challenges already in the transcript, and computing $C$ explicitly would
cost a full multiscalar multiplication. A caller of the unbound variants must have absorbed
every input of $C$, $c$ and $\rho$ before the header.

The argument is **not zero-knowledge**: the final $l$, $n$ are combinations of the witness.
Hiding comes from the blinding of the circuit protocol (§3).

### 2.4 Verification

With the round challenges $\gamma_r$, let $k_n$ be the number of rounds in which $n$ was
folded ($k_n = \min(k, \lceil\log_2 b\rceil)$), $\rho_r = \rho^{2^r}$ for $r < k_n$ and
$\rho_r = 1$ for the frozen rounds $r \ge k_n$:

- $h_i = l^{(k)}_{\lfloor i/2^k\rfloor} \prod_{r<k} (\text{bit}_r(i)\ ?\ \gamma_r : 1)$ for $i < a$;
- $n_i = n^{(k)}_{\lfloor i/2^k\rfloor} \prod_{r<k} (\text{bit}_r(i)\ ?\ \gamma_r : \rho_r)$ for $i < b$;
- $c^{(k)}$ = $c$ folded with the $\gamma_r$; $\mu_{\mathrm{fin}} = \rho^{2^{k_n+1}}$;
  $v = \langle c^{(k)}, l^{(k)}\rangle + |n^{(k)}|^2_{\mu_{\mathrm{fin}}}$.

Accept iff $vG + \langle h, H\rangle + \langle n, N\rangle - C - \sum_r \left(\gamma_r X_r + (\gamma_r^2 - 1) R_r\right) = 0$,
as one multiscalar multiplication. The scalars are exposed (`verification_scalars`) so that
the circuit verifier merges them into its own multiplication.

### 2.5 Encoding

$X_0 R_0 \dots X_{k-1} R_{k-1}\, l^{(k)}\, n^{(k)}$, 32 bytes each; decoding needs $(a, b)$ and
rejects any other length and non-canonical scalars. Point validity is checked on
decompression during verification.

### 2.6 Cross-check with secp256k1-zkp

`ref/xcheck_secp256k1_zkp.py` runs the reference's `wnla_prove` (the function that generates
our vectors) over secp256k1 with secp256k1-zkp's transcript (SHA-256; $\gamma$ = SHA-256 of the
running state with `le64(0)` appended, reduced mod $n$), its 65-byte round encoding and the
legacy layout, and reproduces all proofs of their `test_vectors/prove.h` byte for byte
(`tests/vectors/bppp/secp256k1-zkp/norm_prove.json`). Our transcript, curve and encoding differ;
the round algebra, the weights and the length-1 rule are theirs.

Note on constant time: secp256k1-zkp computes the norm argument in variable time, since inside
the circuit protocol its inputs are uniformly distributed given the transcript (paper,
Theorem 2: $l(\tau)$, $n(\tau)$ are masked by the fresh $l_S$, $n_S$, $r_S$ of $C_S$). This crate does
the same: the multiscalar multiplications for $X$ and $R$ run in variable time **inside the
circuit protocol** (always, since 2026-10-22; before, constant time unless the feature
`bppp-vartime`, now removed). The standalone argument, whose inputs are the caller's witness, and
every commitment to the witness stay constant time. The proofs are identical either way.

Implementation note (no effect on the proofs): the prover computes $X$ and $R$ of the first
rounds directly from the input generators with accumulated public coefficients and folds the
generators only afterwards (2 such rounds in constant time, 3 in variable time); a fold of the
norm generators is one scalar multiplication per pair ($N' = s\rho(N'_0 + \gamma\rho^{-1} N'_1)$ with
a common factor $s$).

## 3. Arithmetic circuits (paper §5)

The structure is the paper's §5.3 (commitments $C_L, C_R, C_O$, challenges, blinding
commitment $C_S$, one norm argument). The paper's typeset formulas for the constraint vectors,
the affine terms and $s_r$ contain sign and factor errors, so the signs and factors below are
re-derived; §3.5 states the identity they satisfy, and the reference checks it numerically.
All deviations from the paper are collected, with evidence, in `docs/bppp/bppp-paper-errors.tex`.
The prover computes $r_S$ by solving for the coefficients of a polynomial (§3.6) instead of
the paper's hand-expanded $s_r$; the blinding vector $c_r(T)$ and the zero pattern of the
$r_X$ are the paper's ($c_r$ is also the one of secp256k1-zkp's range proof, PR #207).

### 3.1 Relation

Dimensions: $N_m \ge 1$ multiplications, $N_O \ge 0$ further witness elements, $k \ge 0$ input
vectors of length $N_v \ge 1$, $N_l \ge 0$ linear constraints, and the length $N_{lin} \ge N_v - 1$
of the linear part of the commitments. Witness: $w_L, w_R \in \mathbb F^{N_m}$, $w_O \in \mathbb F^{N_O}$,
$w = w_L \| w_R \| w_O$ (so $W$ has $N_w = 2N_m + N_O$ columns: $w_L$ first, then $w_R$, then $w_O$),
inputs $v_0, \dots, v_{k-1} \in \mathbb F^{N_v}$ with blindings $s_i$, and
$w_V = v_0 \| \dots \| v_{k-1} \in \mathbb F^{kN_v}$.

A circuit is $(W_l \in \mathbb F^{N_l \times N_w}, a_l \in \mathbb F^{N_l}, W_m \in \mathbb F^{N_m \times N_w}, a_m \in \mathbb F^{N_m}, f_l, f_m \in \{0,1\})$
and a partition (§3.3). The witness satisfies it iff

$$W_l w + f_l w_V + a_l = 0, \qquad w_L \circ w_R = W_m w + f_m w_V + a_m,$$

where $w_V$ is zero-padded to the number of rows; $f_l = 1$ requires $N_l \ge kN_v$ and
$f_m = 1$ requires $N_m \ge kN_v$, and $k > 0$ requires $f_l = 1$ or $f_m = 1$ (otherwise the
inputs would enter no check at all). A row of $W_l$ or $W_m$ is a list of (column, coefficient)
terms; a column may repeat (the terms add up) and need not be sorted.

### 3.2 Generators and inputs

From `PedersenGens` $(B, \tilde B)$ and `BulletproofGens` (party 0, vectors $\mathbf G$ and
$\mathbf H$): $G = B$; $H_0 = \tilde B$, $H_{1..6} = \mathbf H_{0..5}$, $H_{7+t} = \mathbf H_{6+t}$ for
$t < N_{lin}$ (so $|H| = 7 + N_{lin}$); $N_t = \mathbf G_t$ for $t < N_m$. The `BulletproofGens`
capacity must be at least $\max(N_m, N_{lin} + 6)$.

Input commitments: $V_i = v_{i,0} G + s_i H_0 + \sum_{j=1}^{N_v - 1} v_{i,j} H_{6+j}$. For
$N_v = 1$ this is `PedersenGens::commit(v, s)`, the same commitment as in the BP backend.

**What is proven about the inputs.** The protocol binds the coordinates of $V_i$ that enter the
constraints — $v_{i,0}$ on $G$ and $v_{i,1..}$ on $H_{7..}$ — and the prover knows the rest of an
opening. It does not prove that $V_i$ has exactly the form above: components on
$H_1, \dots, H_6$, on linear slots beyond $N_v - 1$, or on $N$ (where orthogonal to the norm
slots in use) are absorbed by the blinding (found in review; the paper's relation (32) states the
strict form, and its extractor has the same gap). Applications that need $V_i = v G + s H_0$
exactly (e.g. homomorphic balance checks with a signature on the excess over $H_0$) get it from
their own equations.

### 3.3 Commitments

For $X \in \{L, R, O, S\}$, with $r_X \in \mathbb F^8$, $l_X \in \mathbb F^{N_{lin}}$, $n_X \in \mathbb F^{N_m}$:

$$C_X = r_{X,0} G + \sum_{j=1}^{7} r_{X,j} H_{j-1} + \sum_{t < N_{lin}} l_{X,t} H_{7+t} + \sum_{t < N_m} n_{X,t} N_t .$$

$n_L = w_L$, $n_R = w_R$. The partition maps each $w_{O,i}$ injectively to one slot $(n_O, t)$
with $t < N_m$ or $(l_O, t)$, $(l_L, t)$, $(l_R, t)$ with $t < N_{lin}$; slots not in the image
are 0.

Randomness, drawn with `Scalar::random` in this order: $r'_O$ (6 scalars), $r'_L$ (5),
$r'_R$ (4) before the commitments, then $l_S$ ($N_{lin}$) and $n_S$ ($N_m$) after the challenges.

$$r_O = (r'_{O,0}, r'_{O,1}, r'_{O,2}, r'_{O,3}, 0, r'_{O,4}, r'_{O,5}, 0), \quad r_L = (r'_{L,0}, r'_{L,1}, r'_{L,2}, 0, r'_{L,3}, r'_{L,4}, 0, 0), \quad r_R = (r'_{R,0}, r'_{R,1}, 0, r'_{R,2}, r'_{R,3}, 0, 0, 0).$$

### 3.4 Challenges and weights

After $C_L, C_R, C_O$: $\rho, \lambda, \beta, \delta$; $\rho$, $\beta$, $\delta$ must be non-zero (else the
prover fails and the verifier rejects). $\mu = \rho^2$, $\boldsymbol\mu_r = \mu^{r+1}$ for $r < N_m$.

Linear weights: $\Lambda_t = \lambda^t$ for $t < N_l$ (so $\Lambda_0 = 1$; $\lambda = 0$ is allowed), except when $f_l = f_m = 1$, where for
$t = N_v i + j$ with $i < k$ and $1 \le j < N_v$:

$$\Lambda_t = \lambda^t + \mu^j \lambda^{N_v i} - \lambda^j \mu^{N_v i + 1}$$

(this cancels the cross terms between the two input scalings). The rows stay bound: the
$\mu$-free part of $\Lambda_t$ is $\lambda^t$ (for $i = 0$, $\Lambda_j = (1 - \mu)\lambda^j + \mu^j$),
and the multiplicative terms of $E$ contribute only monomials with $\mu^{\ge 1}$, so $E$ vanishes
identically in $(\lambda, \mu)$ only if every residual is zero.

Column weights $y = \Lambda^\top W_l - \boldsymbol\mu^\top W_m \in \mathbb F^{N_w}$, and from them:

- $c_{n,L,t} = y_t / \boldsymbol\mu_t$, $c_{n,R,t} = y_{N_m + t} / \boldsymbol\mu_t$ for $t < N_m$;
- for $w_{O,i}$ in slot $(n_O, t)$: $c_{n,O,t} = y_{2N_m + i} / \boldsymbol\mu_t$; in slot $(l_X, t)$:
  $c_{l,X,t} = y_{2N_m + i}$; all other entries 0.

Inputs: $\nu_i = 2\left(f_m \mu^{N_v i + 1} - f_l \lambda^{N_v i}\right)$, $\hat V = \sum_i \nu_i V_i$,
$\hat v = \sum_i \nu_i v_{i,0}$, $l_V = \sum_i \nu_i v_{i,1:}$ and
$c_{V,j-1} = -(f_m \mu^j + f_l \lambda^j)$ for $1 \le j < N_v$ (both at linear indices
$0..N_v - 2$, zero beyond), $r_V = (0, \sum_i \nu_i s_i, 0, 0, 0, 0, 0, 0)$.

### 3.5 Polynomials

Laurent polynomials in $T$:

$$p_n(T) = \delta^{-1} T^3 c_{n,O} + T^2 c_{n,L} + T c_{n,R}, \qquad p_s(T) = |p_n(T)|^2_\mu + T^3\left(2\langle \boldsymbol\mu, a_m\rangle - 2\langle \Lambda, a_l\rangle\right),$$

$$\hat c_l(T) = 2\left(\delta^{-1} T^3 c_{l,O} + T^2 c_{l,L} + T c_{l,R}\right) + c_V, \qquad c_r(T) = \beta\,(T^{-1}, T, T^2, T^3, T^5, T^6, T^7),$$

$$\hat l(T) = T^{-1} l_S + \delta l_O + T l_L + T^2 l_R + T^3 l_V, \qquad n(T) = p_n(T) + T^{-1} n_S + \delta n_O + T n_L + T^2 n_R,$$

$$\hat f(T) = p_s(T) + T^3 \hat v - \langle \hat c_l(T), \hat l(T)\rangle - |n(T)|^2_\mu .$$

**Identity.** $\hat f$ has degrees $-2..6$, and its $T^3$ coefficient is $-2E$ with

$$E = \Lambda^\top (W_l w + f_l w_V + a_l) + \langle w_L, w_R\rangle_\mu - \boldsymbol\mu^\top (W_m w + f_m w_V + a_m),$$

which is 0 for a satisfying witness and, by Schwartz–Zippel in $\lambda$ and $\mu$, non-zero with
overwhelming probability otherwise.

### 3.6 Blinding commitment

Write $(e_1, \dots, e_7) = (-1, 1, 2, 3, 5, 6, 7)$ for the exponents of $c_r$ and

$$g(T) = \sum_{(X, \sigma)} \left( \sum_{j=1}^{7} \beta T^{e_j} \sigma\, r_{X,j} - \sigma\, r_{X,0} \right), \qquad (X, \sigma) \in \{(O, \delta), (L, T), (R, T^2), (V, T^3)\}.$$

The zero pattern of $r_O, r_L, r_R$ makes $g$ free of $T^3$ and of degree $\le 6$. With
$d(T) = \hat f(T) - g(T)$:

$$r_{S,0} = -d_{-1}, \qquad r_{S,j} = \beta^{-1} d_{e_j - 1} \quad (j = 1..7).$$

These cancel every coefficient of $d$ except $d_3 = \hat f_3$. The prover refuses (returns an
error) when $\hat f_3 \ne 0$, i.e. for a witness that does not satisfy the circuit. Then $C_S$ as in §3.3 with
$(r_S, l_S, n_S)$; absorb it; $\tau$ = challenge, non-zero.

### 3.7 Norm argument

$r(T) = T^{-1} r_S + \delta r_O + T r_L + T^2 r_R + T^3 r_V$. The verifier's commitment is

$$C(\tau) = p_s(\tau) G + \langle p_n(\tau), N\rangle + \tau^{-1} C_S + \delta C_O + \tau C_L + \tau^2 C_R + \tau^3 \hat V,$$

and it opens to $v = p_s(\tau) + r_0(\tau) + \tau^3 \hat v$, $l = r_{1..7}(\tau) \| \hat l(\tau)$,
$n = n(\tau)$, which satisfy the norm linear relation for $c = c_r(\tau) \| \hat c_l(\tau)$ and
$\mu = \rho^2$ exactly when $\hat f_3 = 0$. The norm argument (§2) runs on
$(G, H, N, c, \rho)$ **without** absorbing its statement: $C(\tau)$, $c$ and $\rho$ are functions of
values already in the transcript.

**Verification** (one multiscalar multiplication), with the norm argument's scalars
$(v', h, n', \gamma)$ of §2.4 ($v'$ the coefficient of $G$):

$$(v' - p_s(\tau)) G + \langle h, H\rangle + \langle n' - p_n(\tau), N\rangle - \tau^{-1} C_S - \delta C_O - \tau C_L - \tau^2 C_R - \sum_i \tau^3 \nu_i V_i - \sum_r \left(\gamma_r X_r + (\gamma_r^2 - 1) R_r\right) = 0 .$$

### 3.8 Transcript

`domain_sep("bppp-circuit v1")`; `u64` `"N_m"`, `"N_O"`, `"N_v"`, `"N_lin"`, `"k"`, `"N_l"`,
`"f_l"`, `"f_m"`; points `"G"` and `"H_0"` (the value and blinding generators, which may be
application-specific); message `"circuit"` = the circuit digest (§3.9); point `"V"` for each input;
points `"C_L"`, `"C_R"`, `"C_O"`; challenges `"rho"`, `"lambda"`, `"beta"`, `"delta"`; point
`"C_S"`; challenge `"tau"`; then the norm argument's header and rounds (§2.3).

The public `prove`/`verify` absorb the digest (strong Fiat–Shamir). Protocols built on top
absorb their own statement and enter the inner protocol at `"rho"` (crate-internal
`prove_inner`/`verify_inner`): the reciprocal form (§4.5) absorbs `C_L`, `C_O`, `"alpha"`, `C_R`
before it, and skips the whole §3 statement, which its own statement covers.

### 3.9 Circuit digest

SHA3-256 over: the bytes `bppp-circuit-digest v1`; the eight dimensions and flags of §3.8 as
`u64` little-endian; for each $w_{O,i}$ its slot (one byte: 0 $n_O$, 1 $l_O$, 2 $l_L$, 3 $l_R$) and
index (`u64`); for $W_l$ then $W_m$: per row the number of terms (`u64`) and per term the column
(`u64`) and the coefficient (32 bytes), in stored order; then $a_l$ and $a_m$ (32 bytes each).

### 3.10 Encoding

$C_L \| C_R \| C_O \| C_S \|$ norm argument for $|l| = 7 + N_{lin}$, $|n| = N_m$ (§2.5).

### 3.11 Batch verification

Proofs over the same `PedersenGens` and `BulletproofGens` (circuits §3, reciprocal form §4,
range proofs and transactions §5) are verified together: each proof's transcript is replayed as
in its own verification, which gives its equation of §3.7 as
$g\,G + \langle h, H\rangle + \langle n, N\rangle + \sum_k k P_k = 0$ over the shared generators
(prefixes of one setup) and its own points ($C_S, C_O, C_L, C_R$, the inputs, the rounds' $X, R$).
The verifier draws a uniformly random weight per proof from its own RNG (never from a
transcript: the weights must be unknown to the provers), sums the weighted equations
coefficient by coefficient, and checks the sum with one multiscalar multiplication. If some
proof's equation does not hold, the sum vanishes with probability at most $1/\ell$ over its
weight. A failing batch does not identify the proof; malformed proofs and statements that fail
before the multiplication are reported when added.

## 4. Reciprocal form circuits (paper §6.2–6.3)

A reciprocal form circuit adds to an arithmetic circuit $N_p$ *poles*: private denominators
$w_{D,i}$ and reciprocals $w_{P,i} = \mathrm{num}_i / (\alpha + w_{D,i})$ computed after a challenge
$\alpha$, together with linear *reciprocal rows* that sum reciprocals and public poles
$m/(\alpha + t)$. For a fixed $\alpha$ it compiles to an arithmetic circuit (§3) with
$N'_m = N_p + N_m$ multiplications, which is then proven with the inner protocol of §3 (from the
challenge $\rho$ on). Soundness of the reciprocal argument (paper Lemma 1) needs every numerator
and multiplicity committed before $\alpha$; the rules below enforce it.

**Tuple poles (our extension, not in the paper).** A pole may also be a *tuple pole*
$w_{D,i} = \sum_j \eta^j x_{i,j}$, a compression of a tuple with a challenge $\eta$, and a public
pole may be a polynomial in $\eta$. The components $x_{i,j}$ are committed in $C_O$ before $\eta$;
$C_L$ (which holds $w_D$) follows $\eta$: the transcript becomes $C_O, \eta, C_L, \alpha, C_R$ (§4.3).
This gives lookups of tuples whose components are arbitrary field elements, as logUp does in
BP (§7.3); soundness in §4.7. A circuit without them is proven exactly as before (protocol v1).

### 4.1 Witness and circuit

Witness: poles $w_D \in \mathbb F^{N_p}$, $w_L, w_R \in \mathbb F^{N_m}$, $w_O \in \mathbb F^{N_O}$,
inputs as in §3. The prover computes $w_P \in \mathbb F^{N_p}$ (§4.3). The full witness is

$$w' = w'_L \| w'_R \| w_O, \qquad w'_L = w_D \| w_L, \qquad w'_R = w_P \| w_R,$$

with $N'_w = 2N'_m + N_O$ columns; all matrices below index $w'$. The **initial columns** are
those committed before $\alpha$: all of $w'_L$, and the elements of $w_O$ whose partition slot is
not $l_R$ (that slot is committed in $C_R$, after $\alpha$). The **early columns** are those
committed in $C_O$: the elements of $w_O$ in slots $n_O$ and $l_O$.

A *pole polynomial* is a list of $d \ge 1$ scalars $(t_0, \dots, t_{d-1})$, with the value
$t(\eta) = \sum_e t_e \eta^e$; a public pole $t$ (below) is a pole polynomial, and one of length 1
is the constant $t_0$.

A reciprocal form circuit consists of

- $W_n \in \mathbb F^{N_p \times N'_w}$, $a_n \in \mathbb F^{N_p}$ (numerators): only initial columns;
- $W_m \in \mathbb F^{N_m \times N'_w}$, $a_m \in \mathbb F^{N_m}$ (ordinary multiplicative rows);
- $W_l \in \mathbb F^{N_l \times N'_w}$, $a_l \in \mathbb F^{N_l}$ (ordinary linear rows, any columns);
- $N_r$ reciprocal rows; row $q$ is a list of terms $(\text{column}, c, t)$ meaning
  $c\, w'_{\text{column}}/(X + t)$, or $c\, w'_{\text{column}}$ when $t$ is absent, and a list of
  constants $(c, t)$ meaning $c/(X + t)$ or $c$. A term with a pole $t$ must use an initial column;
  a term without a pole must use an initial column or a reciprocal column $w_{P,i}$ (the first
  $N_p$ columns of $w'_R$);
- the *tuple poles*: a list of entries $(i, x_{i,0}, \dots, x_{i,m_i - 1})$ with $i < N_p$ (each $i$ at
  most once, the entries in increasing $i$) and $m_i \ge 1$ components; a component is a list of
  terms $(\text{column}, c)$ over **early columns only** and a constant $a$, with the value
  $x_{i,j} = \sum c\, w'_{\text{column}} + a$. Then $w_{D,i}$ is not a witness value but
  $\sum_j \eta^j x_{i,j}$ (computed by the prover after $\eta$); the other poles are *free*;
- the flags $f_l$, $f_m$ and the partition of $w_O$ as in §3, with $N_{lin}$, $N_v$, $k$;
  $f_l = 1$ requires $N_l \ge kN_v$ (inputs never reach the reciprocal rows); $N_m = 0$ is
  allowed (only $N'_m \ge 1$ is needed), and a slot $(n_O, t)$ needs $t < N'_m$.

Ordinary rows that read $w_P$ or $w_R$ hold at the challenge $\alpha$ only (they are part of the
compiled circuit); $w_R$ and the elements of $w_O$ in slot $l_R$ may therefore be computed
after $\alpha$: the two-phase prover (§4.3) takes them from a callback that receives $\alpha$ and
$w_P$.

The circuit **uses $\eta$** if it has a tuple pole or a public pole of length at least 2; only then
is $\eta$ drawn (§4.3). For a circuit that does not, $\eta$ plays no role below.

A reciprocal row is an **$\eta$-row** if it has a term on the reciprocal column $w_{P,i}$ of a tuple
pole, or a term or constant whose pole has length at least 2. In an $\eta$-row every term on a
reciprocal column must be on a tuple pole: free poles (committed in $C_L$, after $\eta$) and tuple
poles do not mix (§4.7). Other rows are unrestricted, as in v1.

It is satisfied for $(\eta, \alpha)$ if, with the tuple poles set to $w_{D,i} = \sum_j \eta^j x_{i,j}$ and every
public pole $t$ replaced by $t(\eta)$: for every $i < N_p$,
$(X + w_{D,i})\, w_{P,i}(X) = (W_n w' + f_m w_V + a_n)_i$
defines the reciprocals, every reciprocal row vanishes **as a rational function of $X$**, and the
ordinary rows hold:
$w_L \circ w_R = (W_m w' + f_m \tilde w_V + a_m)$ and $W_l w' + f_l w_V + a_l = 0$, where
$\tilde w_V$ is the part of the zero-padded $w_V$ that falls on rows $N_p..N'_m - 1$ (see §4.2).

### 4.2 Compilation for the challenges $(\eta, \alpha)$

The compiled circuit (§3) has $N'_m = N_p + N_m$, $N_O$, $N_v$, $N_{lin}$, $k$, the same flags and
partition, and

- multiplicative rows: for $i < N_p$, row $i$ of $W_n$ with $-\alpha$ added at the column of
  $w_{P,i}$ (that is, $w_{D,i}\, w_{P,i} = (W_n w')_i - \alpha\, w_{P,i} + f_m w_{V,i} + a_{n,i}$), then
  the rows of $W_m$; $a'_m = a_n \| a_m$;
- linear rows: the rows of $W_l$; then, for each tuple pole $(i, x_{i,0}, \dots)$ in order, the row
  $[(w_{D,i}, 1)]$ followed, for $j = 0, 1, \dots$, by the terms of $x_{i,j}$ with coefficients
  multiplied by $-\eta^j$, affine term $-\sum_j \eta^j a_{i,j}$ (so $w_{D,i} = \sum_j \eta^j x_{i,j}$);
  then each reciprocal row evaluated at $X = \alpha$ (a term with pole $t$ gets the coefficient
  $c/(\alpha + t(\eta))$, constants are summed into the affine term);
  $a'_l = a_l \| a_t(\eta) \| a_r(\eta, \alpha)$.
  (A circuit that does not use $\eta$ has no tuple rows and constant poles: the compilation of v1.)

So $f_m w_V$ meets the first $kN_v$ compiled multiplicative rows (numerators first) and $f_l w_V$
the first $kN_v$ rows of $W_l$; the requirements of §3.1 apply to the compiled dimensions.

### 4.3 Protocol

1. Commit the initial witness: $C_L$ for $(r_L, l_L, w'_L)$ and $C_O$ for $(r_O, l_O, n_O)$ as in
   §3.3 (randomness $r'_O$, then $r'_L$).
   **If the circuit uses $\eta$** (protocol v2): commit $C_O$ first (randomness $r'_O$), absorb it
   and take the challenge $\eta$; set the tuple poles $w_{D,i} = \sum_j \eta^j x_{i,j}$ (the
   witness's values for them are ignored); then commit $C_L$ (randomness $r'_L$). The randomness
   is drawn in the same order as in v1.
2. Absorb (§4.5) and take the challenge $\alpha$.
3. Compute $w_{P,i} = (W_n w' + f_m w_V + a_n)_i \cdot (\alpha + w_{D,i})^{-1}$; the prover fails if
   $\alpha + w_{D,i} = 0$ for some $i$, and both prover and verifier fail if $\alpha + t = 0$
   for a public pole $t$ (probability negligible in either case). Commit $C_R$ for $(r_R, l_R, w'_R)$ (randomness $r'_R$).
4. Absorb $C_R$ and run the inner protocol of §3 on the compiled circuit from the challenges
   $\rho, \lambda, \beta, \delta$ on (§3.4–3.7). The prover refuses if the compiled circuit is not
   satisfied (its value term is non-zero).

The verifier compiles the circuit for $(\eta, \alpha)$ and runs the §3 verification on $C_L, C_R, C_O, C_S$.
$\eta = 0$ needs no special case: the compiled circuit is still well defined, and the soundness
bound of §4.7 counts it.
Randomness is drawn in the order of §3.3 ($r'_O$, $r'_L$, $r'_R$, then $l_S$, $n_S$).

**Two-phase prover.** The *late* values — $w_R$ and the elements of $w_O$ in slot $l_R$ — may
depend on $\alpha$ and $w_P$. The prover takes the initial witness ($w_D$, $w_L$, the other
elements of $w_O$, the inputs; in Rust a full witness whose late entries are placeholders,
length-checked and ignored) and a callback $(\alpha, w_P) \mapsto (w_R, (w_{O,i})_{i \in l_R})$
(the $l_R$ elements in $w_O$ order), called once between steps 3 and 4 (after $w_P$ is computed,
before $C_R$). Transcript, randomness and proof are those of the one-phase prover, which is the
special case of a callback that returns values fixed in advance.

### 4.4 Digest

For a circuit that does not use $\eta$: SHA3-256 over: the bytes `bppp-reciprocal-digest v1`; the dimensions of §4.5 as `u64`
little-endian; the partition as in §3.9; the rows of $W_n$, $W_m$, $W_l$ as in §3.9; $a_n$, $a_m$,
$a_l$ (32 bytes each); then per reciprocal row: the number of terms (`u64`), per term the column
(`u64`), $c$ (32 bytes) and the pole (one byte 0, or one byte 1 and $t$, 32 bytes); the number of
constants (`u64`) and per constant $c$ and the pole likewise.

For a circuit that uses $\eta$: the same with the bytes `bppp-reciprocal-digest v2`, the dimensions
of v2 (§4.5, $N_t$ last), each pole as one byte 0, or one byte 1, its length $d$ (`u64`) and $t_0..t_{d-1}$
(32 bytes each), and at the end, per tuple pole: $i$ (`u64`), $m_i$ (`u64`), per component the
number of terms (`u64`), per term the column (`u64`) and $c$ (32 bytes), then $a$ (32 bytes).

### 4.5 Transcript

`domain_sep("bppp-reciprocal v1")`; `u64` `"N_p"`, `"N_m"`, `"N_O"`, `"N_v"`, `"N_lin"`, `"k"`,
`"N_l"`, `"N_r"`, `"f_l"`, `"f_m"`; points `"G"`, `"H_0"`; message `"circuit"` = the digest
(§4.4); point `"V"` per input; points `"C_L"`, `"C_O"`; challenge `"alpha"`; point `"C_R"`; then
the challenges and messages of §3.8 from `"rho"` on (the §3 statement — dimensions, generators,
digest, inputs — is not absorbed again: the reciprocal statement above covers it).

v2 (the circuit uses $\eta$): `domain_sep("bppp-reciprocal v2")`; the dimensions of v1, then `u64`
`"N_t"` (the number of tuple poles); points `"G"`, `"H_0"`; message `"circuit"` (the v2 digest);
point `"V"` per input; point `"C_O"`; challenge `"eta"`; point `"C_L"`; challenge `"alpha"`; point
`"C_R"`; then as v1.

### 4.6 Encoding

As §3.10, for the compiled dimensions ($|n| = N_p + N_m$); v1 and v2 proofs have the same size.

### 4.7 Soundness of tuple poles (argument, not a formal proof)

The §3 extractor (from $\rho$ on) yields openings of $C_O, C_L, C_R$ that satisfy the compiled
circuit for $(\eta, \alpha)$; by binding, the opening of $C_O$ — the early columns, hence every
component $x_{i,j}$ — is fixed before $\eta$, and the initial columns are fixed before $\alpha$.
For a fixed $\eta$, paper Lemma 1 applies unchanged (the poles $w_{D,i}$ and the numerators are in
$C_L$, $C_O$, fixed before $\alpha$): except with probability about $(N_p + T)/\ell$ over $\alpha$, every
reciprocal row vanishes as a rational function of $X$ with the poles $w_{D,i} = \sum_j \eta^j x_{i,j}$
and $t(\eta)$.

What a tuple lookup needs is the identity *per tuple*: for each distinct tuple, the sum of the
numerators of its terms is zero. Let $S$ be the set of distinct tuples (component lists, padded
with zeros to a common length $m$) of the private tuple poles and the public poles of one row.
They are fixed before $\eta$ (private: by $C_O$; public: by the statement). If $\tau \mapsto
\sum_j \eta^j \tau_j$ is injective on $S$, grouping by pole value is grouping by tuple and the
identity per tuple follows. For two distinct tuples the difference $\sum_j \eta^j(\tau_j - \tau'_j)$ is
a non-zero polynomial of degree $\le m - 1$, so (Schwartz–Zippel, union bound) injectivity fails
with probability at most $\binom{|S|}{2}(m-1)/\ell$ over $\eta$; summed over the rows, at most
$(N_p + T)^2 (m-1)/(2\ell)$ with $T$ public terms. This needs every private pole of the row to be
a tuple pole: a free pole ($w_{D,i}$ in $C_L$, after $\eta$) could take the compressed value of any
tuple and cancel it, which is why §4.1 forbids free poles in $\eta$-rows. A row of free poles only
has the identity over pole values, which is all it needs: its poles are fixed before $\alpha$.
The builder (§7.6) never mixes them (an argument has one $m$).

The numerators need not be fixed before $\eta$: $W_n$ may read $w_L$ and $w_D$ (in $C_L$, after
$\eta$), and the relation is the identity for the extracted numerators at that $\eta$ — only the
set of tuples must be fixed before $\eta$ for grouping by pole value to be grouping by tuple.

So the extra round adds one challenge with a bad-challenge probability as above (round-by-round
soundness); assuming the §3 protocol is $(k_1, \dots, k_\mu)$-special-sound, the Fiat–Shamir loss
for multi-round special-sound protocols is linear in the number of random-oracle queries
(Attema, Fehr, Klooß 2022), so with $Q$ queries the added term is
$Q (N_p + T)^2 (m-1)/(2\ell)$. Zero knowledge is unaffected: the commitments, their randomness and
the openings are those of v1, only the order of the public challenges differs (§3's simulator
does not depend on it).

## 5. Range proofs and multi-asset transactions (paper §6.4–6.5)

Front ends that build reciprocal form circuits (§4) from a statement. The circuit layout below is
normative: prover, verifier and reference build the same circuit, column for column.

### 5.1 Digit layout for a range $[0, B)$

For $B \ge 2$ and a base $b \ge 2$, a layout is a list of digits $(g_j, r_j)$ (weight, radix) such that
the sums $\sum_j g_j d_j$ with $d_j \in [0, r_j)$ are exactly $[0, B)$. It is built as follows
(the paper's Cases 1–3 with the same number of digits and tables, plus ranges smaller than the
base, where the paper's eq. (73) fails):

1. $S = 0$, $p = 1$; while $S + (b-1)p \le B - 1$: append $(p, b)$, $S \mathrel{+}= (b-1)p$, $p \mathrel{*}= b$.
   Let $R = B - 1 - S$; stop if $R = 0$.
2. (Case 1) If $(b - 1) \mid R$ and $R/(b-1) \le S + 1$: append $(R/(b-1), b)$ and stop.
3. (Case 2) If $R \le S + 1$: append $(R, 2)$ and stop.
4. (Case 3) If $R \ge b - 1$: append $(g, b)$ with $g = \lfloor R/(b-1)\rfloor$, $S \mathrel{+}= (b-1)g$,
   $R \mathrel{-}= (b-1)g$; then, if $R > 0$, append $(R, 2)$ (now $R < b - 1 \le S + 1$).
5. (Otherwise $S = 0$, i.e. $B < b$, and $2 \le R < b - 1$.) Append $(1, R + 1)$.

Every prefix of the layout sorted by weight satisfies $g_j \le 1 + \sum_{i<j}(r_i - 1)g_i$, so the sums are
contiguous, and $\sum_j (r_j - 1) g_j = B - 1$. A value $x \in [0, B)$ is decomposed from the largest
weight down: with $M_j$ the maximum of the digits of smaller weight,
$d_j = \max(0, \lceil (x - M_j)/g_j \rceil)$ and $x \mathrel{-}= d_j g_j$ (ties in weight: the later
digit counts as larger). The prover computes this in constant time with respect to $x$.

### 5.2 Range proof circuit

Statement: base $b$ ($2 \le b \le 256$) and $m \ge 1$ ranges $[A_i, B_i)$ of integers with
$0 \le A_i$, $A_i + 2 \le B_i \le 2^{64}$ (values are 64-bit); inputs $V_i = v_i G + s_i H_0$
($N_v = 1$, $k = m$) with $v_i \in [A_i, B_i)$. Let $L_i$ be the layout of
$B_i - A_i$ (§5.1, in construction order).

- **Poles**: the digits of $L_0$, then of $L_1$, …; $N_p = \sum_i |L_i|$, $N_m = 0$; numerators 1
  ($W_n = 0$, $a_n = 1$).
- **Tables**: one per distinct radix $r$ among the digits, in ascending order of $r$. Table $r$ has
  the multiplicities $m_{r,s}$ ($s = 1..r-1$) of the digit values among the digits of radix $r$
  (value 0 is implicit, paper eq. (75)). $w_O$ is the concatenation of the tables' multiplicities,
  $N_O = \sum_r (r - 1)$. They go to slots $(n_O, t)$, $t = 0..N_O - 1$, if $N_O \le N_p$
  (inline); otherwise to $(l_L, t)$ with $N_{lin} = N_O$ (shared). Otherwise $N_{lin} = 0$.
- **Linear rows** ($f_l = 1$, $f_m = 0$): row $i$ has $-g_j$ on the pole column of each digit $j$ of
  $L_i$, in layout order, and $a_{l,i} = -A_i$, so the row is $v_i - A_i - \sum_j g_j d_j = 0$.
- **Reciprocal rows**, one per table $r$: the terms $(w_{P,p}, 1)$ for every pole $p$ of radix $r$, in
  pole order; then for $s = 1..r-1$ the terms $(m_{r,s}, 1, \text{pole } 0)$ and
  $(m_{r,s}, -1, \text{pole } s)$; and the constant $(-N_r, \text{pole } 0)$, $N_r$ the number of
  digits of radix $r$. That is
  $\sum_p \frac{1}{X + d_p} = \frac{N_r - \sum_s m_{r,s}}{X} + \sum_{s \ge 1} \frac{m_{r,s}}{X + s}$.
  The terms are stored in exactly this order, and the pole $0$ is a pole (`Some(0)`), not "no
  pole": the digest (§4.4) hashes rows as stored.

Multiplicities are totals over all digits of a radix, in $n_O$ when they fit (the paper's
inline variant instead aligns per-range multiplicities with the digits).

The transcript is `domain_sep("bppp-range v1")` followed by §4.5 (whose digest binds the
circuit, hence the ranges and the base). Soundness: a digit outside $[0, r)$ leaves a pole at
$-d$ with multiplicity between 1 and the number of digits, non-zero in $\mathbb F$; then
$v_i - A_i = \sum g_j d_j \in [0, B_i - A_i)$.

### 5.3 Multi-asset transaction circuit

Statement: $n_{in}$ inputs and $n_{out}$ outputs ($k = n_{in} + n_{out} \ge 1$; either may be 0), base
$b$ ($2 \le b \le 256$). Entry $i$
(inputs first) is an amount $a_i \in [0, 2^{64})$, an asset type $t_i \in \mathbb F$ and a blinding
$s_i$, committed as $V_i = a_i G + s_i H_0 + t_i H_7$ ($N_v = 2$). The relation: for every asset type,
inputs and outputs balance, and every output amount is in $[0, 2^{64})$. (Input amounts are
assumed in range — they are earlier outputs; then $k\,2^{64} < \ell$ makes the balance in
$\mathbb F$ a balance in $\mathbb Z$, paper Theorem 5.) Asset types are scalars (for example a
hash of the asset id), as in the paper; this is not the asset-generator construction of
confidential assets. Let $L$ be the layout of $2^{64}$ in base $b$.

- **Poles**: the asset types $w_{D,i} = t_i$ for $i < k$, then the digits of each output (output 0
  first) in layout order. Numerators: pole $i < k$ has $W_n$ row $\pm 1$ on the amount copy
  $c_i$ ($+$ for inputs, $-$ for outputs), $a_{n,i} = 0$; digit poles have $a_n = 1$. $N_m = 0$.
- **$w_O$**: the amount copies $c_0..c_{k-1}$ in slots $(l_O, i)$, then the table multiplicities as in
  §5.2, inline in $(n_O, t)$ if they fit in $N_p$, else shared in $(l_L, t)$.
  $N_{lin} = \max(k, M)$ with $M$ the number of multiplicities if they are shared, else 0.
- **Linear rows** ($f_l = 1$, $f_m = 0$; $w_V = (a_0, t_0, a_1, t_1, \dots)$): row $2i$ is $-c_i$ (so
  $a_i - c_i = 0$), row $2i+1$ is $-w_{D,i}$ (so $t_i - w_{D,i} = 0$), with $a_l = 0$; then for each
  output $j$ a row with $-g$ on its digit poles (layout order) and then $+1$ on $c_{n_{in}+j}$,
  $a_l = 0$.
- **Reciprocal rows**: first the balance row $\sum_{i<k} w_{P,i} = 0$, i.e.
  $\sum_i \frac{\pm c_i}{X + t_i} = 0$; then the table rows of §5.2.

The paper (§6.5.1) takes the numerators from the inputs with $f_m = 1$ and aligns them by dummy
constraints; we copy the amounts into $c_i$ with linear rows instead ($f_m = 0$), which keeps
every numerator on an initial column.

The transcript is `domain_sep("bppp-mact v1")` followed by §4.5.

## 6. The R1CS front end on BP++ (paper §5.1)

`Prover::set_backend(Backend::Bppp)` and `Verifier::set_backend(Backend::Bppp)` select BP++;
`prove(&bp_gens)` and `verify(&proof, &pc_gens, &bp_gens)` keep their signatures, and gadgets
written against `ConstraintSystem` run unchanged.

### 6.1 Translation

Every constraint system proven with BP++ is lowered by §7.6 to a reciprocal form circuit, whether
or not it uses builder operations (§7); there is one BP++ lowering and one encoding. A plain
R1CS (no builder operation) has no poles, products or witnesses, so it lowers to the reciprocal
form circuit with $N_p = 0$ and no reciprocal rows — in effect an arithmetic circuit (§3):

An R1CS with $n$ multipliers $(a_L, a_R, a_O)$, $k$ committed inputs $V_j = v_j B + s_j \tilde B$ and
linear constraints $\sum c\, x + c_0 = 0$ gives $N_m = \max(1, n)$ (missing gates are zero),
$N_O = N_m + k$, $N_v = 1$, $N_{lin} = k$, $f_l = [k > 0]$, $f_m = 0$:

- $w_L = a_L$, $w_R = a_R$, $w_O = a_O \| c$ with $c_j$ a copy of $v_j$; partition: $a_{O,i}$ in
  $(n_O, i)$, $c_j$ in $(l_O, j)$;
- multiplicative rows: row $i$ selects $w_{O,i}$ ($w_L \circ w_R = a_O$), $a_m = 0$;
- linear rows: first, for $j < k$, $-c_j$ (so $v_j - c_j = 0$ through $f_l$); then each R1CS
  constraint in order, with `MultiplierLeft(i)`, `MultiplierRight(i)`, `MultiplierOutput(i)`,
  `Committed(j)` mapped to the columns of $w_{L,i}$, $w_{R,i}$, $w_{O,i}$, $c_j$, and the constant
  in $a_l$. A variable the constraint system did not allocate is a `GadgetError`.

The copies are the price of the R1CS interface (paper §5.1: inputs used in several constraints
are copied into $w_O$); the native circuit API avoids them. Generators: §3.2 with
$N_{lin}$ and $N'_m$ of the lowered circuit (for a plain R1CS $k$ and $N_m$), from the same
`PedersenGens`/`BulletproofGens` as the BP backend (capacity at least $\max(N'_m, N_{lin} + 6)$,
where BP needs its multipliers rounded up to a power of two), so the input commitments have the
same form in both backends. As for every BP++ input (§3.2), the proof binds the committed values
but not that a commitment has exactly the form $v B + s \tilde B$.

### 6.2 Protocol and encoding

The prover absorbs `domain_sep("bppp-r1cs v2")` after the transcript of the constraint system
(the BP prover's domain separator and the `V` absorbed by `commit`) and runs the reciprocal form
protocol §4 (v1 or v2 as §4.1 decides; its digest binds the lowered circuit). The prover's
randomness is drawn from a transcript RNG rekeyed with the input blindings and the caller's RNG,
and then rekeyed again by `prove` (§1).

The prover's constraint store drops constants (as for BP, so the BP backend pays nothing for
BP++): it recomputes each constant as $-\sum c\, x$ over its witness. For a satisfying witness these
are the verifier's constants; otherwise the prover proves another circuit, whose digest differs,
and the verifier rejects. A witness that violates a multiplicative constraint is refused by the
prover (§3.6).

Randomized constraints (`specify_randomized_constraints`) are not supported: both prover and
verifier return a `GadgetError`. A challenge between the commitments would have to come after
$C_L, C_O$ and before $C_R$ (the reciprocal form's slot), where variables on the right wire are
not yet bound.

Encoding: the byte 4 (BP proofs start with 0 or 1), $N'_m = N_p + N_m$ and $N_{lin}$ as `u64`
little-endian, then the proof (§4.6). Any other first byte is a format error: 2 and 3 were the
BP++ encodings before option B, and a tag-2 proof of a plain R1CS had the same header and body
layout, so the tag changed to make such proofs format errors instead of proofs that only fail
verification. The verifier rejects a proof whose dimensions differ from its own
lowering, and a proof of the other backend.

## 7. The circuit builder (both backends)

`CircuitBuilder` extends `ConstraintSystem` (which is unchanged) with free witnesses, products,
lookups into public tables and general reciprocal arguments. *(2026-10-22: `CircuitBuilder` was merged into
`ConstraintSystem`, the one trait of gadgets; randomized constraints became crate-internal.)* It is implemented by `Prover` and
`Verifier`; a gadget is written once and proven with either backend. The builder only *records*
its operations; at `prove`/`verify` the record is finalized (§7.4) and lowered either to an R1CS
for Bulletproofs (§7.5) or to a reciprocal form circuit for BP++ (§7.6). Prover and verifier run
the same gadget code and therefore record the same operations.

### 7.1 Variables and linear combinations

Variables are those of the R1CS front end — `Committed(j)` ($j < k$), `MultiplierLeft(i)`,
`MultiplierRight(i)`, `MultiplierOutput(i)` ($i < n$, the R1CS multipliers of `multiply`) and
`One` — plus `Witness(i)` for the builder's witnesses ($i < n_w$). *(2026-10-22: `allocate` and
`allocate_multiplier` are gone; `Variable` is opaque to gadgets, which see the variables the
operations return and `Variable::ONE`.)* A linear combination (LC) is a list of terms $(x, c)$, kept in the order given;
its *constant* is the sum of the coefficients of its `One` terms.

Every variable in an LC passed to a builder operation must exist when the operation is called
($j < k$, $i < n$, $i < n_w$ at that moment), otherwise the operation fails with
`GadgetError`. Builder operations exist only in the first phase (the randomizing constraint
systems are internal and have none), so every value the builder sees is committed in the
first phase of BP and before $\alpha$ in BP++.

The R1CS operations record what §6 needs: `multiply(l, r)` creates multiplier $i$, returns
`MultiplierOutput(i)` and appends the constraints $l - a_{L,i}$ and $r - a_{R,i}$ (the terms of
$l$, then $(a_{L,i}, -1)$; likewise for $r$), except for a folded input (§7.1.1); `constrain`
appends its LC. The variables of R1CS constraints are not
checked at the call: both lowerings check them against the final counts (multiplicity witnesses
included; for BP also the second-phase multipliers) and fail with `GadgetError`, as §6.1 does.

Values are read when they are needed, at finalization and lowering (so with the final values of
the multipliers). LCs are lowered as given: terms are neither merged nor dropped (zero
coefficients and repeated variables stay).

#### 7.1.1 Folding (2026-10-22)

An input LC of `multiply` or `constrain_product` that is exactly one term `(Witness(i), 1)` (no
constant) with witness $i$ not yet folded *folds*: witness $i$ becomes that input wire — the left
or right input of R1CS multiplier $i'$ (`multiply`), or of product $g$ (`constrain_product`) — and
the input's linear constraint (§7.1 for `multiply`, §7.6 linear rows 3 for products) is not
emitted. Every reference to `Witness(i)`, before or after, denotes the wire. A witness folds at
most once, into the first input where it stands alone; elsewhere it is read through the wire
(for example the other input of the same multiplier gets the constraint $a_{L,i'} - a_{R,i'}$).
The decision depends on the calls only, so prover and verifier fold alike. The other witnesses
(and the multiplicities, §7.4) are *free*, numbered densely in order ($n_{free}$ of them).

This replaces upstream's `allocate_multiplier`: two fresh witnesses multiplied are a multiplier
with free inputs, at the cost of one multiplier (BP) or one gate and no linear slot (BP++).

### 7.2 Operations

A table has $m \ge 1$ columns; a *tuple* is a list of $m$ LCs (private) or of $m$ `u64` entries
(a public row, entries as scalars). Components are arbitrary field elements: there is no width
or bound (§7.3).

- `witness(v)` → `Witness(n_w)`, $n_w \mathrel{+}= 1$. The prover must supply $v$
  (`MissingAssignment` otherwise).
- `constrain_product(l, r, out)` records the constraint $l \cdot r = out$ (no variables are
  allocated); its lone free witness inputs fold (§7.1.1).
- `table(rows)` → a table id ($0, 1, \dots$ in call order). Fails unless there is at least one row,
  the first row has $m \ge 1$ entries and every row has $m$ entries.
- `lookup(t, tuple)` records that the tuple of $m$ LCs is a row of table $t$. Fails if $t$ does not
  exist or the length differs from $m$.
- `lookup_value(t, v)`: fails unless $t$ has one column; then $x$ = `witness(v)` and
  `lookup(t, [x])`; returns $x$.
- `reciprocal(m)` → an argument id ($0, 1, \dots$ in call order) with $m \ge 1$ columns,
  recorded at once. Terms are added to it one by one, each validated when added (the tuple or
  row has $m$ entries, every variable exists): `reciprocal_term(r, num, tuple)` the private
  term $num / (X + tuple)$ (the handle's `add_weighted`; `add` and `sub` with $num = \pm 1$),
  and `reciprocal_public(r, coeff, row)` the public term $coeff / (X + row)$ for a row of $m$
  `u64` entries (`add_public`). The argument asserts that the terms cancel per tuple: for every
  tuple value, the sum of the numerators (coefficients) of the terms whose tuple has that value
  (component by component) is zero — the sum vanishes as a rational function in which distinct
  tuples are distinct poles. An argument without terms is dropped at finalization (§7.4).

Errors are `GadgetError`; a failed operation records nothing. Without builder operations the
record is empty: BP (§7.5) adds nothing, BP++ (§7.6) lowers the plain R1CS of §6.1.

### 7.3 Tuples

Both backends compress a tuple of $m \ge 2$ components with a challenge drawn after the
components are committed, so a lookup proves that the tuple *is* a table row, component by
component, whatever the components are (no range checks are needed for them):

- BP (§7.5): $c + \sum_j \alpha^j x_j$ with the second-phase challenges `"logup alpha"`,
  `"logup c"`; the components are first-phase values.
- BP++ (§7.6): tuple poles $\sum_j \eta^j x_j$ (§4.1, protocol v2); every component is lowered to
  early columns ($C_O$), with a copy when it reads $w_L$ or $w_R$ (committed after $\eta$).

A one-component tuple is its own pole on both backends ($m = 1$: BP takes $\alpha = 1$, BP++ a free
pole and protocol v1 if no argument has $m \ge 2$). Soundness: §4.7 for BP++; for BP the same
Schwartz–Zippel argument over `"logup alpha"` (bpvm's LogUp).

### 7.4 Finalization

At `prove`/`verify`, before anything is committed:

1. For every table with at least one lookup, in id order: append $|T|$ *multiplicity* witnesses
   `Witness(n_w)`, … (one per row, in row order). The prover sets $m_r$ to the number of lookups
   whose evaluated tuple equals row $r$ (component by component, entries as scalars), counting each lookup for the first
   equal row only, in constant time (every lookup is compared with every row, or, for large tables, a bitonic
   sort of rows and lookups); a lookup equal to no row is a `GadgetError` (prover only).
2. The arguments $\mathcal A$ are the recorded reciprocal arguments with at least one term, in
   the order of their `reciprocal` calls, followed by one
   argument per table with lookups, in id order: the private terms $+1 / (X + q)$ for
   the lookups $q$ in call order, then the public terms $(-m_r) / (X + row_r)$ in row
   order (coefficient: the LC $[(m_r, -1)]$).

Let $n_w$ now include the multiplicities, $n_{prod}$ be the number of products and $N_p$ the
number of private terms of all arguments.

### 7.5 Lowering to Bulletproofs (port of bpvm's LogUp)

After finalization, still in the first phase:

1. Witness multipliers: for $q < \lceil n_{free} / 2 \rceil$, multiplier $n + q$ has left input
   free witness $2q$, right input free witness $2q + 1$ (0 if absent) and their product as
   output; no constraint. Wherever a free witness appears it denotes that wire.
2. For each product $g$ in order: multiplier $n + \lceil n_{free}/2 \rceil + g$ with inputs $l$, $r$
   (constraints $l - a_L$, $r - a_R$ except for folded inputs, which denote these wires), then
   `constrain(o - out)`.
3. For each argument in $\mathcal A$, a randomized constraint (in order): challenges `"logup alpha"`
   (only if $m > 1$; else $\alpha = 1$) and `"logup c"`; $d(x) = c + \sum_j \alpha^j x_j$. For each
   private term $(num, x)$: $(r, d', o)$ = `allocate_multiplier`$(num/d(x), d(x))$,
   `constrain`$(d' - d(x))$, `constrain`$(o - num)$; the prover fails if $d(x) = 0$. Finally
   `constrain`$(\sum r + \sum_{\text{public}} coeff \cdot d(row)^{-1}) = 0$ (both sides fail if
   $d(row) = 0$).

Cost in multipliers: $n + \lceil n_{free}/2 \rceil + n_{prod}$ in the first phase and $N_p$ in the second
(before BP's padding to a power of two). A public term is free.

### 7.6 Lowering to BP++ (reciprocal form, §4)

Dimensions: $n_r = n$, except $n_r = 1$ (one zero multiplier, as in §6) when $n = n_{prod} = N_p = 0$;
$N_m = n_r + n_{prod}$, $N'_m = N_p + N_m$; $N_v = 1$, $k$ inputs, $f_l = [k > 0]$, $f_m = 0$.

**Columns.** $w' = w_D \| w_L \| w_P \| w_R \| w_O$ (§4.1). Pole $i$ is the $i$-th private term in the
order of $\mathcal A$ (argument by argument, terms in order). Gate $i < n_r$ is R1CS multiplier $i$
($w_{L,i} = a_{L,i}$, $w_{R,i} = a_{R,i}$), gate $n_r + g$ is product $g$ ($w_L$, $w_R$ = the values of
$l$ and $r$). $w_O$ is $a_O$ ($n_r$ entries), then the input copies $c_j$ ($k$), then the free
witnesses ($n_{free}$, multiplicities included), then the *copies* below, $N_O$ elements in all. Element $e$ of
$w_O$ goes to slot $(n_O, e)$ if $e < N'_m$, else $(l_O, e - N'_m)$; $N_{lin} = \max(0, N_O - N'_m)$.
A variable maps to a column: `MultiplierLeft(i)` → $w_{L,i}$, `MultiplierRight(i)` → $w_{R,i}$,
`MultiplierOutput(i)` → $w_{O,i}$, `Committed(j)` → $w_{O, n_r + j}$, a free witness with dense
index $f$ → $w_{O, n_r + k + f}$, a folded witness → its wire ($w_{L,i'}$ or $w_{R,i'}$ of multiplier
$i'$, $w_{L, n_r + g}$ or $w_{R, n_r + g}$ of product $g$). Lowering an LC maps each non-`One` term $(x, c)$, in order, to
(column of $x$, $c$); its constant goes to the affine term.

**Copies.** A numerator or a public coefficient must read initial columns only (§4.1), and $w_R$
is committed after $\alpha$; a component of a tuple pole must read early columns only, and $w_L$,
$w_R$ are committed after $\eta$. So, for each argument in $\mathcal A$, for its private terms in
order — first the numerator, then, if $m \ge 2$, the components $j = 0..m-1$ — then its public
terms in order: if the numerator (coefficient) reads a right wire, or the component reads a left
or right wire (any term, whatever its coefficient; a folded witness reads its wire), it is replaced by
a new copy $y$ (the next element of $w_O$; the prover sets $y$ to the LC's value), and the LC
$[(y, 1)]$ is used instead. (Copies are in $w_O$, slots $n_O$ or $l_O$: early columns.)

**Numerators** (row $i$ of $W_n$, $a_{n,i}$): the lowered numerator of pole $i$.

**Multiplicative rows**: gate $i < n_r$: $[(w_{O,i}, 1)]$, $a_m = 0$; gate $n_r + g$: the lowered
$out$ of product $g$ (its constant in $a_m$).

**Linear rows**, in this order:
1. for $j < k$: $[(c_j, -1)]$, $a_l = 0$ (so $v_j - c_j = 0$ through $f_l$);
2. the R1CS constraints in order, lowered (the prover recomputes their constants as in §6.2);
3. for each product $g$: $[(w_{L, n_r + g}, 1)] \| (-l)$ and then $[(w_{R, n_r + g}, 1)] \| (-r)$, where
   $-l$ is the lowered $l$ with negated coefficients and the affine term is $-$(constant of $l$);
   a folded input has no row;
4. for each pole $i$ of an argument with $m = 1$, tuple $(x_0)$: $[(w_{D,i}, 1)] \| (-x_0)$, affine term
   $-$(constant of $x_0$) (poles of arguments with $m \ge 2$ are tuple poles, below);
5. for each copy $y$ of an LC $u$: $[(y, 1)] \| (-u)$, affine term $-$(constant of $u$).

**Tuple poles**, for each pole $i$ of an argument with $m \ge 2$, in pole order: $(i, x_0, \dots,
x_{m-1})$ with $x_j$ the lowered component (terms and constant), or $[(y, 1)]$ with constant 0 for a
copy $y$.

**Reciprocal rows**, one per argument of $\mathcal A$ in order: the terms $(w_{P,i}, 1, \text{none})$ for
its poles in order; then for each public term $(coeff, row)$ in order, the lowered $coeff$ with
the pole polynomial $t = (row_0, \dots, row_{m-1})$ (length $m$) (each term as $(\text{column}, c, t)$, and, if $coeff$ has a `One`
term, the constant $(\text{constant}, t)$, even if it is 0). An argument with public terms only
is a reciprocal row without poles.

**Witness.** $w_{D,i}$ = the value of $x_0$ for a pole of an argument with $m = 1$, and 0 (ignored,
§4.3) for a tuple pole; $w_L$, $w_R$, $w_O$ as above; inputs $v_j$ with blindings $s_j$.

The protocol (v1 or v2) follows from the lowered circuit by §4.1: it uses $\eta$ when $\mathcal A$ has an
argument with $m \ge 2$ and a private term (a tuple pole) or a public term whose coefficient
lowers to at least one term or constant (a pole polynomial of length $m$). An argument with
$m \ge 2$ whose terms are all public with empty coefficients lowers to an empty reciprocal row and
leaves the circuit v1. A circuit of one-column arguments is the circuit of phase 6, byte for byte.

Every rule of §4.1 holds by construction: numerators and pole terms read $w_L$, $w_D$ or $w_O$
(never slot $l_R$); pole-free terms read $w_P$; components of tuple poles read $w_O$ (slots
$n_O$, $l_O$). A pole row (linear rows, step 4) may read $w_R$
(a `MultiplierRight` component): it is an ordinary row, which §4.1 allows, unlike the paper's
eq. (65), where the denominators $W_d w_I$ read the initial witness only. It is sound: the pole
$w_{D,i}$ itself is initial, fixed before $\alpha$, and no ordinary row reads $w_P$, so the row ties
the component to values fixed before $\alpha$. A copy row (step 5) of a component may read $w_L$ or $w_R$
likewise: the copy $y$ is early, fixed before $\eta$, and the row ties the component to it. When $n = 0$ but there are products or poles,
$n_r = 0$ (a circuit of lookups only has $N_m = 0$). Nothing depends on $\alpha$, so the one-phase
prover suffices (a builder operation that exposed reciprocals would need the two-phase prover of
§4.3). Randomized constraints are refused (`GadgetError`), as in §6: mapping a challenge to the slot
between $C_O$ and $C_R$ would leave right-wire values (free inputs of multipliers) unbound there.

Cost in gates: $N'_m = N_p + n_r + n_{prod}$. Free witnesses, multiplicities and copies cost no gate (a
slot in $n_O$ while $N_O \le N'_m$, then a linear slot), nor do public terms, nor the number of
columns $m$ (a component is a row term; one that reads $w_L$ or $w_R$ costs a copy).

### 7.7 Protocol and encoding

BP: the R1CS of §7.5 is proven as usual (unchanged encoding). BP++: §6.2 (one protocol and one
encoding for every constraint system).

### 7.8 Cost summary

| operation | BP multipliers | BP++ gates |
|---|---|---|
| `witness` | 1/2 (0 if folded) | 0 (no slot if folded) |
| `product` | 1 | 1 |
| `lookup`, private reciprocal term | 1 (second phase) | 1 |
| `lookup_value` | 1/2 + 1 | 1 |
| table with lookups ($\lvert T\rvert$ rows) | $\lvert T\rvert/2$ | 0 |
| public reciprocal term | 0 | 0 |
