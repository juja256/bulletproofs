# Bulletproofs++ in this crate: specification

Status: §1–2 (weighted norm linear argument) and §3 (arithmetic circuits) pinned. §4
(reciprocal form), §5 (range proofs, MACT) and §6 (R1CS translation) are written at the start
of the phase that implements them.

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
the circuit protocol its inputs are uniformly distributed (paper, Theorem 2). This crate still
uses constant-time multiscalar multiplications for $X$, $R$ and the commitment; switching is
a performance decision deferred to phase 7.

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

These cancel every coefficient of $d$ except $d_3 = \hat f_3$. Then $C_S$ as in §3.3 with
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

The public `prove`/`verify` absorb the digest (strong Fiat–Shamir). Crate-internal unbound
variants, used where the statement is bound otherwise (R1CS front end, reciprocal form), skip
only the `"circuit"` message.

### 3.9 Circuit digest

SHA3-256 over: the bytes `bppp-circuit-digest v1`; the eight dimensions and flags of §3.8 as
`u64` little-endian; for each $w_{O,i}$ its slot (one byte: 0 $n_O$, 1 $l_O$, 2 $l_L$, 3 $l_R$) and
index (`u64`); for $W_l$ then $W_m$: per row the number of terms (`u64`) and per term the column
(`u64`) and the coefficient (32 bytes), in stored order; then $a_l$ and $a_m$ (32 bytes each).

### 3.10 Encoding

$C_L \| C_R \| C_O \| C_S \|$ norm argument for $|l| = 7 + N_{lin}$, $|n| = N_m$ (§2.5).
