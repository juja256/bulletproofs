# Bulletproofs++ in this crate: specification

Status: §1–2 pinned (weighted norm linear argument). §3 (arithmetic circuits), §4
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
A vector of length 1 is not folded, and while $b = 1$ neither $\rho$ nor $\mu$ changes (the
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
`domain_sep("bppp-wnla-statement v1")`, point `"C"`, scalar `"rho"`, and every $c_i$ under
`"c"`. The generators are the setup and are not absorbed.

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
