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

### 2.1 Round

While $a + b \ge 6$:

$$v_x = 2\rho^{-1}\langle [n]_0, [n]_1\rangle_{\mu^2} + \langle [c]_0, [l]_1\rangle + \langle [c]_1, [l]_0\rangle, \qquad v_r = |[n]_1|^2_{\mu^2} + \langle [c]_1, [l]_1\rangle$$

$$X = v_x G + \langle [l]_1, [H]_0\rangle + \langle [l]_0, [H]_1\rangle + \langle \rho [n]_1, [N]_0\rangle + \langle \rho^{-1}[n]_0, [N]_1\rangle$$

$$R = v_r G + \langle [l]_1, [H]_1\rangle + \langle [n]_1, [N]_1\rangle$$

Absorb $X$, $R$; $\gamma$ = challenge. Then $c' = [c]_0 + \gamma[c]_1$, $l' = [l]_0 + \gamma[l]_1$,
$n' = \rho^{-1}[n]_0 + \gamma[n]_1$, $H' = [H]_0 + \gamma[H]_1$, $N' = \rho[N]_0 + \gamma[N]_1$,
$\rho' = \mu$, $\mu' = \mu^2$, $C' = C + \gamma X + (\gamma^2 - 1)R$.

### 2.2 Stop rule

When $a + b < 6$ the prover sends $l$ and $n$. (The paper's protocol box says $< 6$, its text
$\le 6$; we follow the box, as does bp-pp.) The number of rounds $k$ and the final lengths
follow from $(a, b)$ alone: each round maps $(a, b) \mapsto (\lceil a/2\rceil, \lceil b/2\rceil)$.
Lengths need not be powers of two; nothing is padded explicitly.

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

With the round challenges $\gamma_r$ and $\rho_r = \rho^{2^r}$, $r < k$:

- $h_i = l^{(k)}_{\lfloor i/2^k\rfloor} \prod_{r<k} (\text{bit}_r(i)\ ?\ \gamma_r : 1)$ for $i < a$;
- $n_i = n^{(k)}_{\lfloor i/2^k\rfloor} \prod_{r<k} (\text{bit}_r(i)\ ?\ \gamma_r : \rho_r)$ for $i < b$;
- $c^{(k)}$ = $c$ folded with the $\gamma_r$; $\mu_k = \rho^{2^{k+1}}$;
  $v = \langle c^{(k)}, l^{(k)}\rangle + |n^{(k)}|^2_{\mu_k}$.

Accept iff $vG + \langle h, H\rangle + \langle n, N\rangle - C - \sum_r \left(\gamma_r X_r + (\gamma_r^2 - 1) R_r\right) = 0$,
as one multiscalar multiplication. The scalars are exposed (`verification_scalars`) so that
the circuit verifier merges them into its own multiplication.

### 2.5 Encoding

$X_0 R_0 \dots X_{k-1} R_{k-1}\, l^{(k)}\, n^{(k)}$, 32 bytes each; decoding needs $(a, b)$ and
rejects any other length and non-canonical scalars. Point validity is checked on
decompression during verification.
