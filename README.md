# Class
Rust library for building IQC: cryptography based on class groups (Cl) of imaginary quadratic orders. 

Background
-------------------
Cls are easy to generate. Their most interesting and useful property is that finding the group order is considered hard. In recent years we see more and more cryptographic primitives instantiated using Cls. We recommend [6,7,8] to learn more about Cls in practice.


Group Element Representation
-------------------
Group Element can be represented as (a,b,c) or (a,b,Δ) triple (correspond to BinaryQF and ABDeltaTriple structures
respectively). We also support compression from the [paper][compression] (see BinaryQFCompressed structure).

[compression]: https://eprint.iacr.org/2020/196.pdf

Primitives
-------------------
Contributions for implementing new primitives or improving existing ones are welcome. See open issues first. Existing primitives can be found in the _primitives_ folder : 

1) **PoE**: Proof of exponantiation: The prover can efficiently convince a verifier that a large exponentiation was done correctly. Statement is `(x,u,w)`, verifier accept if `w = u^x`.

2) **Polynomial commitment**:  The following algorithms are implemented ([1] subsection 4.2 and 4.3):
    + `Setup`: generate public parameters
    + `Commit`: commit to a polynomial
    + `Open`: open and verify a commitment
    + `Encode`: stand alone code to encode a polynomial as an integer
    + `Decode`: converts integer to a unique polynomial
    + `Eval_prover`: NI proof that `y = f(z)` for a committed polynomial `f()`
    + `Eval_verify`: NI verifier for eval_proof.

3) **VDF**: Verifiable Delay Function. Based on Wesolowski protocol [4,5]. The following interface is implemented. The same setup can be used for multiple proofs. `time(Eval) >> time(Verify)`: 
    + `Setup`: generate public key
    + `Eval`: using the public key generate a vdf statement `(y,pi)`
    + `Verify`: verify the statement using the public key
    

4) **Encryption scheme**:  Linearly homomorphic encryption scheme and a ZK proof. interface includes: `Keygen`, `Encrypt`, `Decrypt`, `Prove`, `Verify`. The encryption scheme is taken from [2] Theorem 2. The zero knowledge proof is a non interactive version of the proof given in [3] figure 8. The proof Statement includes a public elliptic curve point `Q = xG` and proves that a given ciphertext is encrypts `x`. The ZK proof has another, experimental variant. This construcction is in use in [2P-ECDSA](https://github.com/KZen-networks/multi-party-ecdsa/tree/master/src/protocols/two_party_ecdsa/cclst_2019). To make to proof more efficient we use the LCM trick. see `dl_cl_lcm.rs`. 


Build
-------------------
Use `Cargo build`. 

**PARI build** 

The library uses bindings to PARI c library. Running `Cargo build` for the first time will take PARI from the _depend_ folder and install it on the machine. It was tested on MacOS and Linux. If you encounter a problem with installation of PARI, please open an issue and try to install it [manually](https://pari.math.u-bordeaux.fr/download.html). Bindings are generated automatically on the fly which might slow down the build procces by a few seconds.


Test
-------------------
Tests in rust are multi-thearded if possible. However, PARI configuration supports a single thread. Therefore to make sure all tests run with defined behaviour please use `cargo test  -- --test-threads=1`. 

**Usage**

We use tests to demonstrate correctness of each primitive: At the end of each primitive `.rs` file there is a test to show the correct usage of the primitive. There is usually one test or more to show soundness of the implementation, i.e. not knowing a witness will fail a PoK. For all tests we assume 128bit security (conservatively translates into 1600bit Discriminant).

Security
-------------------
Security assumptions can differ between primitives and are discussed in the relevant papers. They should be understood well before using any primitive. The code is not audited and we did not attempted to make it constant time. Do not use this library in production system.

Contact
-------------------
Feel free to [reach out](mailto:github@kzencorp.com) or join ZenGo X [Telegram](https://t.me/joinchat/ET1mddGXRoyCxZ-7) for discussions on code and research.

Hall of Fame
-------------------
We would like to thank Fabien Laguillaumie, Guilhem Castagnos, Ida Tucker, Claudio Orlandi and Ben Fisch for their support and on-going help.
We extend our gratitude to [CoBloX research lab](https://coblox.tech/) and [Lloyd Fournier](https://github.com/LLFourn) for contributing code, making this library more secure and fast.

References
-------------------
[1] <https://eprint.iacr.org/2019/1229.pdf>

[2] <https://eprint.iacr.org/2018/791.pdf>

[3] <https://eprint.iacr.org/2019/503.pdf>

[4] <https://eprint.iacr.org/2018/623.pdf>

[5] <https://eprint.iacr.org/2018/712.pdf>

[6] Book: Binary quadratic forms: An algorithmic approach

[7] <https://www.michaelstraka.com/posts/classgroups>

[8] <https://github.com/Chia-Network/vdf-competition/blob/master/classgroups.pdf>
