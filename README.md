# Class Groups
Rust library for building cryptography based on class groups. The library provides methods to manipulate specific types of quadratic binary forms that are applicable to cryptography. The library is heavily dependent on bindings to [PARI/GP](https://pari.math.u-bordeaux.fr/). 




Primitives
-------------------
The library will evantually support multiple cryptographic primitves. Currently there is support for linearly homomorphic encrytion scheme based on the construction in [CLT18](https://eprint.iacr.org/2018/791.pdf). The scheme is also used in [CCLST19](https://eprint.iacr.org/2019/503.pdf) figures 6 and 7. We like to thank Fabien Laguillaumie and Guilhem Castagnos for their support and on-going help.

Build
-------------------
Running `Cargo build` will also install PARI on the machine. Follow the `test_encryption` test for usage. 

Contact
-------------------
Feel free to [reach out](mailto:github@kzencorp.com) or join the KZen Research [Telegram]( https://t.me/kzen_research) for discussions on code and research.
