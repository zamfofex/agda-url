Agda URL implementation
===

This is an Agda implementation of URLs as defined in <https://alwinb.github.io/url-specification/>

The goal is to eventually be able to write proofs about some of the interesting properties established therein and possibly others.

To try it out, the `Main/AgdaURL.agda` serves as an entry point. After compiling it, simply write a URL as the first line to stdin, and it should output information about it to stdout.

~~~ sh
agda --ghc Main/AgdaURL.agda
echo 'https://alwinb.github.io/url-specification/#parsing' | ./AgdaURL
~~~

For now, only parsing is implemented, and host parsing is incomplete.

- **TODO:** Implement a better host parser.
- **TODO:** Implement punycoding.
- **TODO:** Implement percent‐encoding.
- **TODO:** Implement the “goto” operation.
- **TODO:** Implement forcing.
- **TODO:** Implement normalization.
- **TODO:** Implement resolution.
- **TODO:** Write proofs for the URL operation properties.
- **TODO:** Test against the WPT suite.

Ideas, sugestions and any other forms of feedback are all welcome!

license — 0BSD
---

copyright © 2021 by zamfofex

Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED “AS IS” AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
