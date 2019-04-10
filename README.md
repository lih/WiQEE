[![Travis Build Status](https://travis-ci.org/lih/WiQEE.svg?branch=master)](https://travis-ci.org/lih/WiQEE)

The WiQEE site template
=======================

This is the forge for the [WiQEE project][wiqee]. Its structure is fairly
straightforward : pages (written in Markdown+CaPriCon) are put in
`src/pages`, and you can run `make` to produce a static site from
those pages.

Beyond the obvious (`make` and a shell), the following utilities will
need to be installed on your system beforehand :

  - [SassC][sassc], a SCSS preprocessor, is a Ruby gem, usually found
    in the system package manager. If not, you can install it from the
    above link, or from [the official Sass
    site](https://sass-lang.com/install), whichever is easiest

  - [Pandoc][pandoc] is a general-purpose document converter, which is here used
    to convert Markdown documents into their final HTML form

  - [CaPriCon][capricon] is the proof preprocessor that produces the
    intermediate Markdown files that Pandoc will transform.

That's it ! Once those are installed, run `make`, and your WiQEE
should now be viewable in any ol' browser, by opening one of the HTML
pages that were created in the `public/` directory.

Don't hesitate to open an issue in this repository if you have some
trouble, or suggestions to make it better, or simply questions about
it.

Happy hacking !

[sassc]: https://github.com/sass/sassc
[pandoc]: https://pandoc.org/
[capricon]: https://github.com/lih/BHR/releases
[wiqee]: https://lih.github.io/WiQEE/
