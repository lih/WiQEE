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

### Integration with GitHub Pages

This WiQEE comes equipped with a fully-functional Travis CI
configuration that automatically builds all commits pushed on the
`master` branch, and uploads them to GitHub Pages.

In short, if you want to host your own version of this WiQEE on
GitHub, all you have to do is :

  - fork this project on GitHub
  - enable GitHub Pages on the branch called `gh-pages` in the
    settings page of your fork
  - log into [Travis CI] with your GitHub account, and enable the
    service for your newly-forked repository (it should be
    automatically detected by Travis).
  - allow Travis to upload the pages back to GitHub :
     - generate a new [GitHub Access
       Token](https://github.com/settings/tokens) (or reuse a previous
       one, but good security recommends the former)
     - set the variable GITHUB_API_KEY to that new token, in the
       "Settings" page of your project on Travis (at
       https://travis-ci.org/$USERNAME/WiQEE/settings)
  - commit to `master`, and wait a few minutes (8-10 minutes, because
    Travis reinstalls LaTeX each time). If all goes well, your own
    WiQEE should be fully-functional and available on
    https://$USERNAME.github.io/WiQEE .

### Questions ?

Don't hesitate to open an issue in this repository if you have some
trouble, or suggestions to make it better, or simply questions about
it.

Happy hacking !

[Travis CI]: https://travis-ci.org/
[sassc]: https://github.com/sass/sassc
[pandoc]: https://pandoc.org/
[capricon]: https://github.com/lih/BHR/releases
[wiqee]: https://lih.github.io/WiQEE/
