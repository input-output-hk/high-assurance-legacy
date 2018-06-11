Setup
=====

In order to use the Isabelle developments in this directory, please add
the path of this directory to the file `$ISABELLE_HOME_USER/ROOTS`. You
can find out the value of `$ISABELLE_HOME_USER` by running the following
command:

    isabelle getenv ISABELLE_HOME_USER


Building
========

Running `make` builds the PDF documents for the different Isabelle
sessions (“packages”) and places them in
`$ISABELLE_BROWSER_INFO/Cardano`. You can find out the value of
`$ISABELLE_BROWSER_INFO` by running the following command:

    isabelle getenv ISABELLE_BROWSER_INFO
