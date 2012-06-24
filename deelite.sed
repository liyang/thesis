#! /bin/sed -nf

/^\\begin{code}$/ { n; b code; }
d;

:code;
/^\\end{code}$/ { i\

d; }
p; n; b code;

