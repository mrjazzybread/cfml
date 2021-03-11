make -C ../.. install \
&& make -f ../Makefile.dev _CoqProject \
&& make -f ../Makefile.dev ML=`pwd`/StackSized.ml
# FILE=`basename \`pwd\``
FILE=StackSized
coqide -async-proofs off -async-proofs-command-error-resilience off ${FILE}_ml.v ${FILE}_proof.v &


# make -f ../Makefile.dev `pwd`/UnitTests_ml.v