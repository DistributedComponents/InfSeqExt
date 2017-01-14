set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents http://opam.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose

./build.sh

case $DOWNSTREAM in
verdi-aggregation)
  opam install coq-mathcomp-ssreflect.$MATHCOMP_VERSION \
    coq-mathcomp-fingroup.$MATHCOMP_VERSION coq-mathcomp-algebra.$MATHCOMP_VERSION \
    coq-aac-tactics.$AAC_TACTICS_VERSION InfSeqExt StructTact verdi --yes --verbose

  pushd ..
    git clone 'https://github.com/DistributedComponents/verdi-aggregation.git'
    pushd verdi-aggregation
      ./build.sh
    popd
  popd
  ;;
esac
