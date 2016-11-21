opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.$COQ_VERSION --yes --verbose

./build.sh

case $DOWNSTREAM in
verdi-aggregation)
  opam install coq.$COQ_VERSION coq-mathcomp-ssreflect.$MATHCOMP_VERSION coq-mathcomp-fingroup.$MATHCOMP_VERSION coq-mathcomp-algebra.$MATHCOMP_VERSION --yes --verbose

  pushd ..
    git clone 'https://github.com/uwplse/StructTact.git'
    pushd StructTact
      ./build.sh
    popd

    git clone 'https://github.com/uwplse/verdi.git'
    pushd verdi
      ./build.sh
    popd

    git clone -b v8.5 'https://github.com/coq-contribs/aac-tactics.git' AAC_tactics
    pushd AAC_tactics
      make
    popd

    git clone 'https://github.com/DistributedComponents/verdi-aggregation.git'
    pushd verdi-aggregation
      ./build.sh
    popd
  popd
  ;;
esac
