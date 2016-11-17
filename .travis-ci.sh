opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.$COQ_VERSION --yes --verbose

./build.sh

case $DOWNSTREAM in
verdi)
  opam install coq-mathcomp-ssreflect.$SSREFLECT_VERSION --yes --verbose

  pushd ..
    git clone 'http://github.com/uwplse/StructTact'
    pushd StructTact
      ./build.sh
    popd

    git clone 'http://github.com/uwplse/verdi'
    pushd verdi
      ./build.sh
    popd
  popd
  ;;
esac
