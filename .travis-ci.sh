opam init --yes --no-setup
eval $(opam config env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq --yes

./build.sh

case $DOWNSTREAM in
verdi)
  opam install coq-mathcomp-ssreflect --yes

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
