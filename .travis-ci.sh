set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq $COQ_VERSION --yes --verbose

./build.sh

case $DOWNSTREAM in
verdi)
  opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
  opam install coq-mathcomp-ssreflect.$SSREFLECT_VERSION StructTact --yes --verbose
  pushd ..
    git clone 'https://github.com/uwplse/verdi.git'
    pushd verdi
      InfSeqExt_PATH=../InfSeqExt ./build.sh
    popd
  popd
  ;;
esac
