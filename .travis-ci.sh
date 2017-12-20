set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq ${COQ_VERSION} --yes

opam pin add InfSeqExt . --yes --verbose

case ${DOWNSTREAM} in
verdi)
  opam install verdi --yes --verbose
  ;;
esac
