mkdir -p shared
cp make_deps_guest.sh shared
cp Makefile.deps shared
docker run -tiv `pwd`/shared:/shared gtksourceview bash /shared/make_deps_guest.sh
