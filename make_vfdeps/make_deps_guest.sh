set -ex
apt-get install -y m4
export PATH=/tmp/vfdeps/bin:$PATH
cd /tmp && make -f /shared/Makefile.deps PREFIX=/tmp/vfdeps
cd /tmp && tar cjf /shared/vfdeps.tar.xz vfdeps
