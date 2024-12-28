set -e
set -x

./setup-build.sh
WORKSPACEFOLDER=`pwd`
echo ". $WORKSPACEFOLDER/setenv.sh" >> ~/.bashrc
sudo apt-get install -y --no-install-recommends opam