# samples2ltl
git submodule init
git submodule update
cd samples2ltl
python -m venv env
source env/bin/activate
pip install -r requirements.txt
python3 samples2LTL.py --sat --traces traces/alt.trace
if [ $? -ne 0 ]; then echo "Failed to install Samples2LTL"; exit 1; fi
cd ..

# # JHoafParser
cd lib
mvn install:install-file -Dfile=jhoafparser-1.1.1.jar -DgroupId=jhoafparser -DartifactId=jhoafparser -Dversion=1.1.1 -Dpackaging=jar -DgeneratePom=true

# TChecker binaries
if [ "$(uname -m)" = "x86_64" ] && [ "$(uname -s)" = "Linux" ]; then
    wget https://github.com/osankur/tchecker/releases/download/v0.8-71-gd711ace/tchecker-Linux_x86_64-0.8-71-gd711ace.tar.gz
    tar -xzf tchecker-Linux_x86_64-0.8-71-gd711ace.tar.gz --strip-components=1
else
    echo "Only Linux x86_64 TChecker binaries are available. Please compile TChecker yourself and add the binaries to your path: https://github.com/ticktac-project/tchecker/"
    exit 1
fi

# Spot
wget http://www.lre.epita.fr/dload/spot/spot-2.15.1.tar.gz
tar -xzf spot-2.15.1.tar.gz
cd spot-2.15.1/
./configure #--prefix ~/usr
make -j$(nproc)
sudo make install

# Compile JAR
sbt assembly
