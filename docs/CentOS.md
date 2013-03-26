Install CentOS
Minimal Profile
sudo yum install wget
sudo yum groupinstall "Development tools"


$ wget http://sourceforge.net/projects/boost/files/latest/download
$ tar xvjf boost*
$ cd boost*
$ ./bootstrap.sh
$ ./b2 --layout=tagged install

sudo yum install libtool-ltdl-devel
sudo yum install libxml2-devel
sudo yum install libpng-devel
sudo yum install libjpeg-devel
sudo yum install libtiff-devel
sudo yum install libcurl-devel
sudo yum install mesa-libGL-devel
sudo yum install pcre-devel
sudo yum remove swig

$ wget http://sourceforge.net/projects/openvrml/files/latest/download
$ tar xvjf openvrml*
$ cd openvrml*
$ ./configure --disable-render-text-node --disable-script-node-javascript --disable-script-node-java --disable-gl-renderer --disable-xembed --disable-player --disable-examples
$ make install

$ wget http://www.cmake.org/files/v2.8/cmake-2.8.10.2.tar.gz
$ tar xvzf cmake-2.8.10.2.tar.gz
$ cd cmake-2.8.10
$ ./configure
$ make install

$ svn co http://www.openscenegraph.org/svn/osg/OpenSceneGraph/tags/OpenSceneGraph-3.1.5 OpenSceneGraph
$ cd OpenSceneGraph
$ mkdir build && cd build
$ cmake ..
$ make
$ make install

$ wget http://sourceforge.net/projects/boost/files/latest/download
$ tar xvjf swig*
$ cd swig*
$ ./configure
$ make
$ make install

$ git clone git://github.com/tklab-tud/uscxml.git
$ cd uscxml
$ mkdir build && cd build
$ cmake ..
$ make

