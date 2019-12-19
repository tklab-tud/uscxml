from conans import ConanFile, CMake

class Uscxml(ConanFile):
    name = "uscxml"
    version = "1.0"
    url = "uscxml Library"
    description = "<Description of Hello here>"
    settings = "os", "compiler", "build_type", "arch"
    generators = "cmake"
    exports_sources = "src/*", "test/*", "CMakeLists.txt"
    requires ="openssl/1.1.1d"

    def configure_cmake(self):
        cmake = CMake(self)
        cmake.definitions["CMAKE_BUILD_TYPE"] = "Release"
        cmake.configure()
        return cmake

    def build_requirements(self):
        self.build_requires("openssl/1.1.1d")

    def build(self):
        cmake = self.configure_cmake()
        cmake.build()
        cmake.test()

    def package(self):
        self.copy("*.hpp", dst="include", keep_path=False)
        self.copy("*.a", dst="lib", keep_path=False)

    def package_info(self):
        self.cpp_info.libs = ["uscxml"]
