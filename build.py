import os

if __name__ == "__main__":
    # os.system("conan install . --install-folder cmake-build-debug")
    # os.system("conan build . --build-folder cmake-build-debug")
    os.system("conan create . user/testing")