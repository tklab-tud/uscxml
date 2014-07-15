# Dashboard is opened for submissions for a 24 hour period starting at
# the specified NIGHLY_START_TIME. Time is specified in 24 hour format.
#
# run as: ctest -D Experimental
#
#SET (CTEST_NIGHTLY_START_TIME "23:00:00 EDT")

set(CTEST_PROJECT_NAME "uscxml")
set(CTEST_NIGHTLY_START_TIME "01:00:00 UTC")

set(CTEST_DROP_METHOD "http")
set(CTEST_DROP_SITE "umundo.mintwerk.de")
set(CTEST_DROP_LOCATION "/cdash/submit.php?project=uscxml")
set(CTEST_DROP_SITE_CDASH TRUE)
