#include "URL.h"
#include "Foundation/Foundation.h"

#ifdef __has_feature
# if __has_feature(objc_arc)
#   define(HAS_AUTORELEASE_POOL)
# endif
#endif

namespace uscxml {

std::string URL::getResourceDir() {
#if HAS_AUTORELEASE_POOL
  @autoreleasepool {
#else
		NSAutoreleasePool *pool = [[NSAutoreleasePool alloc] init];
#endif
		NSString *resourcePath = [[NSBundle mainBundle] resourcePath];
		return std::string([resourcePath cStringUsingEncoding:NSUTF8StringEncoding]);

#if HAS_AUTORELEASE_POOL
  }
#else
  [pool drain];
#endif
}
	
}
