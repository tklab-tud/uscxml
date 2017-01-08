/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "URL.h"
#include "Foundation/Foundation.h"

#ifdef __has_feature
# if __has_feature(objc_arc)
#   define(HAS_AUTORELEASE_POOL)
# endif
#endif

namespace uscxml {

std::string URL::getResourceDir() {
	std::string path;
#if HAS_AUTORELEASE_POOL
  @autoreleasepool {
#else
    NSAutoreleasePool *pool = [[NSAutoreleasePool alloc] init];
#endif
    NSString *bundleId = [[NSBundle mainBundle] bundleIdentifier];
    if (bundleId != nil) {
        NSString *resourcePath = [[NSBundle mainBundle] resourcePath];
        path = [resourcePath cStringUsingEncoding:NSUTF8StringEncoding];
    } else {
        // we are not actually in a bundle, fall back to /tmp
        NSFileManager *fm = [NSFileManager defaultManager];
        NSURL* resURL = [[fm homeDirectoryForCurrentUser] URLByAppendingPathComponent:@".uscxml"];
        NSString* resPath = [NSString stringWithUTF8String:[resURL fileSystemRepresentation]];
        
        if (![fm fileExistsAtPath:resPath]) {
            [fm createDirectoryAtPath:resPath withIntermediateDirectories:YES attributes:nil error:nil];
        }
        path = [resPath cStringUsingEncoding:NSUTF8StringEncoding];
    }

#if HAS_AUTORELEASE_POOL
  }
#else
  [pool drain];
#endif
	return path;
}
	
}
