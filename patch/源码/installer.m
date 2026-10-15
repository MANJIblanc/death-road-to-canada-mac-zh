// Standalone macOS installer. Uses only system Foundation and CommonCrypto.
#import <Foundation/Foundation.h>
#import <CommonCrypto/CommonDigest.h>
#include <sys/stat.h>
#include <sys/sysctl.h>
#include <sys/file.h>
#include <unistd.h>
#include <errno.h>

#ifndef PAYLOAD_SHA256
#error PAYLOAD_SHA256 must identify the reviewed payload
#endif
static NSFileManager *fm;
static NSString *packageRoot, *stateRoot, *savesRoot, *steamRoot;
static NSDictionary *payload;
static BOOL failAfterWrite = NO; // enabled only in a separately compiled test binary

static void say(NSString *s) { puts(s.UTF8String); fflush(stdout); }
static void require(BOOL ok, NSString *s) {
    if (!ok) @throw [NSException exceptionWithName:@"InstallerError" reason:s userInfo:nil];
}
static NSString *join(NSString *a, NSString *b) { return [a stringByAppendingPathComponent:b]; }
static NSString *hashData(NSData *d) {
    require(d != nil, @"无法读取待校验文件。");
    unsigned char h[CC_SHA256_DIGEST_LENGTH];
    CC_SHA256(d.bytes, (CC_LONG)d.length, h);
    NSMutableString *s = [NSMutableString new];
    for (int i=0;i<CC_SHA256_DIGEST_LENGTH;i++) [s appendFormat:@"%02x", h[i]];
    return s;
}
static NSData *readData(NSString *p) {
    NSError *e=nil; NSData *d=[NSData dataWithContentsOfFile:p options:0 error:&e];
    require(d != nil, [NSString stringWithFormat:@"无法读取：%@ (%@)",p,e.localizedDescription]); return d;
}
static NSString *hashFile(NSString *p) { return hashData(readData(p)); }
static id json(NSString *p) {
    NSError *e=nil; id obj=[NSJSONSerialization JSONObjectWithData:readData(p) options:NSJSONReadingFragmentsAllowed error:&e];
    require(obj != nil, [NSString stringWithFormat:@"数据文件无效：%@ (%@)",p,e.localizedDescription]); return obj;
}
static void mkdirp(NSString *p) {
    NSError *e=nil; require([fm createDirectoryAtPath:p withIntermediateDirectories:YES attributes:nil error:&e],
                            [NSString stringWithFormat:@"无法建立目录：%@ (%@)",p,e.localizedDescription]);
}
static void writeData(NSData *d, NSString *p, NSNumber *mode) {
    mkdirp(p.stringByDeletingLastPathComponent);
    NSError *e=nil; require([d writeToFile:p options:NSDataWritingAtomic error:&e],
                            [NSString stringWithFormat:@"无法写入：%@ (%@)",p,e.localizedDescription]);
    if(mode) require(chmod(p.fileSystemRepresentation,mode.unsignedShortValue)==0,@"无法设置文件权限。");
}
static void writeJSON(id obj, NSString *p) {
    NSError *e=nil; NSData *d=[NSJSONSerialization dataWithJSONObject:obj options:NSJSONWritingPrettyPrinted error:&e];
    require(d != nil,@"无法保存安装记录。"); writeData(d,p,@0600);
}
static void copy(NSString *a, NSString *b) {
    mkdirp(b.stringByDeletingLastPathComponent); NSError *e=nil;
    require([fm copyItemAtPath:a toPath:b error:&e],
            [NSString stringWithFormat:@"备份失败：%@ (%@)",a,e.localizedDescription]);
}
static void removeItem(NSString *p) {
    NSError *e=nil;
    if([fm fileExistsAtPath:p]) require([fm removeItemAtPath:p error:&e],
                                       [NSString stringWithFormat:@"无法移除：%@ (%@)",p,e.localizedDescription]);
}
static NSString *canonical(NSString *p) {
    p=p.stringByExpandingTildeInPath;
    if(!p.isAbsolutePath) p=join(fm.currentDirectoryPath,p);
    return p.stringByStandardizingPath.stringByResolvingSymlinksInPath;
}
static BOOL safeRelative(NSString *r) {
    return [r isKindOfClass:NSString.class] && r.length && !r.isAbsolutePath &&
           ![r.pathComponents containsObject:@".."] && ![r.pathComponents containsObject:@"."];
}
static NSString *targetPath(NSString *app, NSString *r) {
    require(safeRelative(r),@"补丁或记录含无效文件路径。");
    NSString *p=join(app,r);
    require([canonical(p) hasPrefix:[canonical(app) stringByAppendingString:@"/"]],@"游戏中的文件链接指向外部目录，停止覆盖。");
    return p;
}
static void gameClosed(void) {
    int mib[]={CTL_KERN,KERN_PROC,KERN_PROC_ALL,0}; size_t n=0;
    require(sysctl(mib,4,NULL,&n,NULL,0)==0,@"无法检查游戏进程。");
    n=n*2+4096; NSMutableData *d=[NSMutableData dataWithLength:n];
    require(sysctl(mib,4,d.mutableBytes,&n,NULL,0)==0,@"无法检查游戏进程，请重试。");
    struct kinfo_proc *ps=d.mutableBytes;
    for(size_t i=0;i<n/sizeof(*ps);i++)
        require(strcmp(ps[i].kp_proc.p_comm,"DR2C")!=0,@"游戏正在运行。请完全退出游戏后重试。");
}
static NSDictionary *loadPayload(void) {
    NSString *p=join(packageRoot,@"Payload/patches.json");
    require([hashFile(p) isEqual:@PAYLOAD_SHA256],@"安装包不完整或已被修改，请重新解压完整压缩包。");
    NSDictionary *d=json(p);
    require([d[@"schema"] isEqual:@1] && [d[@"files"] isKindOfClass:NSArray.class],@"不支持此补丁格式。");
    NSMutableSet *seen=[NSMutableSet new];
    for(NSDictionary *item in d[@"files"]) {
        NSString *r=item[@"path"];
        require(safeRelative(r) && ![seen containsObject:r],@"补丁包含重复或不安全路径。"); [seen addObject:r];
        if(item[@"source_path"]!=NSNull.null) require(safeRelative(item[@"source_path"]),@"补丁来源路径无效。");
        if(item[@"asset"]) {
            require(safeRelative(item[@"asset"]),@"补丁资源路径无效。");
            require([hashFile(join(packageRoot,item[@"asset"])) isEqual:item[@"target_sha256"]],@"汉化模块或字库损坏，请重新解压。");
        }
    }
    return d;
}
static NSData *patched(NSData *base, NSDictionary *item) {
    if(item[@"asset"]) return readData(join(packageRoot,item[@"asset"]));
    NSMutableData *d=[NSMutableData new];
    for(NSDictionary *op in item[@"ops"]) {
        if(op[@"copy"]) {
            NSArray *range=op[@"copy"]; require(range.count==2,@"差异补丁范围无效。");
            uint64_t off=[range[0] unsignedLongLongValue],len=[range[1] unsignedLongLongValue];
            require(off<=base.length && len<=base.length-off,@"差异补丁超出原文件范围。");
            [d appendBytes:(const char *)base.bytes+off length:(NSUInteger)len];
        } else {
            NSData *literal=[[NSData alloc] initWithBase64EncodedString:op[@"data"] options:0];
            require(literal!=nil,@"差异补丁内容无效。"); [d appendData:literal];
        }
        require(d.length<=[item[@"target_size"] unsignedLongLongValue],@"差异补丁输出过长。");
    }
    require(d.length==[item[@"target_size"] unsignedLongLongValue],@"差异补丁输出长度不符。"); return d;
}
static NSString *statePath(NSString *app) {
    NSString *key=[hashData([canonical(app) dataUsingEncoding:NSUTF8StringEncoding]) substringToIndex:24];
    return join(join(stateRoot,key),@"state.json");
}
static NSMutableDictionary *readState(NSString *app) {
    NSString *p=statePath(app); if(![fm fileExistsAtPath:p]) return nil;
    NSMutableDictionary *s=[json(p) mutableCopy];
    require([s[@"app"] isEqual:canonical(app)] && [s[@"files"] isKindOfClass:NSArray.class],@"安装记录与游戏位置不符。");
    return s;
}
static void checkExecutable(NSString *app, NSString *expected) {
    require([fm fileExistsAtPath:join(app,@"Contents/MacOS/DR2C")],@"没有找到 DR2C.app，请选取 Mac Steam 游戏。");
    require([hashFile(join(app,@"Contents/MacOS/DR2C")) isEqual:expected],
            @"游戏版本不匹配，未修改游戏。本补丁只支持 Steam build 24936165 的已核验 Mac 程序；更新版本需要重新适配。");
}
static void checkCurrent(NSString *app, NSDictionary *s) {
    for(NSDictionary *item in s[@"files"]) {
        NSString *p=targetPath(app,item[@"path"]);
        require([fm fileExistsAtPath:p] && [hashFile(p) isEqual:item[@"target_sha256"]],
                [NSString stringWithFormat:@"文件与安装记录不同，未继续覆盖：%@。可能是 Steam 更新或其他模组，请先检查。",item[@"path"]]);
    }
}
static NSString *newBackupDir(NSString *app) {
    NSString *parent=join(statePath(app).stringByDeletingLastPathComponent,@"backups");
    NSDateFormatter *fmt=[NSDateFormatter new]; fmt.dateFormat=@"yyyyMMdd-HHmmss";
    return join(parent,[NSString stringWithFormat:@"%@-%@",[fmt stringFromDate:NSDate.date],[NSUUID.UUID.UUIDString substringToIndex:8]]);
}
static void backupSaves(NSString *backup) {
    if([fm fileExistsAtPath:savesRoot]) copy(savesRoot,join(backup,@"DR2C-saves"));
    NSString *users=join(steamRoot,@"userdata");
    for(NSString *user in [fm contentsOfDirectoryAtPath:users error:nil]) {
        NSString *p=join(join(users,user),@"252610");
        if([fm fileExistsAtPath:p]) copy(p,join(join(backup,@"Steam-save-metadata"),user));
    }
}
static void verifyBackup(NSString *app, NSDictionary *s) {
    NSString *backup=s[@"backup"];
    require([backup isKindOfClass:NSString.class] && backup.isAbsolutePath,@"备份目录记录无效。");
    for(NSDictionary *item in s[@"files"]) if([item[@"existed"] boolValue]) {
        NSString *p=targetPath(join(backup,@"DR2C.app"),item[@"path"]);
        require([fm fileExistsAtPath:p] && [hashFile(p) isEqual:item[@"original_sha256"]],
                [NSString stringWithFormat:@"原版备份缺失或损坏，未修改游戏：%@",item[@"path"]]);
    }
}
static void originalFiles(NSString *app, NSDictionary *s) {
    for(NSDictionary *item in s[@"files"]) {
        NSString *p=targetPath(app,item[@"path"]);
        if([item[@"existed"] boolValue]) writeData(readData(targetPath(join(s[@"backup"],@"DR2C.app"),item[@"path"])),p,item[@"mode"]);
        else removeItem(p);
    }
    for(NSDictionary *item in s[@"files"]) {
        NSString *p=targetPath(app,item[@"path"]);
        require([item[@"existed"] boolValue] ? [hashFile(p) isEqual:item[@"original_sha256"]] : ![fm fileExistsAtPath:p],@"原版恢复校验失败。");
    }
}
static void install(NSString *app) {
    gameClosed(); checkExecutable(app,payload[@"game_sha256"]);
    NSMutableDictionary *old=readState(app);
    if([old[@"status"] isEqual:@"installed"]) {
        checkCurrent(app,old);
        require([old[@"payload_sha256"] isEqual:@PAYLOAD_SHA256],@"已安装其他版本，请先双击“还原原版”再安装本版。");
        say(@"此版本汉化已安装，文件校验通过。"); return;
    }
    require(!old || [old[@"status"] isEqual:@"restored"],@"发现未完成的操作。请先运行“还原原版”恢复，再重新安装。");
    NSMutableArray *records=[NSMutableArray new]; NSMutableDictionary *staged=[NSMutableDictionary new];
    // Build and validate every output in memory before any write to the game.
    for(NSDictionary *item in payload[@"files"]) {
        NSString *r=item[@"path"], *dest=targetPath(app,r); BOOL exists=[fm fileExistsAtPath:dest];
        require(exists==[item[@"existed"] boolValue], [NSString stringWithFormat:@"游戏包含其他补丁或缺少文件，未修改：%@",r]);
        NSString *source=item[@"source_path"]==NSNull.null ? nil : targetPath(app,item[@"source_path"]);
        NSData *base=source ? readData(source) : [NSData data];
        require([hashData(base) isEqual:item[@"base_sha256"]], [NSString stringWithFormat:@"原文件不匹配，未修改：%@。请使用对应版本的原版游戏。",item[@"source_path"]]);
        NSData *result=patched(base,item);
        require([hashData(result) isEqual:item[@"target_sha256"]],@"差异补丁生成校验失败，未修改游戏。");
        NSNumber *mode=exists ? [fm attributesOfItemAtPath:dest error:nil][NSFilePosixPermissions] : @0644;
        if([r.lastPathComponent hasPrefix:@"SDL2_mixer"]) mode=@0755;
        [records addObject:@{@"path":r,@"existed":@(exists),@"original_sha256":exists?hashFile(dest):NSNull.null,
                             @"target_sha256":item[@"target_sha256"],@"mode":mode}]; staged[r]=result;
    }
    NSString *backup=newBackupDir(app); mkdirp(backup);
    say(@"版本与文件检查通过，正在备份原游戏及存档……");
    copy(app,join(backup,@"DR2C.app")); backupSaves(backup);
    NSMutableDictionary *s=[@{@"schema":@1,@"status":@"installing",@"app":canonical(app),@"backup":backup,
                             @"game_sha256":payload[@"game_sha256"],@"package_id":payload[@"package_id"],
                             @"payload_sha256":@PAYLOAD_SHA256,@"files":records} mutableCopy];
    verifyBackup(app,s); gameClosed(); writeJSON(s,statePath(app));
    @try {
        for(NSDictionary *item in records) {
            writeData(staged[item[@"path"]],targetPath(app,item[@"path"]),item[@"mode"]);
#ifdef INSTALLER_TEST_FAULT
            if(failAfterWrite) @throw [NSException exceptionWithName:@"TestFailure" reason:@"模拟中途写入失败" userInfo:nil];
#endif
        }
        checkCurrent(app,s); checkExecutable(app,payload[@"game_sha256"]);
        s[@"status"]=@"installed"; writeJSON(s,statePath(app));
    } @catch(NSException *e) {
        say(@"安装未完成，正在恢复原文件……"); originalFiles(app,s);
        s[@"status"]=@"restored"; writeJSON(s,statePath(app)); @throw e;
    }
    say([NSString stringWithFormat:@"汉化已安装：%@\n原版与存档备份：%@\n以后从 Steam 正常启动即可。",app,backup]);
}
static void restore(NSString *app) {
    gameClosed(); NSMutableDictionary *s=readState(app); require(s!=nil,@"此游戏没有本工具的安装记录。");
    if([s[@"status"] isEqual:@"restored"]) { say(@"此游戏已经还原，当前存档保留。"); return; }
    checkExecutable(app,s[@"game_sha256"]); verifyBackup(app,s);
    if([s[@"status"] isEqual:@"installed"]) checkCurrent(app,s);
    else {
        for(NSDictionary *item in s[@"files"]) {
            NSString *p=targetPath(app,item[@"path"]);
            BOOL exists=[fm fileExistsAtPath:p]; NSString *h=exists?hashFile(p):@"";
            require((exists && ([h isEqual:item[@"target_sha256"]] || [h isEqual:item[@"original_sha256"]])) ||
                    (!exists && ![item[@"existed"] boolValue]),@"未完成的操作中有文件又被其他程序修改，停止自动还原。");
        }
    }
    // Keep a full, verified snapshot so a failed restore can roll back as well.
    NSMutableDictionary *current=[NSMutableDictionary new];
    for(NSDictionary *item in s[@"files"]) {
        NSString *p=targetPath(app,item[@"path"]); current[item[@"path"]]=[fm fileExistsAtPath:p] ? readData(p) : NSNull.null;
    }
    NSString *before=s[@"status"]; s[@"status"]=@"restoring"; writeJSON(s,statePath(app));
    @try { originalFiles(app,s); s[@"status"]=@"restored"; writeJSON(s,statePath(app)); }
    @catch(NSException *e) {
        for(NSDictionary *item in s[@"files"]) {
            id d=current[item[@"path"]]; NSString *p=targetPath(app,item[@"path"]);
            if(d==NSNull.null) removeItem(p); else writeData(d,p,item[@"mode"]);
        }
        s[@"status"]=before; writeJSON(s,statePath(app)); @throw e;
    }
    say([NSString stringWithFormat:@"已恢复原版游戏文件，当前存档保留。\n安装前的游戏与存档备份仍保留在：%@",s[@"backup"]]);
}
static void status(NSString *app) {
    NSMutableDictionary *s=readState(app);
    if(!s) { checkExecutable(app,payload[@"game_sha256"]); say(@"游戏版本支持；此工具尚未安装汉化。"); return; }
    say([NSString stringWithFormat:@"游戏：%@\n状态：%@\n备份：%@",app,s[@"status"],s[@"backup"]]);
    checkExecutable(app,s[@"game_sha256"]);
    if([s[@"status"] isEqual:@"installed"]) { checkCurrent(app,s); say(@"汉化文件校验通过。"); }
    else if([s[@"status"] isEqual:@"restored"]) {
        for(NSDictionary *item in s[@"files"]) {
            NSString *p=targetPath(app,item[@"path"]);
            require([item[@"existed"] boolValue] ? [hashFile(p) isEqual:item[@"original_sha256"]] : ![fm fileExistsAtPath:p],@"还原后的游戏文件又发生变化。");
        }
        say(@"已还原文件校验通过。");
    } else require(NO,@"操作未完成，请运行“还原原版”恢复。");
}
static NSArray *discover(void) {
    NSMutableOrderedSet *libs=[NSMutableOrderedSet orderedSetWithObject:steamRoot];
    NSString *vdf=[NSString stringWithContentsOfFile:join(steamRoot,@"steamapps/libraryfolders.vdf") encoding:NSUTF8StringEncoding error:nil];
    NSRegularExpression *re=[NSRegularExpression regularExpressionWithPattern:@"\"(?:path|[0-9]+)\"\\s*\"([^\"]+)\"" options:0 error:nil];
    for(NSTextCheckingResult *m in [re matchesInString:vdf?:@"" options:0 range:NSMakeRange(0,vdf.length)]) {
        NSString *p=[vdf substringWithRange:[m rangeAtIndex:1]];
        if(p.isAbsolutePath) [libs addObject:[p stringByReplacingOccurrencesOfString:@"\\\\" withString:@"\\"]];
    }
    NSMutableOrderedSet *apps=[NSMutableOrderedSet new];
    for(NSString *lib in libs) {
        NSString *steamapps=join(lib,@"steamapps");
        NSMutableOrderedSet *dirs=[NSMutableOrderedSet orderedSetWithObject:join(steamapps,@"common/DeathRoadToCanada")];
        NSString *acf=[NSString stringWithContentsOfFile:join(steamapps,@"appmanifest_252610.acf") encoding:NSUTF8StringEncoding error:nil];
        NSRegularExpression *dirRE=[NSRegularExpression regularExpressionWithPattern:@"\"installdir\"\\s*\"([^\"]+)\"" options:0 error:nil];
        NSTextCheckingResult *m=[dirRE firstMatchInString:acf?:@"" options:0 range:NSMakeRange(0,acf.length)];
        if(m) { NSString *r=[acf substringWithRange:[m rangeAtIndex:1]]; if(safeRelative(r)) [dirs addObject:join(join(steamapps,@"common"),r)]; }
        for(NSString *dir in dirs) {
            NSString *a=join(dir,@"DR2C.app");
            if([fm fileExistsAtPath:join(a,@"Contents/MacOS/DR2C")]) [apps addObject:canonical(a)];
        }
    }
    // Restoration still finds a previously installed copy after the package is moved.
    for(NSString *key in [fm contentsOfDirectoryAtPath:stateRoot error:nil]) {
        NSString *p=join(join(stateRoot,key),@"state.json");
        if([fm fileExistsAtPath:p]) {
            NSDictionary *s=json(p); NSString *a=s[@"app"];
            if([a isKindOfClass:NSString.class] && [fm fileExistsAtPath:join(a,@"Contents/MacOS/DR2C")]) [apps addObject:canonical(a)];
        }
    }
    return apps.array;
}
static NSString *inputLine(void) {
    char *line=NULL; size_t n=0; ssize_t len=getline(&line,&n,stdin);
    require(len>=0,@"没有输入游戏路径。可把 DR2C.app 拖到“安装汉化.command”上。");
    NSString *s=[[NSString alloc] initWithBytes:line length:len encoding:NSUTF8StringEncoding]; free(line);
    return [s stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
}
static NSString *draggedPath(NSString *s) {
    // Finder/Terminal escapes spaces. Parse escapes without evaluating shell code.
    if(s.length>=2 && (([s hasPrefix:@"'"] && [s hasSuffix:@"'"]) || ([s hasPrefix:@"\""] && [s hasSuffix:@"\""]))) s=[s substringWithRange:NSMakeRange(1,s.length-2)];
    NSMutableString *r=[NSMutableString new];
    for(NSUInteger i=0;i<s.length;i++) { unichar c=[s characterAtIndex:i]; if(c=='\\' && i+1<s.length)c=[s characterAtIndex:++i]; [r appendFormat:@"%C",c]; }
    return canonical(r);
}
int main(int argc,const char **argv) { @autoreleasepool {
    fm=NSFileManager.defaultManager;
    NSString *home=NSHomeDirectory();
    stateRoot=join(home,@"Library/Application Support/DR2C-Mac-Hans");
    savesRoot=join(home,@"Library/Application Support/DR2C");
    steamRoot=join(home,@"Library/Application Support/Steam");
    packageRoot=canonical([NSString stringWithUTF8String:argv[0]]).stringByDeletingLastPathComponent;
    packageRoot=packageRoot.stringByDeletingLastPathComponent;
    NSString *action=nil,*app=nil; int lockFD=-1;
    @try {
        for(int i=1;i<argc;i++) {
            NSString *a=[NSString stringWithUTF8String:argv[i]];
            if([a isEqual:@"--app"] || [a isEqual:@"--state-root"] || [a isEqual:@"--saves-root"] || [a isEqual:@"--steam-root"]) {
                require(i+1<argc,@"缺少参数路径。"); NSString *v=canonical([NSString stringWithUTF8String:argv[++i]]);
                if([a isEqual:@"--app"]) app=v; else if([a isEqual:@"--state-root"]) stateRoot=v; else if([a isEqual:@"--saves-root"]) savesRoot=v; else steamRoot=v;
            }
#ifdef INSTALLER_TEST_FAULT
            else if([a isEqual:@"--fail-after-write"]) failAfterWrite=YES;
#endif
            else if(!action) action=a; else require(NO,@"不支持的参数。");
        }
        require([@[@"install",@"restore",@"status",@"verify",@"list"] containsObject:action],@"用法：installer install|restore|status|verify|list [--app /路径/DR2C.app]");
        payload=loadPayload();
        if([action isEqual:@"verify"]) { say(@"安装包完整性校验通过。"); return 0; }
        NSArray *apps=discover();
        if([action isEqual:@"list"]) { for(NSString *a in apps)say(a); return 0; }
        if(!app) {
            if(apps.count==1) app=apps[0];
            else {
                if(apps.count) { say(@"找到多个游戏位置，请输入序号："); for(NSUInteger i=0;i<apps.count;i++)say([NSString stringWithFormat:@"%lu. %@",(unsigned long)i+1,apps[i]]); }
                else say(@"未自动找到游戏。请把 DR2C.app 拖入此窗口，然后按回车：");
                NSString *line=inputLine();
                if(apps.count && [line rangeOfCharacterFromSet:NSCharacterSet.decimalDigitCharacterSet.invertedSet].location==NSNotFound) {
                    NSInteger index=line.integerValue; require(index>=1 && index<=(NSInteger)apps.count,@"序号无效，未修改游戏。"); app=apps[index-1];
                } else app=draggedPath(line);
            }
        }
        require([app.pathExtension.lowercaseString isEqual:@"app"],@"请选择 DR2C.app 游戏应用。");
        say([NSString stringWithFormat:@"目标游戏：%@",app]);
        // Serialize all mutations across copies and package versions.
        if(![action isEqual:@"status"]) {
            mkdirp(stateRoot); chmod(stateRoot.fileSystemRepresentation,0700);
            NSString *p=join(stateRoot,@"installer.lock"); lockFD=open(p.fileSystemRepresentation,O_CREAT|O_RDWR,0600);
            require(lockFD>=0 && flock(lockFD,LOCK_EX|LOCK_NB)==0,@"另一个安装或还原操作正在运行，请稍后重试。");
        }
        if([action isEqual:@"install"])install(app); else if([action isEqual:@"restore"])restore(app); else status(app);
        if(lockFD>=0)close(lockFD); return 0;
    } @catch(NSException *e) { if(lockFD>=0)close(lockFD); fprintf(stderr,"\n未完成：%s\n",e.reason.UTF8String); return 1; }
} }
