// Local macOS display adapter. Game scripts and persistent identifiers stay original.
#include <OpenGL/gl.h>
#include <CommonCrypto/CommonDigest.h>
#include <mach/mach.h>
#include <mach/mach_vm.h>
#include <mach-o/dyld.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <regex.h>
#include <assert.h>
#include <stdarg.h>
#include "addresses.h"
#include "translations.h"
#include "format_patterns.h"

typedef struct { int32_t id, base, count; } Font;
typedef struct { int16_t xywh[16]; void *atlas; } Sprite;
_Static_assert(sizeof(Sprite) == 40, "Mac sprite layout");
typedef struct Cache { struct Cache *next; uint64_t hash; char *key, *value; } Cache;
static Cache *cache[8192];
static intptr_t slide;
static FILE *logfile;
static char resources[PATH_MAX], test_save[PATH_MAX];
static double *turtle;
static Font *default_font;
static int (**glyph_callback)(int, int, void *);
static void **glyph_context;
static Sprite *(*sprite_get)(int);
static void *(*sprite_plot)(Sprite *, int, int);
static void (*turtle_trans)(double, double);
static int (*original_glyphs)(Font *, const char *, int, int, int);
static int (*original_plot)(const char *, int, int, Font *);
static int (*original_upload)(void *, int, int);
static int (*original_wrapped)(const char *,int,int,int,int,Font *);
static unsigned char *(*image_load)(const char *, int *, int *, int *, int);
static void *combined_atlas;
static int original_width, original_height;
static bool font_ready;

static void *at(uint64_t a) { return (void *)(uintptr_t)(a + slide); }
static uint64_t hash_string(const char *s) { uint64_t h=1469598103934665603ULL; while(*s) { h^=(unsigned char)*s++;h*=1099511628211ULL; }return h; }
static const char *translate(const char *s);
static uint32_t decode(const char *s,size_t available,size_t *bytes);
static char *pattern_translate(const char *s) {
    regmatch_t matches[10];
    for(size_t i=0;i<sizeof(display_patterns)/sizeof(display_patterns[0]);i++) {
        DisplayPattern *p=&display_patterns[i];
        if(!p->ready){if(regcomp(&p->regex,p->pattern,REG_EXTENDED))continue;p->ready=true;}
        if(regexec(&p->regex,s,10,matches,0))continue;
        size_t cap=strlen(s)*6+2048,n=0;char *out=malloc(cap);
        for(const char *q=p->output;*q;q++) {
            if(*q=='@' && q[1]>='1' && q[1]<='9') {
                int k=*++q-'0';if(matches[k].rm_so<0)continue;
                char *part=strndup(s+matches[k].rm_so,matches[k].rm_eo-matches[k].rm_so);
                const char *value=(p->translate_mask&(1U<<k))?translate(part):part;size_t length=strlen(value);
                if(n+length+1>=cap){cap=(n+length+1)*2;out=realloc(out,cap);}memcpy(out+n,value,length);n+=length;free(part);
            } else {if(n+2>=cap){cap*=2;out=realloc(out,cap);}out[n++]=*q;}
        }
        out[n]=0;if(!strcmp(out,s)){free(out);continue;}return out;
    }
    return NULL;
}
// Colour effects wrap many canonical labels before they reach the renderer.
// Preserve those control bytes and migrate just the complete enclosed label.
static char *decorated_translate(const char *s) {
    size_t length=strlen(s),lead=0,tail=0,bytes;
    while(lead<length){uint32_t cp=decode(s+lead,length-lead,&bytes);if(bytes!=1 || !(cp==' ' || cp>=0xF0))break;lead+=bytes;}
    for(size_t i=lead;i<length;i+=bytes) {
        uint32_t cp=decode(s+i,length-i,&bytes);
        if(!(bytes==1 && (cp==' ' || cp<32 || cp>=128)))tail=i+bytes;
    }
    if(tail<lead)tail=lead;
    char *core=strndup(s+lead,tail-lead),*numbered=NULL;const char *value=core;
    if(lead || tail<length)value=translate(core);
    // Native slider/check-box formatting occurs after Windows gettext's label lookup.
    // Reproduce that order at display time, using existing labels and untouched numbers.
    if(!strcmp(value,core)) {
        char *separator=strrchr(core,' ');
        if(separator && separator[1]) {
            char *number=separator+1;if(*number=='+' || *number=='-')number++;
            bool numeric=*number!=0;for(char *p=number;*p;p++)if(!isdigit((unsigned char)*p))numeric=false;
            if(numeric){*separator=0;const char *label=translate(core);if(strcmp(label,core)){
                numbered=malloc(strlen(label)+strlen(separator+1)+2);sprintf(numbered,"%s %s",label,separator+1);value=numbered;
            }*separator=' ';}
        }
    }
    if(!strcmp(core,value)){free(core);free(numbered);return NULL;}
    size_t n=strlen(value);char *out=malloc(lead+n+length-tail+1);
    memcpy(out,s,lead);memcpy(out+lead,value,n);memcpy(out+lead+n,s+tail,length-tail);out[lead+n+length-tail]=0;
    free(core);free(numbered);return out;
}

// Translate complete display labels from the original patch only.
// Mutable game buffers retain their address and are looked up again when changed.
static const char *translate(const char *s) {
    if(!s || !*s)return s;
    uint64_t h=hash_string(s);unsigned slot=h%8192;
    for(Cache *c=cache[slot];c;c=c->next)if(c->hash==h && !strcmp(c->key,s))return c->value?c->value:s;
    size_t len=strlen(s);const char *value=NULL;
    for(size_t i=0;i<TRANSLATION_COUNT;i++)if(translations[i].len==len && !memcmp(s,translations[i].en,len)){value=translations[i].zh;break;}
    if(!value && strpbrk(s,"\n\r\t")) {
        char *flat=malloc(len+1);size_t used=0;
        for(size_t i=0;i<len;i++){char ch=s[i];if(ch=='\n'||ch=='\r'||ch=='\t')ch=' ';if(ch==' ' && used && flat[used-1]==' ')continue;flat[used++]=ch;}
        flat[used]=0;
        for(size_t i=0;i<TRANSLATION_COUNT;i++)if(translations[i].len==used && !memcmp(flat,translations[i].en,used)){value=translations[i].zh;break;}
        free(flat);
    }
    char *formatted=value?NULL:pattern_translate(s);
    if(!value && !formatted)formatted=decorated_translate(s);
    Cache *c=calloc(1,sizeof(*c));c->hash=h;c->key=strdup(s);c->value=value?strdup(value):formatted;c->next=cache[slot];cache[slot]=c;
    if(value && test_save[0] && getenv("DR2C_ZH_TRACE")){fprintf(logfile,"LABEL %s => %s\n",s,value);fflush(logfile);}
    return c->value?c->value:s;
}

// Valid Unicode sequences coexist with the game's single-byte colour/icon codes.
static uint32_t decode(const char *s, size_t available, size_t *bytes) {
    const unsigned char *p=(const unsigned char*)s;*bytes=1;
    if(!available)return 0;
    if(p[0]>=0xC2 && p[0]<=0xDF && available>=2 && (p[1]&0xC0)==0x80){*bytes=2;return ((p[0]&31)<<6)|(p[1]&63);}
    if(p[0]>=0xE0 && p[0]<=0xEF && available>=3 && (p[1]&0xC0)==0x80 && (p[2]&0xC0)==0x80){uint32_t c=((p[0]&15)<<12)|((p[1]&63)<<6)|(p[2]&63);if(c>=0x800 && !(c>=0xD800 && c<=0xDFFF)){*bytes=3;return c;}}
    if(p[0]>=0xF0 && p[0]<=0xF4 && available>=4 && (p[1]&0xC0)==0x80 && (p[2]&0xC0)==0x80 && (p[3]&0xC0)==0x80){uint32_t c=((p[0]&7)<<18)|((p[1]&63)<<12)|((p[2]&63)<<6)|(p[3]&63);if(c>=0x10000 && c<=0x10FFFF){*bytes=4;return c;}}
    return p[0];
}

// Migrate Windows gettext-before-formatting at the native format call itself.
// Argument boundaries come from printf; names, numbers and icon bytes stay intact.
static void append_format_piece(char *buffer,size_t capacity,size_t *count,const char *piece,size_t length) {
    if(capacity && *count<capacity-1) {
        size_t available=capacity-1-*count,requested=length<available?length:available,used=0,n;
        while(used<requested){decode(piece+used,length-used,&n);if(used+n>requested)break;used+=n;}
        memcpy(buffer+*count,piece,used);buffer[*count+used]=0;
    }
    *count+=length;
}
static int catalogue_vsnprintf(char *buffer,size_t capacity,const char *format,va_list args) {
    const CatalogueFormat *entry=NULL;
    for(size_t i=0;i<sizeof(catalogue_formats)/sizeof(catalogue_formats[0]);i++)
        if(!strcmp(format,catalogue_formats[i].source)){entry=&catalogue_formats[i];break;}
    if(!entry)return vsnprintf(buffer,capacity,format,args);
    size_t count=0;unsigned argument=0;va_list ap;va_copy(ap,args);
    if(capacity)buffer[0]=0;
    for(const char *p=entry->target;*p;) {
        if(*p!='%'){const char *start=p;while(*p && *p!='%')p++;append_format_piece(buffer,capacity,&count,start,p-start);continue;}
        const char *start=p++;if(*p=='%'){append_format_piece(buffer,capacity,&count,p++,1);continue;}
        while(*p && strchr("-+ #0123456789.",*p))p++;
        char kind=*p++;char token[64];size_t token_length=p-start;
        assert(token_length<sizeof(token));memcpy(token,start,token_length);token[token_length]=0;argument++;
        char piece[4096];int length;
        if(kind=='s') {
            const char *value=va_arg(ap,const char*);if(!value)value="(null)";
            if(entry->translate_mask&(1U<<argument))value=translate(value);
            // Catalogue %s fields are unqualified; keep the complete source so
            // capacity truncation cannot cut a Chinese character in half.
            if(!strcmp(token,"%s")){append_format_piece(buffer,capacity,&count,value,strlen(value));continue;}
            length=snprintf(piece,sizeof(piece),token,value);
        } else if(kind=='c' || kind=='d' || kind=='i')length=snprintf(piece,sizeof(piece),token,va_arg(ap,int));
        else if(kind=='u')length=snprintf(piece,sizeof(piece),token,va_arg(ap,unsigned));
        else {va_end(ap);return vsnprintf(buffer,capacity,format,args);}
        if(length<0){va_end(ap);return length;}
        assert((size_t)length<sizeof(piece));append_format_piece(buffer,capacity,&count,piece,(size_t)length);
    }
    va_end(ap);return (int)count;
}
static char *main_stextf_hans(const char *format,...) {
    char *buffer=at(A_main_stextf_destbuf);va_list args;va_start(args,format);
    catalogue_vsnprintf(buffer,1024,format,args);va_end(args);buffer[1023]=0;return buffer;
}
static float width(Font *font,uint32_t c) {
    if(c>255)return 8;
    if(!font || c<(uint32_t)font->base || c>=(uint32_t)(font->base+font->count))return 0;
    return sprite_get(font->id)[c-font->base].xywh[6];
}
static float string_width(Font *font,const char *s) {if(!s)return 0;size_t len=strlen(s),n;float result=0;for(size_t i=0;i<len;i+=n)result+=width(font,decode(s+i,len-i,&n));return result;}

static int glyphs_hans(Font *font,const char *s,int length,int alignment,int glow) {
    if(!s || !font || length<=0)return 0;
    if((size_t)length==strlen(s)){const char *translated=translate(s);if(translated!=s){s=translated;length=(int)strlen(s);}}
    size_t full=strlen(s),requested=(size_t)length<full?(size_t)length:full,len=0,n;
    while(len<requested){decode(s+len,full-len,&n);if(len+n>requested)break;len+=n;}
    bool unicode=false;
    for(size_t i=0;i<len;i+=n)if(decode(s+i,len-i,&n)>255)unicode=true;
    if(!unicode || !font_ready)return original_glyphs(font,s,(int)len,alignment,glow);
    unsigned char state[96];memcpy(state,turtle,96);
    Sprite *base=sprite_get(font->id);
    uint32_t first=decode(s,len,&n);double advance=width(font,first)*0.5,total=0;
    for(size_t i=0;i<len;i+=n)total+=width(font,decode(s+i,len-i,&n));
    if(alignment==1)advance-=total*0.5;else if(alignment==2)advance-=total;
    turtle_trans(advance,0);
    size_t count=0;
    for(size_t i=0;i<len;i+=n,count++) {
        uint32_t c=decode(s+i,len-i,&n);float w=width(font,c);
        int code=(int)c-font->base;
        if(c<=255 && *glyph_callback && (*glyph_callback)((int8_t)code,0,*glyph_context)) { if(*glyph_callback)(*glyph_callback)((int8_t)code,1,*glyph_context);continue; }
        if(count)turtle_trans(w*0.5,0);
        if(c>255) {
            if(c>65535)c=0x25A1;
            Sprite sprite=base['M'-font->base];
            sprite.xywh[0]=original_width+(c%256)*12;sprite.xywh[1]=original_height-3072+(c/256)*12;
            sprite.xywh[2]=sprite.xywh[3]=sprite.xywh[6]=sprite.xywh[7]=12;
            sprite.xywh[10]=sprite.xywh[11]=0;
            // Chinese is centred on the same baseline as the original pixel font.
            double sx=turtle[3],sy=turtle[4];turtle[3]*=2.0/3.0;turtle[4]*=2.0/3.0;
            sprite_plot(&sprite,0,glow);turtle[3]=sx;turtle[4]=sy;
        } else {
            if(code<0 || code>=font->count)code=font->count-1;
            sprite_plot(&base[code],0,glow);
        }
        turtle_trans(w*0.5,0);
        if(c<=255 && *glyph_callback)(*glyph_callback)((int8_t)code,1,*glyph_context);
    }
    unsigned char colour[16];memcpy(colour,(char*)turtle+80,16);memcpy(turtle,state,96);memcpy((char*)turtle+80,colour,16);
    return length;
}
static int plot_hans(const char *s,int alignment,int shadow,Font *font){return original_plot(translate(s),alignment,shadow,font);}
static int plot_noshadow_hans(const char *s,int alignment){s=translate(s);return glyphs_hans(default_font,s,(int)strlen(s),alignment,*(int*)at(A_textglow_));}
static int text_width_hans(const char *s){return (int)string_width(default_font,translate(s));}
static float glyph_width_hans(Font *font,const char *s){return string_width(font,translate(s))*(float)turtle[3];}
static float glyph_height_hans(Font *font,unsigned char c){if(font==default_font)return 8;int index=c-font->base;if(index<0 || index>=font->count)return 0;return sprite_get(font->id)[index].xywh[7];}
static int wrapped_hans(const char *s,int a,int b,int width,int spacing,Font *font){return original_wrapped(translate(s),a,b,width,spacing,font);}

static int (*original_main_wrap)(void *,int);
static int main_wrap_hans(void *button,int event) {
    const char **label=(const char**)((char*)button+200);const char *source=*label;
    if(event==7)*label=translate(source);
    int result=original_main_wrap(button,event);
    if(event==7 && *label==translate(source))*label=source;
    return result;
}

static int (*original_main_default)(void *,int);
static int (*original_main_image_wrap)(void *,int);
static int main_image_wrap_hans(void *button,int event) {
    const char **label=(const char**)((char*)button+200);const char *source=*label,*display=source;
    if(event==7){display=translate(source);*label=display;}
    int result=original_main_image_wrap(button,event);
    if(event==7 && *label==display)*label=source;
    return result;
}
static int main_default_hans(void *button,int event) {
    const char **label=(const char**)((char*)button+200);const char *source=*label,*display=source;
    if(event==7){display=translate(source);*label=display;}
    int result=original_main_default(button,event);
    if(event==7 && *label==display)*label=source;
    return result;
}

typedef struct Description {struct Description *next;void *perk;char *text;} Description;
static Description *descriptions;
static char *(*fs_pop_string)(void *);
static void **current_perk;
static void *(*original_textpad_append)(const char*);
static void *textpad_append_hans(const char *s){return original_textpad_append(translate(s));}
static void *append_text_hans(void *context){
    const char *s=fs_pop_string(context);
    return ((void *(*)(const char*))at(A_cyoa_append_text))(translate(s));
}
static void *set_text_hans(void *context){
    const char *s=fs_pop_string(context);
    return ((void *(*)(const char*))at(A_cyoa_set_text))(translate(s));
}
static const char *full_description(void *perk) {
    for(Description *d=descriptions;d;d=d->next)if(d->perk==perk)return d->text;
    return (const char*)perk+40;
}
// The original patch extends perk descriptions beyond the native 256-byte field.
static char *perk_desc_store(void *context) {
    char *s=fs_pop_string(context);void *perk=*current_perk;if(!perk)return s;
    Description *d=descriptions;while(d && d->perk!=perk)d=d->next;
    if(!d){d=calloc(1,sizeof(*d));d->perk=perk;d->next=descriptions;descriptions=d;}
    free(d->text);d->text=strdup(s);
    size_t length=strlen(s);if(length>255)length=255;
    while(length && ((unsigned char)s[length]&0xC0)==0x80)length--;
    memcpy((char*)perk+40,s,length);((char*)perk+40)[length]=0;return s;
}
static void *perk_desc_show(void *perk) {
    *current_perk=perk;
    const char *description=full_description(perk);
    void *(*just_ok)(const char*)=at(A_cyoa_just_ok);
    void *(*yesno)(const char*,const char*,const char*,void*)=at(A_cyoa_yesno);
    void (*choice_text)(const char*)=at(A_cyoa_set_choice_text);
    void (*fade)(int)=at(A_cyoa_set_fade);
    void (*clickspeed)(int)=at(A_cyoa_set_clickspeed);
    void *(*title)(const char*)=at(A_cyoa_set_title);
    if(*(int*)((char*)perk+304)){just_ok(description);choice_text("Nuts");}
    else yesno(description,"Good","Nope",at(A_perkpick));
    fade(1);clickspeed(1);
    if(*(int*)at(A_perks_selected))return title(translate(perk));
    int level=*(int*)((char*)perk+296)+1;if(level>3)level=3;if(level<0)level=0;
    char stars[4]={0xB4,0xB4,0xB4,0};for(int i=0;i<level;i++)stars[i]=0x1C;
    char buffer[512];snprintf(buffer,sizeof(buffer),"%s %s",translate(perk),stars);return title(buffer);
}

// Width-aware UTF-8 wrapping. Original control bytes remain in each returned line.
static const char *wrap_hans(const char **cursor,Font *font,unsigned limit,int keep_space) {
    static char line[16384];
    if(!cursor || !*cursor || !**cursor)return NULL;
    const char *s=*cursor;size_t len=strlen(s),i=0,last_space=SIZE_MAX,cut=0,n=1;float w=0;
    if(!keep_space)while(s[i]==' ' || s[i]=='\t')i++;
    size_t start=i;
    for(;i<len && i-start<sizeof(line)-5;i+=n){uint32_t c=decode(s+i,len-i,&n);if(c=='\n'||c=='\r')break;if(c==' '||c=='\t')last_space=i;float next=width(font,c);if(w+next>limit && i>start)break;w+=next;}
    cut=i;
    if(i<len && s[i]!='\n' && s[i]!='\r' && last_space!=SIZE_MAX && last_space>start && i-last_space<20)cut=last_space;
    if(cut==start && i<len && s[i]!='\n' && s[i]!='\r'){decode(s+i,len-i,&n);cut=i+n;}
    memcpy(line,s+start,cut-start);line[cut-start]=0;
    size_t next=cut;if(s[next]=='\n'||s[next]=='\r'){char c=s[next++];if(c=='\r' && s[next]=='\n')next++;}else if(!keep_space)while(s[next]==' '||s[next]=='\t')next++;
    *cursor=s+next;return line;
}
static const char *save_path_hans(void){return test_save;}

// Expand the game's own texture. Native batching, effects and draw order remain intact.
static int expand_atlas(void *atlas) {
    int *a=(int*)atlas;
    if(!combined_atlas){combined_atlas=atlas;original_width=a[2];original_height=a[3];}
    if(atlas!=combined_atlas)return 1;
    GLint maxsize=0;glGetIntegerv(GL_MAX_TEXTURE_SIZE,&maxsize);int nw=original_width+3072,nh=original_height>3072?original_height:3072;
    if(nw>maxsize || nh>maxsize){fprintf(logfile,"Font atlas exceeds GPU limit\n");fflush(logfile);return -3;}
    size_t oldbytes=(size_t)original_width*original_height*4,newbytes=(size_t)nw*nh*4;
    unsigned char *old=malloc(oldbytes),*pixels=calloc(1,newbytes);
    glBindTexture(GL_TEXTURE_2D,a[4]);glGetTexImage(GL_TEXTURE_2D,0,GL_RGBA,GL_UNSIGNED_BYTE,old);
    for(int y=0;y<original_height;y++)memcpy(pixels+((size_t)y*nw)*4,old+(size_t)y*original_width*4,(size_t)original_width*4);
    char path[PATH_MAX];snprintf(path,sizeof(path),"%s/gfx/fonts/font_ucs2_12x12.png",resources);int fw,fh,fc;unsigned char *font=image_load(path,&fw,&fh,&fc,4);
    if(!font || fw!=3072 || fh!=3072){fprintf(logfile,"Chinese font load failed\n");fflush(logfile);free(old);free(pixels);free(font);return -3;}
    for(int y=0;y<3072;y++)memcpy(pixels+((size_t)(nh-1-y)*nw+original_width)*4,font+(size_t)y*3072*4,3072*4);
    glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA,nw,nh,0,GL_RGBA,GL_UNSIGNED_BYTE,pixels);
    glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MIN_FILTER,GL_NEAREST);glTexParameteri(GL_TEXTURE_2D,GL_TEXTURE_MAG_FILTER,GL_NEAREST);
    font_ready=true;
    fprintf(logfile,"Chinese atlas ready: %dx%d -> %dx%d, GL error %u\n",original_width,original_height,nw,nh,glGetError());fflush(logfile);
    free(old);free(pixels);free(font);return 1;
}
static int upload_hans(void *atlas,int filter,int format){int result=original_upload(atlas,filter,format);if(result<0 || !atlas)return result;return expand_atlas(atlas);}
static void bind_hans(void *atlas){int *a=atlas;int *last=at(0x1000ca1acULL);int w=a[2],h=a[3];if(atlas==combined_atlas && font_ready){w=original_width+3072;h=original_height>3072?original_height:3072;}if(a[4]!=*last || atlas==combined_atlas){glMatrixMode(GL_TEXTURE);glLoadIdentity();glScalef(1.0f/w,1.0f/h,1);glMatrixMode(GL_MODELVIEW);glBindTexture(GL_TEXTURE_2D,a[4]);*last=a[4];}}
static int update_hans(void *atlas){int *a=atlas;void *pixels=*(void**)((char*)atlas+32);if(!pixels)return -1;bind_hans(atlas);glTexImage2D(GL_TEXTURE_2D,0,GL_RGBA,a[2],a[3],0,GL_RGBA,GL_UNSIGNED_BYTE,pixels);return atlas==combined_atlas?expand_atlas(atlas):1;}

static void jump(unsigned char *p,void *target){p[0]=0xFF;p[1]=0x25;memset(p+2,0,4);memcpy(p+6,&target,8);}
static bool hook(uint64_t address,const unsigned char *expected,size_t n,void *replacement,void **original) {
    unsigned char *p=at(address);if(memcmp(p,expected,n)){fprintf(logfile,"Hook bytes mismatch at %llx\n",address);return false;}
    if(original){unsigned char *trampoline=mmap(NULL,4096,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANON,-1,0);if(trampoline==MAP_FAILED)return false;memcpy(trampoline,p,n);jump(trampoline+n,p+n);if(mprotect(trampoline,4096,PROT_READ|PROT_EXEC))return false;*original=trampoline;}
    mach_vm_address_t start=(uintptr_t)p&~((uintptr_t)4095);
    size_t region=(((uintptr_t)p+n-start+4095)/4096)*4096;
    kern_return_t kr=mach_vm_protect(mach_task_self(),start,region,false,VM_PROT_READ|VM_PROT_WRITE|VM_PROT_EXECUTE|VM_PROT_COPY);
    if(kr!=KERN_SUCCESS){fprintf(logfile,"Memory protection failed: %d\n",kr);return false;}
    jump(p,replacement);memset(p+14,0x90,n-14);__builtin___clear_cache((char*)p,(char*)p+n);
    mach_vm_protect(mach_task_self(),start,region,false,VM_PROT_READ|VM_PROT_EXECUTE);return true;
}

static bool supported(const char *path) {
    FILE *f=fopen(path,"rb");if(!f)return false;CC_SHA256_CTX ctx;CC_SHA256_Init(&ctx);unsigned char b[16384],digest[32];size_t n;
    while((n=fread(b,1,sizeof(b),f)))CC_SHA256_Update(&ctx,b,(CC_LONG)n);fclose(f);CC_SHA256_Final(digest,&ctx);char hex[65];for(int i=0;i<32;i++)sprintf(hex+2*i,"%02x",digest[i]);
    return !strcmp(hex,"e384223c506c5e30582416afc156f6d2eca580adfe82ec77a2c87ecad720f65b");
}
#ifndef ADAPTER_SELF_TEST
__attribute__((constructor)) static void initialize(void) {
    char executable[PATH_MAX];uint32_t size=sizeof(executable);if(_NSGetExecutablePath(executable,&size))return;
    char real[PATH_MAX];if(!realpath(executable,real))return;char *last=strrchr(real,'/');if(!last)return;*last=0;last=strrchr(real,'/');if(!last)return;*last=0;snprintf(resources,sizeof(resources),"%s/Resources",real);
    const char *test=getenv("DR2C_ZH_TEST_SAVE_DIR");if(test && test[0]=='/'){snprintf(test_save,sizeof(test_save),"%s%s",test,test[strlen(test)-1]=='/'?"":"/");mkdir(test_save,0700);}
    char logpath[PATH_MAX];snprintf(logpath,sizeof(logpath),"%s/dr2c_hans.log",test_save[0]?test_save:resources);logfile=fopen(logpath,"a");if(!logfile)logfile=stderr;
    if(!supported(executable)){fprintf(logfile,"Unsupported executable. Adapter disabled.\n");fflush(logfile);return;}
    slide=_dyld_get_image_vmaddr_slide(0);turtle=at(A_turtle);default_font=at(A_font6x8);glyph_callback=at(A_glyph_callback_func_);glyph_context=at(A_glyph_callback_context_);
    sprite_get=at(A_sprite_get);sprite_plot=at(A_sprite_batch_plot);turtle_trans=at(A_turtle_trans);image_load=at(0x1000210e7ULL);
    // These trampolines contain only verified prologues without relative instructions.
    bool ok=hook(A_atlas_upload,expected_atlas_upload,sizeof(expected_atlas_upload),upload_hans,(void**)&original_upload);
    ok &= hook(A_draw_bind_texture,expected_draw_bind_texture,sizeof(expected_draw_bind_texture),bind_hans,NULL);
    ok &= hook(A_atlas_update_texture,expected_atlas_update_texture,sizeof(expected_atlas_update_texture),update_hans,NULL);
    ok &= hook(A_glyphs_batch_plot_ex,expected_glyphs_batch_plot_ex,sizeof(expected_glyphs_batch_plot_ex),glyphs_hans,(void**)&original_glyphs);
    ok &= hook(A_plot_text_ex,expected_plot_text_ex,sizeof(expected_plot_text_ex),plot_hans,(void**)&original_plot);
    ok &= hook(A_plot_text_noshadow,expected_plot_text_noshadow,sizeof(expected_plot_text_noshadow),plot_noshadow_hans,NULL);
    ok &= hook(A_text_w,expected_text_w,sizeof(expected_text_w),text_width_hans,NULL);
    ok &= hook(A_glyphs_w,expected_glyphs_w,sizeof(expected_glyphs_w),glyph_width_hans,NULL);
    ok &= hook(A_wrap_text_ex,expected_wrap_text_ex,sizeof(expected_wrap_text_ex),wrap_hans,NULL);
    ok &= hook(A_glyph_h,expected_glyph_h,sizeof(expected_glyph_h),glyph_height_hans,NULL);
    ok &= hook(A_plot_text_wrapped_ex,expected_plot_text_wrapped_ex,sizeof(expected_plot_text_wrapped_ex),wrapped_hans,(void**)&original_wrapped);
    ok &= hook(A_main_btn_default,expected_main_btn_default,sizeof(expected_main_btn_default),main_default_hans,(void**)&original_main_default);
    ok &= hook(A_main_btn_image_wrap,expected_main_btn_image_wrap,sizeof(expected_main_btn_image_wrap),main_image_wrap_hans,(void**)&original_main_image_wrap);
    ok &= hook(A_main_stextf,expected_main_stextf,sizeof(expected_main_stextf),main_stextf_hans,NULL);
    ok &= hook(A_main_btn_wrap,expected_main_btn_wrap,sizeof(expected_main_btn_wrap),main_wrap_hans,(void**)&original_main_wrap);
    fs_pop_string=at(A_fs_pop_string);current_perk=at(A_curperk);
    ok &= hook(A_main_textpad_append,expected_main_textpad_append,sizeof(expected_main_textpad_append),textpad_append_hans,(void**)&original_textpad_append);
    ok &= hook(A_word_cyoa_text_append,expected_word_cyoa_text_append,sizeof(expected_word_cyoa_text_append),append_text_hans,NULL);
    ok &= hook(A_word_cyoa_set_text,expected_word_cyoa_set_text,sizeof(expected_word_cyoa_set_text),set_text_hans,NULL);
    ok &= hook(A_perk_word_strdesc,expected_perk_word_strdesc,sizeof(expected_perk_word_strdesc),perk_desc_store,NULL);
    ok &= hook(A_do_perk_desc,expected_do_perk_desc,sizeof(expected_do_perk_desc),perk_desc_show,NULL);
    if(test_save[0])ok &= hook(A_wrapper_file_save_path,expected_wrapper_file_save_path,sizeof(expected_wrapper_file_save_path),save_path_hans,NULL);
    fprintf(logfile,"Mac Simplified Chinese adapter: hooks=%s, dictionary=%zu, saves=%s\n",ok?"OK":"FAILED",(size_t)TRANSLATION_COUNT,test_save[0]?test_save:"original");fflush(logfile);
    if(!ok)_exit(71);
}
#else
static int test_format(char *buffer,size_t capacity,const char *format,...) {
    va_list args;va_start(args,format);int n=catalogue_vsnprintf(buffer,capacity,format,args);va_end(args);return n;
}
static Sprite test_sprites[256];
static Sprite *test_sprite_get(int id){(void)id;return test_sprites;}
int main(void) {
    Font font={0,0,256};double state[12]={0};default_font=&font;turtle=state;sprite_get=test_sprite_get;
    for(int i=0;i<256;i++){test_sprites[i].xywh[6]=(i>=32 && i<127)?6:0;test_sprites[i].xywh[7]=8;}
    size_t n;assert(decode("中",3,&n)==0x4E2D && n==3);assert(decode("\xF1",1,&n)==0xF1 && n==1);
    assert(decode("😀",4,&n)==0x1F600 && n==4);assert(decode("\xE4\xB8",2,&n)==0xE4 && n==1);
    assert(!strcmp(translate("START"),"开始游戏"));
    assert(!strcmp(translate("Random"),"完全随机"));
    assert(!strcmp(translate("Ranger"),"Ranger"));
    assert(!strcmp(translate("Craftsman"),"Craftsman"));
    assert(!strcmp(translate("Load\nRandom"),"从自定义中随机"));
    assert(!strcmp(translate("Sound 75"),"游戏音效 75"));
    assert(!strcmp(translate(" Sound 75 ")," 游戏音效 75 "));
    assert(!strcmp(translate("Scratch \x1C"),"划痕特效 \x1C"));
    assert(!strcmp(translate("Stash in the Woods"),"林中小屋"));
    assert(!strcmp(translate("Hockey Stick"),"冰球棒"));
    assert(!strcmp(translate("\xF1" "Bandit" "\xF0"),"\xF1" "强盗" "\xF0"));
    assert(strstr(translate("\x12 HAIR 17 \x12"),"头发 17"));
    assert(strstr(translate("\xF1Joeseph's strength revealed \x99 ?\xF0"),"力量"));
    const char *stats[]={"morale","attitude","composure","charm","wits","loyalty","medical","mechanical","shooting","strength","dexterity","fitness","vitality"};
    const char *names[]={"Peggi","Alida","Pat O'Brien","GET","士气"};
    const char *icons="\xE4 \x99 \xE3";
    char source[1024],actual[1024],expected[1024];unsigned dynamic_cases=0;
    for(size_t i=0;i<sizeof(stats)/sizeof(stats[0]);i++)for(size_t j=0;j<sizeof(names)/sizeof(names[0]);j++)for(int direction=0;direction<2;direction++) {
        const char *verb=direction?"increases":"decreases";int colour=direction?0xF2:0xF3;
        snprintf(source,sizeof(source),"%c%s's %s %s %s\xF0",colour,names[j],stats[i],verb,icons);
        snprintf(expected,sizeof(expected),"%c%s的 %s %s %s\xF0",colour,names[j],translate(stats[i]),direction?"属性提升了":"属性降低了",icons);
        assert(!strcmp(translate(source),expected));
        test_format(actual,sizeof(actual),"%c%s's %s %s %s\xF0",colour,names[j],stats[i],verb,icons);
        assert(!strcmp(actual,expected));dynamic_cases++;
    }
    test_format(actual,sizeof(actual),"\xF1%s's %s revealed \x99 %c\xF0","GET","vitality",0xE4);
    assert(!strcmp(actual,"\xF1GET 显示了属性：最大生命 \x99 \xE4\xF0"));
    test_format(actual,sizeof(actual),"%c%s %s \x99 \xF0%c %c%+d\xF0",0xF3,"LOSE","shotgun ammo",0x94,0xF3,-4);
    assert(!strcmp(actual,"\xF3失去霰弹枪子弹 \x99 \xF0\x94 \xF3-4\xF0"));
    test_format(actual,sizeof(actual),"%s: \"%s\"","GET","untranslated future speech");
    assert(!strcmp(actual,"GET: \"untranslated future speech\""));
    test_format(actual,sizeof(actual),"unrecognised %s %.2f %ld","GET",1.25,987654L);
    assert(!strcmp(actual,"unrecognised GET 1.25 987654"));
    test_format(actual,4,"\x12 HAIR %d \x12",15);assert(!strcmp(actual,"\x12 "));
    char mutable_label[64]="Mechanic";
    const char *first=translate(mutable_label);assert(strcmp(first,mutable_label));
    strcpy(mutable_label,"Athlete");const char *second=translate(mutable_label);
    assert(strcmp(first,second));assert(!strcmp(mutable_label,"Athlete"));
    strcpy(mutable_label,"Untranslated future text");assert(translate(mutable_label)==mutable_label);
    assert(!strcmp(translate("Joeseph"),"Joeseph"));assert(string_width(&font,"中A文")==22);
    const char *s="中文测试AB\n下一行";unsigned lines=0;char rebuilt[128]="";
    while(*s){const char *old=s,*line=wrap_hans(&s,&font,16,0);assert(s>old);assert(line);assert(string_width(&font,line)<=16);strcat(rebuilt,line);lines++;}
    assert(lines==5);assert(!strcmp(rebuilt,"中文测试AB下一行"));
    const char *empty="";assert(!wrap_hans(&empty,&font,16,0));
    const char *blank="\n\r\n中";
    assert(!strcmp(wrap_hans(&blank,&font,16,0),""));
    assert(!strcmp(wrap_hans(&blank,&font,16,0),""));
    assert(!strcmp(wrap_hans(&blank,&font,16,0),"中"));
    printf("PASS: %u stat-change cases preserve names/icons and translate full fields; native catalogue formatting, original-patch labels, mutable buffers and UTF-8 wrapping.\n",dynamic_cases);
    return 0;
}
#endif
