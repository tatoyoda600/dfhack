#include <string>
#include <vector>
#include <iostream>
#include <fstream>

#include "Core.h"
#include "Console.h"
#include "DataDefs.h"
#include "Debug.h"
#include "PluginManager.h"
#include <LuaTools.h>
#include "MemAccess.h"

#ifdef WIN32
#define WIN32_LEAN_AND_MEAN
#define _WIN32_WINNT 0x0501
#define WINVER 0x0501
#include <windows.h>
#endif
#include <queue>
#include <deque>
#include <df/large_integer.h>

using std::string;
using std::vector;

using namespace DFHack;
using namespace df::enums;

// Offset a pointer by a number
#define PTR_ADD(ptr, offset) reinterpret_cast<const void *>(uintptr_t(ptr) + (offset))

class DumpItem;
// A list of DF's memory ranges
std::vector<t_memrange> mapped;
// Map of memory addresses to their DumpItems
std::map<const void*, DumpItem*> dumpItems;

DFHACK_PLUGIN("dump");

namespace DFHack {
    DBG_DECLARE(dump, log);
}

static command_result do_command(color_ostream& out, vector<string>& parameters);

DFhackCExport command_result plugin_init(color_ostream& out, std::vector <PluginCommand>& commands) {
    DEBUG(log, out).print("initializing %s\n", plugin_name);
    string name = plugin_name;
    name += "-plugin";
    commands.push_back(PluginCommand(
        name.c_str(),
        "My dump plugin.",
        do_command));

    return CR_OK;
}

template<typename T>
concept Identifiable = requires(T var) {
    { df::identity_traits<T>::get() } -> std::convertible_to<type_identity*>;
};
template<typename T>
concept NonIdentifiable = not Identifiable<T>;

template<Identifiable T>
type_identity* GetIdentity(T& var) {
    return df::identity_traits<T>::get();
}

template<NonIdentifiable T>
type_identity* GetIdentity(T& var) {
    return nullptr;
}

static char* bytesToHex(void* address, size_t size) {
    char* buffer = new char[size * 2 + 1];
    for (int i = 0; i < size; i++) {
        const unsigned char* temp = static_cast<const unsigned char*>(address);
        sprintf(&buffer[i * 2], "%02X", temp[size - 1 - i]);
    }
    return buffer;
}

// Calculate the byte size a structure should have, using identity and count
inline static size_t getIdentityByteSize(const type_identity* identity, size_t count = 0) {
    return identity->byte_size() * (count ? count : 1);
}

static bool isProcessing(const void* ptr, type_identity* identity, size_t count = 0) {
    const void* ptrEnd = PTR_ADD(ptr, getIdentityByteSize(identity, count));

    auto prev = dumpItems.lower_bound(ptr);
    if (prev != dumpItems.cbegin() && uintptr_t(prev->first) > uintptr_t(ptr))
        prev--;

    // If the element isn't the beginning of the map, and the key <= stateRef.ptr,
    //  and stateRef.ptr is before the end of the element's object (contains stateRef.ptr)
    if (prev != dumpItems.cend() && uintptr_t(prev->first) <= uintptr_t(ptr) && uintptr_t(prev->first) + prev->second->getByteSize() > uintptr_t(ptr)) {
        // Get the offset into the element's object where stateRef.ptr is located
        uintptr_t offset = uintptr_t(ptr) - uintptr_t(prev->first);
        // If the element's object does not contain an object of the same type as stateRef at the offset
        if (!IdentityItem(prev->second).HasTypeAtOffset(identity, offset)) {
            // stateRef is a void* and has the same memory address as the element
            if (offset == 0 && identity == df::identity_traits<void*>::get())
                return true;

            // The element and stateRef have conflicting claims
            return true;
        }

        // The element contains stateRef, so fail
        //  Meaning stateRef, or an object containing it has been processed previously
        return true;
    }

    // Gets the 1st element where key >= stateRef.ptr, or end if none exist
    auto overlap_start = dumpItems.lower_bound(ptr);
    // Gets the 1st element where key >= ptr_end, or end if none exist
    auto overlap_end = dumpItems.lower_bound(ptrEnd);
    // Loop through all the elements that lie between the start and end memory addresses
    //  (Skipped if start and end overlap the same element, or none at all)
    for (auto overlap = overlap_start; overlap != overlap_end; overlap++) {
        // Get the offset into stateRef.ptr where the element's object is located
        uintptr_t offset = uintptr_t(overlap->first) - uintptr_t(ptr);
        // If stateRef does not contain an object of the same type as the element's object at the offset
        if (!IdentityItem(identity, count).HasTypeAtOffset(overlap->second->identity, offset))
            return true;
    }

    return false;
}

// Validate that an object of size 'size' can be located at 'ptr' while fitting in valid DF memory
static bool isValidDereference(const void* ptr, size_t size) {
    // Cast the pointer to a non-constant void pointer
    void* base = const_cast<void*>(ptr);
    if (!base)
        return false;

    // Try and find the entirety of the provided object in valid ranges of DF's memory
    //  Looping is for cases where an object covers multiple memory ranges
    bool found = true;
    void* expected_start = base;
    size_t remaining_size = size;
    // So long as parts of the object are found in DF's memory ranges, loop
    while (found) {
        found = false;

        // Loop through DF's memory ranges
        for (auto& range : mapped) {
            // If the start memory address isn't in the memory range, skip it
            if (!range.isInRange(expected_start))
                continue;

            // Found the address in DF's memory
            found = true;

            // If the memory range isn't valid, or doesn't have read permissions, fail
            if (!range.valid || !range.read)
                return false;

            // Get the address of the end of the object
            void* expected_end = const_cast<void*>(PTR_ADD(expected_start, remaining_size - 1));
            // If a size was provided and the end of the object isn't in this memory range
            if (size && !range.isInRange(expected_end)) {
                // Get the address after the end of this memory range
                const void* next_start = PTR_ADD(range.end, 1);
                // Reduce the size of the object to look for by the size already found
                remaining_size -= ptrdiff_t(next_start) - ptrdiff_t(expected_start);
                // Make the next search start from the after this memory range
                expected_start = const_cast<void*>(next_start);
                break;
            }

            // The object was found to be fully in valid and readable parts of DF's memory
            return true;
        }
    }

    // At least some part of the object wasn't found in DF's memory ranges, so fail
    return false;
}


class IdentityItem {
public:
    const type_identity* identity = nullptr;
    size_t count = 0;
    bool valid = false;

    IdentityItem(const type_identity* identity, size_t count = 0) :
        identity(identity),
        count(count),
        valid(true)
    {}

    IdentityItem(DumpItem* item):
        IdentityItem(item->identity, item->count)
    {}

    IdentityItem(const struct_field_info* fieldInfo) {
        // If the struct field is invalid, fail
        if (!fieldInfo || fieldInfo->mode == struct_field_info::END)
            return;

        // INVESTIGATE THIS SECTION!! <----------------------------------------------------------------------------------
        //  (What purpose does identity serve when valid is false?)
        this->identity = fieldInfo->type;
        // Depending on the type of struct field, process its data differently
        switch (fieldInfo->mode)
        {
        case struct_field_info::STATIC_STRING:
            if (!fieldInfo->count || fieldInfo->type)
                return;
            this->identity = df::identity_traits<char>::get();
            this->count = fieldInfo->count;
            this->valid = true;
            break;
        case struct_field_info::POINTER:
            this->identity = wrap_in_pointer(fieldInfo->type);
            this->valid = true;
            break;
        case struct_field_info::STATIC_ARRAY:
            if (!fieldInfo->count || !fieldInfo->type)
                return;
            this->count = fieldInfo->count;
            this->valid = true;
            break;
        case struct_field_info::STL_VECTOR_PTR:
            if (fieldInfo->count)
                return;
            this->identity = wrap_in_stl_ptr_vector(fieldInfo->type);
            this->valid = true;
            break;
        case struct_field_info::PRIMITIVE:
        case struct_field_info::SUBSTRUCT:
        case struct_field_info::CONTAINER:
            if (fieldInfo->count || !fieldInfo->type)
                return;
            this->valid = true;
            break;
        case struct_field_info::OBJ_METHOD:
        case struct_field_info::CLASS_METHOD:
            return;
        }
    }

    size_t getByteSize() const {
        return getIdentityByteSize(this->identity, this->count);
    }

    // Check if this object contains a specified type at a specified offset
    bool HasTypeAtOffset(const type_identity* typeIdentity, size_t offset) const {
        // If the type is invalid, fail
        if (!this->identity)
            return false;

        // If the type matches this object's type, success
        if (offset == 0 && this->identity == typeIdentity)
            return true;

        // If the offset is bigger than the size of this object's type,
        //  yet smaller than this object's size (object list), then set
        //  the offset to be relative to that item.
        //  Fail if completely outside of this object
        if (offset >= this->identity->byte_size())
            if (offset < this->getByteSize())
                offset %= this->identity->byte_size();
            else
                return false;

        // If this object's type is a buffer
        //  (What's a buffer??)
        if (this->identity->type() == IDTYPE_BUFFER) {
            // Get the type_identity of the buffer's content
            const type_identity* target = static_cast<const container_identity*>(this->identity)->getItemType();
            // Check the buffer's content for the type, adjusting the offset to be relative to a buffer item
            return IdentityItem(target).HasTypeAtOffset(typeIdentity, offset % target->byte_size());
        }

        // Cast this object's type to a struct type
        const struct_identity* st = dynamic_cast<const struct_identity*>(this->identity);
        // If it's not a struct type, fail
        if (!st)
            return false;

        // Loop through parent types of the struct type
        for (auto p = st; p; p = p->getParent()) {
            // Get the type's fields
            const struct_field_info* fields = p->getFields();
            // If no fields were found, skip it
            if (!fields)
                continue;

            // Loop through the type's fields
            for (const struct_field_info* field = fields; field->mode != struct_field_info::END; field++) {
                // If the field is a method, or the field's offset is greater than the specified offset, skip it
                if (field->mode == struct_field_info::OBJ_METHOD || field->mode == struct_field_info::CLASS_METHOD || field->offset > offset)
                    continue;

                // Check the field for the type, adjusting the offset to be relative to it, and if so, success
                if (IdentityItem(field).HasTypeAtOffset(typeIdentity, offset - field->offset))
                    return true;
            }
        }

        // The type wasn't equal to, or contained inside, this object's type, so fail
        return false;
    }
};

class DumpItem {
public:
    const void* ptr = nullptr;
    const type_identity* identity = nullptr;
    const size_t count = 0;
    const std::vector<std::tuple<std::string, DumpItem*>> children;

    // Create
    DumpItem(int depth, const void* ptr, type_identity* identity, size_t count = 0):
        ptr(ptr),
        count(count)
    {
        if (!ptr || !identity || depth < 0)
            return;

        type_identity* tempIdentity = nullptr;

        // If the item is a class
        if (identity->type() == IDTYPE_CLASS) {
            // If the class is also a list, fail
            if (count)
                return;

            // If the item's vtable name can be obtained
            if (get_vtable_name(ptr)) {
                // Get the virtual_identity from the pointer, and use that identity instead
                virtual_identity* actual_identity = virtual_identity::get(reinterpret_cast<virtual_ptr>(const_cast<void*>(ptr)));
                if (static_cast<const virtual_identity*>(identity)->is_subclass(actual_identity))
                    tempIdentity = actual_identity;
            }
        }

        tempIdentity = tempIdentity ? tempIdentity : identity;

        // If this item is already contained within a previous DumpItem
        if (isProcessing(ptr, tempIdentity))
            return;

        // INVESTIGATE THIS SECTION!! <----------------------------------------------------------------------------------
        //  (When/Why are elements erased from the list? Should anything be done before they're erased?)
        // Get the address of the end of the item
        const void* ptrEnd = PTR_ADD(ptr, this->getByteSize());
        // Gets the 1st element where key >= ptr, or end if none exist
        auto overlapStart = dumpItems.lower_bound(ptr);
        // Gets the 1st element where key >= ptrEnd, or end if none exist
        auto overlapEnd = dumpItems.lower_bound(ptrEnd);
        // Erases all elements in range [overlapStart, overlapEnd)
        //  (Why is this so sure that overlapStart isn't a separate object that shouldn't be erased??)
        dumpItems.erase(overlapStart, overlapEnd);

        // Adds this item to the item map
        dumpItems[this->ptr] = this;

        // If the item isn't valid, fail
        if (!isValidDereference(this->ptr, this->getByteSize()))
            return;

        this->identity = tempIdentity;
        this->dispatch();
    }

    // Encode
    // Parse
    // Restore

    size_t getByteSize() const {
        return getIdentityByteSize(identity, count);
    }

private:
    void dispatch() {
        // INVESTIGATE THIS SECTION!! <----------------------------------------------------------------------------------
        //  (The following dispatch section needs to somehow give back the list of children)

        // Get the starting pointer and item size
        const void* curPtr = ptr;
        size_t size = identity->byte_size();
        // Loop through each element of the list, or just once if not a list
        for (size_t i = 0; i < (count ? count : 1); i++) {
            // Based on the type of data, process the item differently
            switch (identity->type())
            {
            case IDTYPE_GLOBAL:
            case IDTYPE_FUNCTION:
            case IDTYPE_PTR_CONTAINER: // (Why skip this??)
            case IDTYPE_OPAQUE: // (What is this??)
                break;
            case IDTYPE_PRIMITIVE:
                dispatch_primitive(curPtr, identity);
                break;
            case IDTYPE_POINTER:
                dispatch_pointer(curPtr, identity, count);
                break;
            case IDTYPE_CONTAINER:
                dispatch_container(curPtr, identity);
                break;
            case IDTYPE_BIT_CONTAINER:
                dispatch_bit_container(curPtr, identity);
                break;
            case IDTYPE_BITFIELD:
                dispatch_bitfield(curPtr, identity);
                break;
            case IDTYPE_ENUM:
                dispatch_enum(curPtr, identity);
                break;
            case IDTYPE_STRUCT:
                dispatch_struct(curPtr, identity);
                break;
            case IDTYPE_CLASS:
                dispatch_class(curPtr, identity);
                break;
            case IDTYPE_BUFFER:
                dispatch_buffer(curPtr, identity);
                break;
            case IDTYPE_STL_PTR_VECTOR:
                dispatch_stl_ptr_vector(curPtr, identity);
                break;
            case IDTYPE_UNION:
                dispatch_untagged_union(curPtr, identity);
                break;
            }

            // Advance to the next element in the list
            curPtr = PTR_ADD(curPtr, size);
        }
    }
};


// Data format plan:
//  - Parsing function:
//      1. Split the string on the first and last curly brackets
//      2. Split on "content: "
//      3. Split the first half on comma
//      4. Process the first half's splits (type)
//      5. If the second half (content) has square brackets
//          N:
//              1. Pass to the casting function, along with the type
//          Y:
//              1. Get tabs until first non tab character
//              2. Remove first tabs
//              3. Split on ",\n"+TAB_COUNT
//              4. For each item:
//                  1. Split on the first ": "
//                  2. Process the first half (field name)
//                  3. Pass the second half (field value) to the parsing function
//  - Proposed format:
/*
Any header data up here before the 1st curly bracket
{
    type: "",
    content: [
        field1: {
            type: "",
            content: ""
        },
        field2: {
            type: "",
            content: [
                field1: {
                    type: "",
                    content: ""
                },
            ]
        },
    ]
}
*/
//  - Potential format expansion:
/*
Any header data up here before the 1st curly bracket
{
    dump: DUMP_FORMAT_HERE,
    pointers: [
        {
            type: "",
            content: ""
        },
        {
            type: "",
            content: [
                field1: {
                    type: "",
                    content: ""
                },
            ]
        },
    ]
}
*/








void main(color_ostream& out, std::string path, int depth = 10, bool compare = false) {
    StackUnwinder unwinder(State);

    // Use Lua to convert the path to an object
    PushModulePublic(out, "utils", "df_expr_to_ref");
    Push(path);

    if (!SafeCall(out, 1, 1)) {
        out.printerr("unable to get expression reference");
        return;
    }
    if (!lua_touserdata(State, -1)) {
        out.printerr("non-userdata state");
        return;
    }

    // Get the object's reference and identity
    const void* statePtr = get_object_ref(State, -1);
    lua_getfield(State, -1, "_type");
    lua_getfield(State, -1, "_identity");
    type_identity* stateIdentity = reinterpret_cast<type_identity*>(lua_touserdata(State, -1));

    if (!statePtr || !stateIdentity) {
        out.printerr("invalid reference from expression");
        return;
    }

    // Store DF's memory ranges in mapped
    DFHack::Core::getInstance().p->getMemRanges(mapped);

    DumpItem stateItem = DumpItem(depth, statePtr, stateIdentity);
}














struct GlobalConsole {
    color_ostream& out;
    GlobalConsole(color_ostream& o): out(o) {}
};
GlobalConsole* global_console;



using namespace DFHack::Lua;
using namespace DFHack::Lua::Core;
using namespace DFHack::LuaWrapper;

// Handle failures
#define FAIL_MSG(message) {global_console->out << message << std::endl; maxerrors--;} /* __debugbreak(); */
#define FAIL_RET(message) {FAIL_MSG(message); return;}
#define FAIL_RETV(message, value) {FAIL_MSG(message); return value;}
#define FAIL_BRK(message) {FAIL_MSG(message); break;}
#define FAIL_CON(message) {FAIL_MSG(message); continue;}
// Assumes MALLOC_PERTURB_=45
//  (Why does it assume that?)
#ifdef DFHACK64
#define UNINIT_PTR 0xd2d2d2d2d2d2d2d2
#else
#define UNINIT_PTR 0xd2d2d2d2
#endif
#ifdef _WIN64
#define PRIxPTR  "llx"
#else
#define PRIxPTR  "x"
#endif

struct IdentityRef {
    const void* ptr = nullptr;
    const type_identity* identity = nullptr;
    size_t count = 0;
    const enum_identity* enumIdentity = nullptr;
    bool inStructure = false;
    bool isArray = false;

    IdentityRef() {}

    IdentityRef(const type_identity* identity, const void* ptr, size_t count = 0) :
        identity(identity),
        ptr(ptr),
        count(count)
    {}

    IdentityRef(const struct_field_info* field, const void* ptr);

    IdentityRef(lua_State* state);

    // Calculates the byte size of this object
    size_t getByteSize() const;

    // Check if this object contains a specified type at a specified offset
    bool HasTypeAtOffset(const type_identity* typeIdentity, size_t offset) const;
};

// Map of memory addresses to their path and identity reference
std::map<const void*, IdentityRef> data;
// Queue of structures to process
std::deque<IdentityRef> queue;
// The value that malloc uses for newly allocated memory
uint8_t perturb_byte;
// Max amount of errors before stopping
size_t maxerrors = 100000;

static const type_identity* wrap_in_pointer(const type_identity* base);
static const type_identity* wrap_in_stl_ptr_vector(const type_identity* base);
static void dispatch_item(const IdentityRef& item);

IdentityRef::IdentityRef(const struct_field_info* field, const void* ptr) {
    // If the struct field is invalid, fail
    if (!field || field->mode == struct_field_info::END)
        FAIL_RET("invalid struct field")

    // Get the data to fill out this struct's members
    this->ptr = ptr;
    this->identity = field->type;
    this->enumIdentity = field->extra ? field->extra->index_enum : nullptr;
    this->inStructure = true;
    // Depending on the type of struct field, process its data differently
    switch (field->mode)
    {
    case struct_field_info::STATIC_STRING:
        if (!field->count || field->type)
            FAIL_MSG("invalid struct field")
        identity = df::identity_traits<char>::get();
        count = field->count;
        break;
    case struct_field_info::POINTER:
        if (field->count & PTRFLAG_IS_ARRAY)
            this->isArray = true;
        identity = wrap_in_pointer(field->type);
        break;
    case struct_field_info::STATIC_ARRAY:
        if (!field->count || !field->type)
            FAIL_MSG("invalid struct field")
        count = field->count;
        break;
    case struct_field_info::STL_VECTOR_PTR:
        if (field->count)
            FAIL_MSG("invalid struct field")
        identity = wrap_in_stl_ptr_vector(field->type);
        break;
    case struct_field_info::PRIMITIVE:
    case struct_field_info::SUBSTRUCT:
    case struct_field_info::CONTAINER:
        if (field->count || !field->type)
            FAIL_MSG("invalid struct field")
        break;
    case struct_field_info::END:
    case struct_field_info::OBJ_METHOD:
    case struct_field_info::CLASS_METHOD:
        FAIL_MSG("invalid struct field")
        break;
    }
}

IdentityRef::IdentityRef(lua_State* state) {
    // If the Lua state isn't a pointer, return
    if (!lua_touserdata(state, -1))
        FAIL_RET("non-userdata state")

        // Get the pointer from the Lua state object
        this->ptr = get_object_ref(state, -1);
    // Get the Lua state object's "obj._type._identity"
    lua_getfield(state, -1, "_type");
    lua_getfield(state, -1, "_identity");
    // Get the pointer and cast it to a type_identity pointer
    this->identity = reinterpret_cast<type_identity*>(lua_touserdata(state, -1));
}

// Calculates the byte size of this object
size_t IdentityRef::getByteSize() const {
    return getIdentityByteSize(this->identity, this->count);
}

// Check if this object contains a specified type at a specified offset
bool IdentityRef::HasTypeAtOffset(const type_identity* typeIdentity, size_t offset) const
{
    // If the type is invalid, fail
    if (!this->identity)
        return false;

    // If the type matches this object's type, success
    if (offset == 0 && this->identity == typeIdentity)
        return true;

    // If the offset is bigger than the size of this object's type,
    //  yet smaller than this object's size (object list), then set
    //  the offset to be relative to that item.
    //  Fail if completely outside of this object
    if (offset >= this->identity->byte_size())
        if (offset < this->getByteSize())
            offset %= this->identity->byte_size();
        else
            return false;

    // If this object's type is a buffer (What's a buffer??)
    if (this->identity->type() == IDTYPE_BUFFER)
    {
        // Get the type_identity of the buffer's content
        const type_identity* target = static_cast<const container_identity*>(this->identity)->getItemType();
        // Check the buffer's content for the type, adjusting the offset to be relative to a buffer item
        return IdentityRef(target, nullptr).HasTypeAtOffset(typeIdentity, offset % target->byte_size());
    }

    // Cast this object's type to a struct type
    const struct_identity* st = dynamic_cast<const struct_identity*>(this->identity);
    // If it's not a struct type, fail
    if (!st)
        return false;

    // Loop through parent types of the struct type
    for (auto p = st; p; p = p->getParent())
    {
        // Get the type's fields
        const struct_field_info* fields = p->getFields();
        // If no fields were found, skip it
        if (!fields)
            continue;

        // Loop through the type's fields
        for (const struct_field_info* field = fields; field->mode != struct_field_info::END; field++)
        {
            // If the field is a method, or the field's offset is greater than the specified offset, skip it
            if (field->mode == struct_field_info::OBJ_METHOD || field->mode == struct_field_info::CLASS_METHOD || field->offset > offset)
                continue;

            // Check the field for the type, adjusting the offset to be relative to it, and if so, success
            if (IdentityRef(field, nullptr).HasTypeAtOffset(typeIdentity, offset - field->offset))
                return true;
        }
    }

    // The type wasn't equal to, or contained inside, this object's type, so fail
    return false;
}

// If T is a pointer, then std::is_pointer<T>::value will return true,
//  but since 2nd definition is more specific, due to explicitly stating
//  <T,true>, that one will be chosen
// Essentially making this safe_t only be used when T isn't a pointer
template<typename T, bool is_pointer = std::is_pointer<T>::value>
struct safe_t
{
    // Maybe?? typedef std::conditional<is_pointer, void*, T> type;
    typedef T type;
};
// As explained above, this version of safe_t will only be used if T is a pointer
template<typename T>
struct safe_t<T, true>
{
    typedef void* type;
};

/*
// Potentially, both definitions of safe_t could be replaced with this one
template<typename T, bool is_pointer = std::is_pointer<T>::value>
struct safe_t
{
    typedef std::conditional<is_pointer, void*, T> type;
};
*/

// Gets the value that malloc uses for newly allocated memory
static uint8_t check_malloc_perturb()
{
    // MALLOC_PERTURB_ is an environment value used to detect uses of malloc that don't initialize the memory
    /*
    https://udrepper.livejournal.com/11429.html
    The byte value used to initialize values returned by malloc is the byte value of the environment value.
    The value used to clear memory is the bitwise inverse.
    Setting MALLOC_PERTURB_ to zero disables the feature.
    */

    // Creates a large array of bytes
    const size_t TEST_DATA_LEN = 5000;  // >1 4kb page
    std::unique_ptr<uint8_t[]> test_data{ new uint8_t[TEST_DATA_LEN] };

    // Gets the value the 1st element was created with
    uint8_t expected_perturb = test_data[0];
    // If the MALLOC_PERTURB_ environment value can be gotten, get the bitwise inverse of its value
    if (getenv("MALLOC_PERTURB_"))
        expected_perturb = 0xff ^ static_cast<uint8_t>(atoi(getenv("MALLOC_PERTURB_")));

    // For every element in the array, if it was created with a different starting value than expected, return 0
    for (size_t i = 0; i < TEST_DATA_LEN; i++)
        if (expected_perturb != test_data[i])
            return 0;

    // Return the value that malloc uses for newly allocated memory
    return expected_perturb;
}

// Validate that an object of size 'size' can be located at 'ptr' while fitting in valid DF memory
static bool is_valid_dereference(const void* ptr, size_t size)
{
    // Cast the pointer to a non-constant void pointer
    void* base = const_cast<void*>(ptr);
    if (!base)
        return false;

    // assumes MALLOC_PERTURB_=45
#ifdef DFHACK64
#define FAIL_PTR stl_sprintf("0x%016zx: ", reinterpret_cast<uintptr_t>(base))
#else
#define FAIL_PTR stl_sprintf("0x%08zx: ", reinterpret_cast<uintptr_t>(base))
#endif
    //global_console->out << "Pointer " << FAIL_PTR << std::endl;

    // Make sure the pointer isn't uninitialized
    if (uintptr_t(base) == UNINIT_PTR)
        FAIL_RETV(FAIL_PTR << "uninitialized pointer", false)

    // Try and find the entirety of the provided object in valid ranges of DF's memory
    //  Looping is for cases where an object covers multiple memory ranges
    bool found = true;
    void* expected_start = base;
    size_t remaining_size = size;
    // So long as parts of the object are found in DF's memory ranges, loop
    while (found)
    {
        found = false;

        // Loop through DF's memory ranges
        for (auto& range : mapped)
        {
            // If the start memory address isn't in the memory range, skip it
            if (!range.isInRange(expected_start))
                continue;

            // Found the address in DF's memory
            found = true;

            // If the memory range isn't valid, or doesn't have read permissions, fail
            if (!range.valid || !range.read)
                FAIL_RETV(FAIL_PTR << "pointer to invalid memory range", false)

            // Get the address of the end of the object
            void* expected_end = const_cast<void*>(PTR_ADD(expected_start, remaining_size - 1));
            // If a size was provided and the end of the object isn't in this memory range
            if (size && !range.isInRange(expected_end))
            {
                // Get the address after the end of this memory range
                const void* next_start = PTR_ADD(range.end, 1);
                // Reduce the size of the object to look for by the size already found
                remaining_size -= ptrdiff_t(next_start) - ptrdiff_t(expected_start);
                // Make the next search start from the after this memory range
                expected_start = const_cast<void*>(next_start);
                break;
            }

            //global_console->out << "Fully in memory" << std::endl;
            // The object was found to be fully in valid and readable parts of DF's memory
            return true;
        }
    }

    if (expected_start == base)
        FAIL_MSG(FAIL_PTR << "pointer not in any mapped range")
    else
        FAIL_MSG(FAIL_PTR << "pointer exceeds mapped memory bounds (size " << size << ")")

    // At least some part of the object wasn't found in DF's memory ranges, so fail
    return false;
#undef FAIL_PTR
}

// Validate that an object of type T could be located at 'ptr' and if so, attempt to get said object
template<typename T>
static const T validate_and_dereference(const void* ptr)
{
    // Get the type_identity for T (Using void* if it's a pointer)
    const type_identity* identity = df::identity_traits<typename safe_t<T>::type>::get();
    // If the identified object can't be valid if located at ptr
    if (!is_valid_dereference(ptr, identity->byte_size()))
        return T(); // Create a new instance of T

    // Get the object instance ptr represents
    return *reinterpret_cast<const T*>(ptr);
}

// Get the type name of the object located at 'ptr'
static const char* get_vtable_name(const void* ptr)
{
    // Attempt to get a constant pointer to a constant void* at ptr
    //  (Which is the vtable for some reason???)
    auto vtable = validate_and_dereference<const void* const*>(ptr);
    if (!vtable)
        return nullptr;

    // Attempt to get a constant pointer to a constant char* right before vtable
    //  (Which is something that has data about the type for some reason???)
    auto info = validate_and_dereference<const char* const*>(vtable - 1);
    if (!info)
        return nullptr;

    // Get the name of the vtable using different approaches based on the build environment
#ifdef WIN32
#ifdef DFHACK64
    void* base;
    if (!RtlPcToFileHeader(const_cast<void*>(reinterpret_cast<const void*>(info)), &base))
        return nullptr;

    const char* typeinfo = reinterpret_cast<const char*>(base) + reinterpret_cast<const int32_t*>(info)[3];
    const char* name = typeinfo + 16;
#else
    const char* name = reinterpret_cast<const char*>(info) + 8;
#endif
#else
    auto name = validate_and_dereference<const char*>(info + 1);
#endif

    // Loop through DF's memory ranges
    for (auto& range : mapped)
    {
        // If the vtable name's memory address isn't in the memory range, skip it
        if (!range.isInRange(const_cast<char*>(name)))
            continue;

        // If the memory range isn't valid, or doesn't have read permissions, fail
        if (!range.valid || !range.read)
            return nullptr;

        // Skip forward to the 1st letter's memory address
        const char* first_letter = nullptr;
        bool letter = false;
        for (const char* p = name; ; p++)
        {
            // If the memory range has been exceeded, fail
            if (!range.isInRange(const_cast<char*>(p)))
                return nullptr;

            // If the character is a letter, or underscore
            if ((*p >= 'a' && *p <= 'z') || *p == '_')
            {
                // If no letter has been found, set it as the first letter
                if (!letter)
                    first_letter = p;
                letter = true;
            }
            // If the address contains a nullptr (null terminated) instead of a letter, return the 1st letter memory address
            else if (!*p)
                return first_letter;
        }
    }

    // Either the vtable's name wasn't in DF's memory ranges, or the name wasn't null terminated, so fail
    return nullptr;
}

// Add an object to the processing queue
static bool queue_item(IdentityRef& stateRef) {
    // If the object isn't valid, fail
    if (!stateRef.identity)
        FAIL_RETV("invalid identity", false)

    // If the object is a class
    if (stateRef.identity->type() == IDTYPE_CLASS) {
        // If the class is also a list, fail
        if (stateRef.count)
            FAIL_RETV("invalid class", false)
        //global_console->out << "QUEUE " << stl_sprintf("0x%08zx: ", reinterpret_cast<uintptr_t>(stateRef.ptr)) << std::endl;
        // If the object's vtable name can be obtained
        if (get_vtable_name(stateRef.ptr)) {
            // Get the virtual_identity of the object
            virtual_identity* actual_identity = virtual_identity::get(reinterpret_cast<virtual_ptr>(const_cast<void*>(stateRef.ptr)));
            // If the object's identity is a subclass of the virtual_identity
            if (static_cast<const virtual_identity*>(stateRef.identity)->is_subclass(actual_identity))
                stateRef.identity = actual_identity; // Replace it with the virtual_identity
        }
    }

    // Get the address of the end of the object
    auto ptr_end = PTR_ADD(stateRef.ptr, stateRef.getByteSize());

    // Gets the 1st data element where key >= stateRef.ptr, or end if none exist
    //  This means the 1st queued object whose pointer lies after stateRef's
    auto prev = data.lower_bound(stateRef.ptr);
    // If the element found isn't the beginning of the map (non-empty map)
    //  and the key > stateRef.ptr, get the previous element (key <= stateRef.ptr)
    if (prev != data.cbegin() && uintptr_t(prev->first) > uintptr_t(stateRef.ptr))
        prev--;
    /*
    if (prev != data.cend())
        global_console->out << stl_sprintf("0x%08zx: ", reinterpret_cast<uintptr_t>(prev->first)) << " -- "
            << uintptr_t(prev->first) << " <= " << uintptr_t(stateRef.ptr) << " && " << uintptr_t(prev->first) << " + " << prev->second.getByteSize() << " > " << uintptr_t(stateRef.ptr)
            << std::endl;
    */
    // If the element isn't the beginning of the map, and the key <= stateRef.ptr,
    //  and stateRef.ptr is before the end of the element's object (contains stateRef.ptr)
    if (prev != data.cend() && uintptr_t(prev->first) <= uintptr_t(stateRef.ptr) && uintptr_t(prev->first) + prev->second.getByteSize() > uintptr_t(stateRef.ptr))
    {
        // Get the offset into the element's object where stateRef.ptr is located
        ULONG64 offset = uintptr_t(stateRef.ptr) - uintptr_t(prev->first);
        // If the element's object does not contain an object of the same type as stateRef at the offset
        if (!prev->second.HasTypeAtOffset(stateRef.identity, offset))
        {
            // stateRef is a void* and has the same memory address as the element
            if (offset == 0 && stateRef.identity == df::identity_traits<void*>::get())
                FAIL_RETV("unknown pointer is " << prev->second.identity->getFullName() << ", previously seen at ???", false)

                // The element and stateRef have conflicting claims
                FAIL_RETV("TODO: handle merging structures: ??? overlaps " << prev->second.identity->getFullName() << " (backward)", false)
        }

        // The element contains stateRef, so fail
        //  Meaning stateRef, or an object containing it has been processed previously 
        FAIL_RETV("address previously processed", false)
    }

    // Gets the 1st element where key >= stateRef.ptr, or end if none exist
    auto overlap_start = data.lower_bound(stateRef.ptr);
    // Gets the 1st element where key >= ptr_end, or end if none exist
    auto overlap_end = data.lower_bound(ptr_end);
    // Loop through all the elements that lie between the start and end memory addresses
    //  (Skipped if start and end overlap the same element, or none at all)
    for (auto overlap = overlap_start; overlap != overlap_end; overlap++)
    {
        // Get the offset into stateRef.ptr where the element's object is located
        auto offset = uintptr_t(overlap->first) - uintptr_t(stateRef.ptr);
        // If stateRef does not contain an object of the same type as the element's object at the offset
        if (!stateRef.HasTypeAtOffset(overlap->second.identity, offset))
            FAIL_RETV("TODO: handle merging structures: " << overlap->second.identity->getFullName() << " overlaps ??? (forward)", false)
    }

    // Erases all elements in range [overlap_start, overlap_end)
    //  (Why is this so sure that overlap_start isn't a separate object that shouldn't be erased??)
    data.erase(overlap_start, overlap_end);

    // Add stateRef to the data map
    data[stateRef.ptr] = stateRef;
    // Add stateRef to the processing queue
    queue.push_back(stateRef);
    return true;
}

// Gets a pointer-wrapped version of the type_identity
static const type_identity* wrap_in_pointer(const type_identity* base)
{
    // A static map which links a type_identity to the corresponding pointer-wrapped type_identity
    //  It'll start empty and grow as this function is run, allowing consistent unique references
    static std::map<const type_identity*, std::unique_ptr<const df::pointer_identity>> wrappers;
    // Try and find the type_identity in the map
    auto it = wrappers.find(base);
    // If it's in the map, return the linked pointer-wrapped type_identity
    if (it != wrappers.end())
        return it->second.get();
    // Create a corresponding pointer-wrapped version of the type_identity
    //  and add it to the map, linked to the type_identity
    return (wrappers[base] = std::make_unique<df::pointer_identity>(base)).get();
}

// Gets a stl_ptr_vector-wrapped version of the type_identity
static const type_identity* wrap_in_stl_ptr_vector(const type_identity* base)
{
    // A static map which links a type_identity to the corresponding stl_ptr_vector-wrapped type_identity
    //  It'll start empty and grow as this function is run, allowing consistent unique references
    static std::map<const type_identity*, std::unique_ptr<const df::stl_ptr_vector_identity>> wrappers;
    // Try and find the type_identity in the map
    auto it = wrappers.find(base);
    // If it's in the map, return the linked stl_ptr_vector-wrapped type_identity
    if (it != wrappers.end())
        return it->second.get();
    // Create a corresponding stl_ptr_vector-wrapped version of the type_identity
    //  and add it to the map, linked to the type_identity
    return (wrappers[base] = std::make_unique<df::stl_ptr_vector_identity>(base, nullptr)).get();
}

#ifndef WIN32
// Attempts to get a valid string* from the specified pointer pointer
//  (Does a lot of strange memory address manipulation for some reason??)
static const std::string* validate_stl_string_pointer(const void* const* base)
{
    // If dereferencing base is equal to dereferencing an empty string, then
    //  base is a pointer to an empty string, so return it as such
    std::string empty_string;
    if (*base == *reinterpret_cast<void**>(&empty_string))
        return reinterpret_cast<const std::string*>(base);

    struct string_data_inner
    {
        size_t length;
        size_t capacity;
        int32_t refcount;
    };
    // Starting from 1 byte before the start of the string referenced by base, cast to string_data_inner
    //  (Why would you need to check the previous byte??)
    const string_data_inner* str_data = static_cast<const string_data_inner*>(*base) - 1;

    // If the previous 16 bytes aren't valid memory, fail
    if (!is_valid_dereference(PTR_ADD(str_data, -16), 16))
        return nullptr;

    // If before the start of the string referenced by base, there's a pointer to a specific binary sequence
    //  (How can you know that this info is located there??)
    uint32_t tag = *reinterpret_cast<const uint32_t*>(PTR_ADD(str_data, -8));
    if (tag == 0xdfdf4ac8)
    {
        // Get the allocated size from a pointer before the start of the string referenced by base
        //  (How can you know that this info is located there??)
        size_t allocated_size = *reinterpret_cast<const size_t*>(PTR_ADD(str_data, -16));
        // Get the expected size by combining the length of the string and the size of the string metadata
        size_t expected_size = sizeof(*str_data) + str_data->capacity + 1;

        // If the allocated size and expected size don't match, fail
        if (allocated_size != expected_size)
            return nullptr;
    }
    // If the specific binary sequence is not there, fail
    else
        return nullptr;

    // If the string's capacity is less than its length, fail
    if (str_data->capacity < str_data->length)
        return nullptr;

    // Dereference base into the start of a char array
    const char* ptr = reinterpret_cast<const char*>(*base);
    // For every char in the string, if it's a null terminator, fail
    for (size_t i = 0; i < str_data->length; i++)
        if (!*ptr++)
            return nullptr;

    // If the char after the end of the string isn't a null terminator, fail
    if (*ptr++)
        return nullptr;

    // base is a valid pointer to a non-empty string, so return it as such
    return reinterpret_cast<const std::string*>(base);
}
#endif

#pragma region Dispatchers

// Processes a string
static void check_stl_string(const void* ptr)
{
#ifdef WIN32
    // Represents the internal byte structure of std::string
    struct string_data
    {
        // 16 bytes are used to store either
        union
        {
            // Pointer to an externally allocated char array
            uintptr_t start;
            // A <16 char array directly in the structure (small string optimization)
            char local_data[16];
        };
        // Number of characters in the string
        size_t length;
        // Size of the allocated char array
        size_t capacity;
    };
    // Convert the string to string_data
    const string_data* string = reinterpret_cast<const string_data*>(ptr);
    // Establish that the GCC compiler wasn't used
    const bool is_gcc = false;
    // Whether the char array is contained inside the structure, or externally
    const bool is_local = string->capacity < 16;
#else
    struct string_data
    {
        // Pointer to the start of the char array
        uintptr_t start;
        // Number of characters in the string
        size_t length;
        // 16 bytes are used to store either
        union
        {
            // A <16 char array directly in the structure (small string optimization)
            char local_data[16];
            // The size of the externally allocated char array
            size_t capacity;
        };
    };
    // Convert the string to string_data
    const string_data* string = reinterpret_cast<const string_data*>(ptr);
    // Establish that the GCC compiler wasn used
    const bool is_gcc = true;
    // Whether the char array is contained inside the structure, or externally
    const bool is_local = string->start == reinterpret_cast<uintptr_t>(&string->local_data[0]);
#endif

    // Get the pointer to the start of the char array
    const char* start = is_local ? &string->local_data[0] : reinterpret_cast<const char*>(string->start);
    // Get the length of the string
    ptrdiff_t length = string->length;
    // Get the capacity of the string
    //  This value will be wrong if (is_gcc && is_local), due to the union
    ptrdiff_t capacity = string->capacity;

    // If length is less than 0, fail
    if (length < 0)
        FAIL_MSG("string length is negative (" << length << ")" << "\n~~~ " << stl_sprintf("0x%016zx: ", reinterpret_cast<uintptr_t>(start)) << " | " << stl_sprintf("0x%016zx: ", reinterpret_cast<uintptr_t>(string)) << " ~~~")
    // If GCC was used, the array has chars, but the start of the array is invalid, fail
    else if (is_gcc && length > 0 && !is_valid_dereference(reinterpret_cast<void*>(string->start), 1))
        FAIL_RET("invalid string pointer " << stl_sprintf("0x%" PRIxPTR, string->start))
    // If it's a small string, but the length is bigger than that allows, fail
    else if (is_local && length >= 16)
        FAIL_MSG("string length is too large for small string (" << length << ")")
    // If capacity is set and less than 0, fail
    else if (!(is_gcc && is_local) && capacity < 0)
        FAIL_MSG("string capacity is negative (" << capacity << ")")
    // If capacity is set and less than the string's length, fail
    else if (!(is_gcc && is_local) && capacity < length)
        FAIL_MSG("string capacity (" << capacity << ") is less than length (" << length << ")")
}

// Process an untyped pointer
static void check_unknown_pointer(const void* ptr)
{
    // Skipping dispatch.cpp Checker::check_unknown_pointer() line 787-807 (struct and class size reporting)

#ifndef WIN32
    // If the pointer is a valid string*, fail
    if (const std::string* str = validate_stl_string_pointer(&ptr))
        FAIL_MSG("untyped pointer is actually stl-string with value \"" << *str << "\" (length " << str->length() << ")")
    else
#endif
    // If there's a structure with a vtable definition at the pointer, fail
    if (const char* vtable_name = get_vtable_name(ptr))
        FAIL_MSG("pointer to a vtable: " << vtable_name)
}

// Validate a given vector, and return the array portion if valid
static IdentityRef validate_vector_size(const void* ptr, const type_identity* identity)
{
    struct vector_data
    {
        uintptr_t start;
        uintptr_t finish;
        uintptr_t end_of_storage;
    };

    // Get the vector's data by casting it to vector_data
    vector_data vector = *reinterpret_cast<const vector_data*>(ptr);

    // Get the size of the vector's items
    size_t item_size = identity ? identity->byte_size() : 0;
    // If the items or the vector are invalid, fail
    if (!item_size || vector.start > vector.finish || vector.start > vector.end_of_storage || vector.finish > vector.end_of_storage)
        return IdentityRef();

    // Calculate the unsigned length and capacity of the vector
    size_t ulength = size_t(vector.finish - vector.start);
    ptrdiff_t capacity = vector.end_of_storage - vector.start;

    // If the length or capacity of the array doesn't match up with the size of its items, fail
    if (ulength % item_size != 0 || size_t(capacity) % item_size != 0)
        return IdentityRef();

    // If the capacity is non-zero but the start isn't defined, fail
    if (capacity && !vector.start)
        return IdentityRef();
    
    // Get the pointer to the vector's start
    const void* start_ptr = reinterpret_cast<const void*>(vector.start);

    // If the capacity is non-zero but the 1st item isn't valid, fail
    if (capacity && !is_valid_dereference(start_ptr, getIdentityByteSize(identity, capacity / item_size)))
        return IdentityRef();

    // The vector is valid, so return an IdentityRef for the array part of it
    return IdentityRef(identity, start_ptr, ulength / item_size);
}

// Processes a vector
static void check_stl_vector(const void* ptr, const type_identity* item_identity)
{
    // Validate the vector, and get the array portion if valid
    IdentityRef vec_item = validate_vector_size(ptr, item_identity);

    // IdentityRef.path is originally used here to determine bad pointer vectors
    //  However, currently IdentityRef doesn't track the path
    //  This may end up being necessary
    /*
    // From dispatch.cpp Checker::check_stl_vector() line 828
    // skip bad pointer vectors
    if ((item.path.ends_with(".bad") || item.path.ends_with(".temp_save")) && item_identity->type() == IDTYPE_POINTER)
    */
    // If the vector contains pointers, fail
    if (item_identity->type() == IDTYPE_POINTER)
        return;

    // If the vector's array is valid, add it to the processing queue
    if (vec_item.ptr && vec_item.count)
        queue_item(vec_item);
}

// Processes a map
static void check_stl_map(const void* ptr)
{
#ifndef WIN32
    struct rb_tree_node_base {
        enum { COLOR_RED = false, COLOR_BLACK = true } color;
        rb_tree_node_base* parent; // (Probably the node above this one in the binary tree)
        rb_tree_node_base* left;
        rb_tree_node_base* right;
    };

    struct rb_tree_node : public rb_tree_node_base {
        union {
            int8_t data_i8;
            int16_t data_i16;
            int32_t data_i32;
            int64_t data_i64;
            int64_t data_i64s[4];
        };
    };

    struct map_data
    {
        struct {} compare; // (Probably masking out the comparison function pointer)
        rb_tree_node_base header; // (Probably a node whose parent is the root node)
        size_t node_count;
    };

    // Get the map's data by casting it to map_data
    const map_data* map = reinterpret_cast<const map_data*>(ptr);

    // If the map isn't valid, fail
    if (!is_valid_dereference(map, 1))
        FAIL_RET("invalid map pointer: " << map)
    // If the map is empty, fail
    if (!map->header.parent && map->header.left == &map->header && map->header.right == &map->header)
        return;
    // If the map's initial node is invalid, fail
    if (!is_valid_dereference(map->header.parent, 1))
        FAIL_RET("invalid map initial parent pointer: " << map->header.parent)

    struct search_queue_entry {
        const rb_tree_node_base* node;
        const rb_tree_node_base* parent;
        const std::string path;
        const void* ptr;
    };

    // The queue of nodes to search through
    std::queue<search_queue_entry> search_queue;
    // Map of pointers to node paths that have already been searched through
    std::unordered_map<const rb_tree_node_base*, std::string> visited_nodes_paths;
    // Add the root node to the search queue
    search_queue.push(search_queue_entry{ map->header.parent, nullptr, "header.parent", ptr });
    // Loop through the search queue until it's empty
    size_t num_visited_nodes = 0;
    while (!search_queue.empty()) {
        // Get the 1st node from the queue
        const search_queue_entry entry = search_queue.front();
        // Remove the node from the queue
        search_queue.pop();
        num_visited_nodes++;

        // Insert the node into the map of visited nodes
        auto insert_result = visited_nodes_paths.insert(decltype(visited_nodes_paths)::value_type(entry.node, entry.path));
        // If the insert failed because the node's pointer has already been visited, fail
        if (!insert_result.second)
            FAIL_BRK("cycle detected: node already visited at " << insert_result.first->second)

        // If the node's pointer is invalid, fail
        if (!is_valid_dereference(entry.ptr, 1))
            FAIL_CON("invalid node pointer: " << entry.ptr)

        // If the node's color isn't red or black (aka. 0 or 1), fail
        //  (Why do the nodes have colors?)
        if (entry.node->color != rb_tree_node_base::COLOR_RED && entry.node->color != rb_tree_node_base::COLOR_BLACK)
            FAIL_MSG("invalid map node color: " << int(entry.node->color))

        // If the node's parent doesn't match the one in the search queue element, fail
        if (entry.parent && entry.node->parent != entry.parent)
            FAIL_MSG("mismatched parent pointer: " << entry.node->parent)

        // If the node has a left branch, add it to the search queue
        if (entry.node->left)
            search_queue.push(search_queue_entry{ entry.node->left, entry.node, entry.path + "left", entry.node->left });
        // If the node has a right branch, add it to the search queue
        if (entry.node->right)
            search_queue.push(search_queue_entry{ entry.node->right, entry.node, entry.path + "right", entry.node->right });
    }

    // If the number of nodes in the map differs from the number of nodes found in the search, fail
    if (map->node_count != num_visited_nodes)
        FAIL_MSG("invalid map size (" << map->node_count << "): counted " << num_visited_nodes << " nodes")
#endif
}

// Processes an unordered map
static void check_stl_unordered_map(const void* ptr)
{
#ifndef WIN32
    struct hash_node_base
    {
        hash_node_base* next;
    };

    struct prime_rehash_policy
    {
        float max_load_factor;
        size_t next_resize;
    };

    struct unordered_map_data
    {
        hash_node_base* buckets;    // default: &single_bucket
        size_t bucket_count;        // default: 1
        hash_node_base before_begin;
        size_t element_count;       // default: 0
        prime_rehash_policy rehash_policy;
        hash_node_base* single_bucket;
    };

    // Get the unordered map's data by casting it to unordered_map_data
    const unordered_map_data* umap = reinterpret_cast<const unordered_map_data*>(ptr);

    // If the unordered map isn't valid, fail
    if (!is_valid_dereference(umap, 1))
        FAIL_RET("invalid unordered_map pointer: " << umap)

#define check_ptr_field(field, expect_null) \
        do { \
            if (((expect_null) && umap->field != nullptr) || (!(expect_null) && !is_valid_dereference(umap->field, 1))) \
                FAIL_MSG("invalid unordered_map::" #field " pointer: " << umap->field) \
        } while (0)
    // If the unordered map's bucket list isn't valid, fail
    check_ptr_field(buckets, false);
    // If the unordered map has no elements but has a non-null pointer to one,
    //  or if it has elements but its initial one isn't valid, fail
    check_ptr_field(before_begin.next, umap->element_count == 0);
#undef check_ptr_field

    // If the amount of elements in the unordered map is too big, fail
    if (umap->bucket_count > (1 << 24))
        FAIL_RET("unreasonable unordered_map element count: " << umap->bucket_count)
    // Loop through the buckets in the map
    size_t num_elements = 0;
    for (size_t i = 0; i < umap->bucket_count; i++) {
        // Loop through the elements in the bucket
        size_t num_bucket_elements = 0;
        for (hash_node_base* node = umap->buckets[i].next; node != nullptr; node = node->next) {
            // If the element is invalid, fail
            if (!is_valid_dereference(node, sizeof(hash_node_base)))
                FAIL_BRK("invalid node pointer in bucket " << i << ": " << node)
            // If the element isn't the 1st one, add to the bucket's element counter
            if (node != umap->buckets[i].next)
                num_bucket_elements++;
        }
        // Add the bucket's element count to the total
        num_elements += num_bucket_elements;
    }

    // If the number of nodes in the unordered map differs from the number of nodes found while looping, fail
    if (num_elements != umap->element_count)
        FAIL_MSG("invalid unordered_map size (" << umap->element_count << "): counted " << num_elements << " nodes")
#endif
}

// Check if a pointer is within one of global's fields
static bool is_in_global(const void* ptr)
{
    // Get global's fields
    const struct_field_info* fields = df::global::_identity.getFields();
    // Loop through the fields
    for (const struct_field_info* field = fields; field->mode != struct_field_info::END; field++)
    {
        // Get the byte size of the field
        size_t size = field->type->byte_size();
        // Get a pointer to the start of the field
        //  (How does the field's offset match up with its pointer?)
        //  (Maybe global always starts at memory address 0?)
        const void* start = *reinterpret_cast<const void* const*>(field->offset);
        // Get the distance between the start of the field and ptr
        size_t offset = uintptr_t(ptr) - uintptr_t(start);
        // If the pointer lies within this field, it's in global
        if (offset < size)
            return true;
    }

    // The pointer wasn't found in any of global's fields
    return false;
}

// Attempt to get the value of an int type from a pointer
static int64_t get_int_value(const void* ptr, const type_identity* type)
{
    // If the type is an int32_t, try to get it from the pointer
    if (type == df::identity_traits<int32_t>::get())
        return validate_and_dereference<int32_t>(ptr);
    // If the type is an uint32_t, try to get it from the pointer
    else if (type == df::identity_traits<uint32_t>::get())
        return validate_and_dereference<uint32_t>(ptr);
    // If the type is an int16_t, try to get it from the pointer
    else if (type == df::identity_traits<int16_t>::get())
        return validate_and_dereference<int16_t>(ptr);
    // If the type is an uint16_t, try to get it from the pointer
    else if (type == df::identity_traits<uint16_t>::get())
        return validate_and_dereference<uint16_t>(ptr);
    // If the type is an int64_t, try to get it from the pointer
    else if (type == df::identity_traits<int64_t>::get())
        return validate_and_dereference<int64_t>(ptr);
    // If the type is an uint64_t, try to get it from the pointer
    else if (type == df::identity_traits<uint64_t>::get())
        return int64_t(validate_and_dereference<uint64_t>(ptr));
    // If the type is an int8_t, try to get it from the pointer
    else if (type == df::identity_traits<int8_t>::get())
        return validate_and_dereference<int8_t>(ptr);
    // If the type is an uint8_t, try to get it from the pointer
    else if (type == df::identity_traits<uint8_t>::get())
        return validate_and_dereference<uint8_t>(ptr);
    // If the type isn't an int type, fail
    else
        FAIL_RETV("invalid int type", 0)
}

// Get the key, or one of the attributes, corresponding to an enum value
static const char* const* get_enum_item_attr_or_key(const enum_identity* identity, int64_t value, const char* attr_name)
{
    size_t index;
    // If the enum type has a valid ComplexData
    //  ComplexData contains key->value and value->key maps
    if (const enum_identity::ComplexData* cplx = identity->getComplex())
    {
        // Find the value in the value->key map
        auto it = cplx->value_index_map.find(value);
        // If the value isn't in the map, fail
        if (it == cplx->value_index_map.cend())
            return nullptr;
        // Get the value's index
        index = it->second;
    }
    // If it doesn't have a valid ComplexData
    else
    {
        // If the value is less than the first item or greater than the second item, fail
        if (value < identity->getFirstItem() || value > identity->getLastItem())
            return nullptr;
        // Assuming the enum's values are all consecutive, calculate the index
        //  based off the difference from the 1st value
        index = value - identity->getFirstItem();
    }

    // If looking for an attribute of the enum
    if (attr_name)
    {
        // Get the enum's attributes and their type
        const void* attrs = identity->getAttrs();
        const struct_identity* attr_type = identity->getAttrType();
        // If no attributes or no types are found, fail
        if (!attrs || !attr_type)
            return nullptr;

        // Index into the attribute corresponding with the index
        attrs = PTR_ADD(attrs, attr_type->byte_size() * index);
        // For each field in the attribute's type, if the name matches 'attr_name' then return its value
        for (auto field = attr_type->getFields(); field->mode != struct_field_info::END; field++)
            if (!strcmp(field->name, attr_name))
                return reinterpret_cast<const char* const*>(PTR_ADD(attrs, field->offset));

        // The specified attribute could not be found, so fail
        return nullptr;
    }

    // Looking for the value's key, so return its address
    return &identity->getKeys()[index];
}

// Get the key corresponding to an enum value
static const char* const* get_enum_item_key(const enum_identity* identity, int64_t value)
{
    return get_enum_item_attr_or_key(identity, value, nullptr);
}

// Processes a primitive item
static void dispatch_primitive(const void* ptr, const type_identity* identity)
{
    // If the item is a string, process it as a string
    if (identity == df::identity_traits<std::string>::get())
        check_stl_string(ptr);
    // If the item is a C-style string (char*), fail
    else if (identity == df::identity_traits<char*>::get())
        FAIL_MSG("TODO check c strings")
    // If the item is a boolean
    else if (identity == df::identity_traits<bool>::get())
    {
        // Cast the byte to an int8_t
        uint8_t val = *reinterpret_cast<const uint8_t*>(ptr);
        // If it's higher than 1 and not newly allocated memory and not newly cleared memory, fail
        if (val > 1 && perturb_byte && val != perturb_byte && val != (perturb_byte ^ 0xff))
            FAIL_MSG("invalid value for bool: " << int(val))
    }
    // If the item is an integer, check if it could be a pointer
    else if (dynamic_cast<const df::integer_identity_base*>(identity))
    {
        // Skipping dispatch.cpp Checker::dispatch_primitive() line 307
        // Checker::check_possible_pointer() does nothing if sizes == false
        //FAIL_MSG("TODO check ints?") // Happens too often
    }
    // If the item is a floating point number, fail
    else if (dynamic_cast<const df::float_identity_base*>(identity))
        FAIL_MSG("TODO check floats?")
    // If the item is anything else, fail
    else
        FAIL_MSG("unexpected primitive type")
}

// Processes a pointer
static void dispatch_pointer(const void* ptr, const type_identity* identity, size_t count)
{
    // Make sure that the pointer is valid and initialized
    const void* target_ptr = validate_and_dereference<const void*>(ptr);
    if (!target_ptr || uintptr_t(target_ptr) == UNINIT_PTR)
        return;

    // Get the type identity of the target the pointer references
    const type_identity* target = static_cast<const pointer_identity*>(identity)->getTarget();
    // If it has no target type
    if (!target)
    {
        // Process the untyped pointer
        check_unknown_pointer(target_ptr);
        return;
    }

    // Create an IdentityRef for the target item
    IdentityRef target_item = IdentityRef(target, target_ptr);
    target_item.count = count;

    // If the item is an element in an array, or a small object
    //  256 is an arbitrarily chosen size threshold
    if (count || target->byte_size() <= 256)
    {
        //global_console->out << "small ";
        // Try to add the item to the processing queue
        //  target is small, or we are inside an array of pointers; handle now
        if (queue_item(target_item))
        {
            // Remove the item from the queue
            //  we insert it into the queue to make sure we're not stuck in a loop
            //  get it back out of the queue to prevent the queue growing too big
            queue.pop_back();
            //global_console->out << target_item.count << target_item.enumIdentity << target_item.inStructure << target_item.isArray << std::endl;
            // Process the item
            dispatch_item(target_item);
        }
        /*
        else
            FAIL_MSG("QUEUE Fail")
        */
    }
    // If the item isn't from an array and is large
    else
    {
        //global_console->out << "large ";
        // Add the item to the processing queue
        //  target is large and not part of an array; handle later
        queue_item(target_item);
    }
}

// Processes a container
static void dispatch_container(const void* ptr, const type_identity* identity)
{
    // Get the container's type data
    const container_identity* container = static_cast<const container_identity*>(identity);
    // Get what the container's type name would be if it contained voids
    std::string base_container = container->getFullName(nullptr);
    // If the container is a vector, process it as a vector
    if (base_container == "vector<void>")
        check_stl_vector(ptr, container->getItemType());
    // If the container is a deque, fail
    else if (base_container == "deque<void>")
        FAIL_MSG("TODO: check deque?")
    // If the container is a DfArray, fail
    else if (base_container == "DfArray<void>")
        FAIL_MSG("TODO: check DfArray")
    // If the container is a map or set, process it as a map
    else if (base_container.starts_with("map<") || base_container.starts_with("set<"))
        check_stl_map(ptr);
    // If the container is an unordered_map or unordered_set, process it as an unordered map
    else if (base_container.starts_with("unordered_map<") || base_container.starts_with("unordered_set<"))
        check_stl_unordered_map(ptr);
    // If it's some other type of container, fail
    else
        FAIL_MSG("invalid container type")
}

// Processes a bit container
static void dispatch_bit_container(const void* ptr, const type_identity* identity)
{
    // Get the container's type data
    const container_identity* container = static_cast<const container_identity*>(identity);
    // Get what the container's type name would be if it contained voids
    std::string base_container = container->getFullName(nullptr);
    // If the container is a BitArray, fail
    if (base_container == "BitArray<>")
        FAIL_MSG("TODO: check DF bit array")
    // If the container is a vector of booleans, fail
    else if (base_container == "vector<bool>")
        FAIL_MSG("TODO: check stl bit vector")
    // If it's some other type of container, fail
    else
        FAIL_MSG("invalid bit container")
}

// Processes a bitfield
static void dispatch_bitfield(const void* ptr, const type_identity* identity)
{
    // Skipping dispatch.cpp Checker::dispatch_bitfield() line 421-426 (struct and class size reporting)

    // Get the bitfield's type data
    const bitfield_identity* bitfield_type = static_cast<const bitfield_identity*>(identity);
    // Get the bitfield's value, using its byte size
    uint64_t bitfield_value;
    switch (bitfield_type->byte_size())
    {
    case 1:
        // Get the value, if valid
        bitfield_value = validate_and_dereference<uint8_t>(ptr);
        // don't check for uninitialized; too small to be sure
        break;
    case 2:
        // Get the value, if valid
        bitfield_value = validate_and_dereference<uint16_t>(ptr);
        // If uninitialized, set to 0
        if (bitfield_value == 0xd2d2)
            bitfield_value = 0;
        break;
    case 4:
        // Get the value, if valid
        bitfield_value = validate_and_dereference<uint32_t>(ptr);
        // If uninitialized, set to 0
        if (bitfield_value == 0xd2d2d2d2)
            bitfield_value = 0;
        break;
    case 8:
        // Get the value, if valid
        bitfield_value = validate_and_dereference<uint64_t>(ptr);
        // If uninitialized, set to 0
        if (bitfield_value == 0xd2d2d2d2d2d2d2d2)
            bitfield_value = 0;
        break;
    default:
        // The bitfield's byte size is unexpected, so fail
        FAIL_MSG("invalid bitfield size");
        bitfield_value = 0;
        break;
    }

    // Get the bits in the bifield
    int num_bits = bitfield_type->getNumBits();
    const bitfield_item_info* bits = bitfield_type->getBits();
    // Repeat 64 times
    //  (Why always 64?)
    for (int i = 0; i < 64; i++)
    {
        // Bitshift the value 1 to the right (aka. Divide it by 2)
        bitfield_value >>= 1;
        // If the number of bits is even, skip
        if (!(num_bits & 1))
            continue;

        // If past the last bit, fail
        if (i >= num_bits || !bits[i].size)
            FAIL_MSG("bitfield bit " << i << " is out of range")
        // If the bit is valid but has no name
        else if (bits[i].size > 0 && !bits[i].name)
            FAIL_MSG("bitfield bit " << i << " is unnamed")
        // If the bit is part of a multi-bit field without a name, fail
        //  (Wouldn't this only work correctly if bits[i].size <= 0??)
        else if (!bits[i + bits[i].size].name)
            FAIL_MSG("bitfield bit " << i << " (part of a field starting at bit " << (i + bits[i].size) << ") is unnamed")
    }
}

// Processes an enum
static void dispatch_enum(const void* ptr, const type_identity* identity)
{
    // Skipping dispatch.cpp Checker::dispatch_enum() line 491-496 (struct and class size reporting)

    // Get the enum's type data
    const enum_identity* enum_type = static_cast<const enum_identity*>(identity);
    // Get the int equivalent of the enum value
    int64_t enum_value = get_int_value(ptr, enum_type->getBaseType());
    // If it's uninitialized, fail
    if (
        (enum_type->byte_size() == 2 && uint16_t(enum_value) == 0xd2d2)
        || (enum_type->byte_size() == 4 && uint32_t(enum_value) == 0xd2d2d2d2)
        || (enum_type->byte_size() == 8 && uint64_t(enum_value) == 0xd2d2d2d2d2d2d2d2)
    )
        return;

    // If it's in one of global's fields and set to 0, fail
    if (is_in_global(ptr) && enum_value == 0)
        return;

    // Get the enum value's key
    const char* const* enum_name = get_enum_item_key(enum_type, enum_value);
    // If unable to get the key, fail
    if (!enum_name)
        FAIL_RET("enum value (" << enum_value << ") is out of range" << "\n~~~ " << stl_sprintf("0x%016zx: ", reinterpret_cast<uintptr_t>(ptr)) << " | " << enum_type->getBaseType() << " ~~~")
    // If the key is unnamed, fail
    if (!*enum_name)
        FAIL_MSG("enum value (" << enum_value << ") is unnamed");
}

// Process a tagged union
static void dispatch_tagged_union(const IdentityRef& item, const IdentityRef& tag_item, const char* attr_name)
{
    // If the tag isn't an enum or the item isn't a union, fail
    if (tag_item.identity->type() != IDTYPE_ENUM || item.identity->type() != IDTYPE_UNION)
        FAIL_RET("invalid item")

    // Get the item's type data
    const union_identity* union_type = static_cast<const union_identity*>(item.identity);
    // Read the item union as an array of bytes in int form
    const uint8_t* union_data_ptr = reinterpret_cast<const uint8_t*>(item.ptr);
    // Store the 1st byte of the item
    uint8_t padding_byte = *union_data_ptr;
    bool all_padding = false;
    // If the 1st byte is 0x00, 0xd2, or 0xff, it is assumed to be a padding byte
    if (padding_byte == 0x00 || padding_byte == 0xd2 || padding_byte == 0xff)
    {
        // Loop through the item's bytes looking for a non-padding byte
        all_padding = true;
        for (size_t i = 0; i < union_type->byte_size(); i++)
        {
            // If a byte is different from the padding byte
            if (union_data_ptr[i] != padding_byte)
            {
                // Not all of the item's bytes are padding
                all_padding = false;
                break;
            }
        }
    }

    // Get the tag's type data
    const enum_identity* tag_identity = static_cast<const enum_identity*>(tag_item.identity);
    // Read the tag enum as an int
    int64_t tag_value = get_int_value(tag_item.ptr, tag_identity->getBaseType());
    // If the item is all uninitialized bytes
    if (all_padding && padding_byte == 0xd2)
    {
        // special case: completely uninitialized
        // Check the tag is initialized, based off its byte size
        switch (tag_identity->byte_size())
        {
        case 1:
            // If the tag is uninitialized, end
            if (tag_value == 0xd2)
                return;
            break;
        case 2:
            // If the tag is uninitialized, end
            if (tag_value == 0xd2d2)
                return;
            break;
        case 4:
            // If the tag is uninitialized, end
            if (tag_value == 0xd2d2d2d2)
                return;
            break;
        case 8:
            // If the tag is uninitialized, end
            if (uint64_t(tag_value) == 0xd2d2d2d2d2d2d2d2)
                return;
            break;
        default:
            // The tag's byte size is unexpected, so fail
            FAIL_BRK("invalid tag size");
        }
    }

    // Try and get the name of the tag's enum value
    const char* const* tag_name = get_enum_item_attr_or_key(tag_identity, tag_value, attr_name);
    // If unable to get the name, fail
    if (!tag_name)
        FAIL_RET("tagged union tag (accessed as ????) value (" << tag_value << ") not defined in enum " << tag_item.identity->getFullName())

    // If it's unnamed, fail
    if (!*tag_name)
        FAIL_RET("tagged union tag (accessed as ????) value (" << tag_value << ") is unnamed")

    // Loop through the item's fields
    for (const struct_field_info* field = union_type->getFields(); field->mode != struct_field_info::END; field++)
    {
        // If the field's name doesn't match the tag's name, skip it
        if (strcmp(field->name, *tag_name))
            continue;

        // If the field is offset from the start of the union, fail
        if (field->offset != 0)
            FAIL_MSG("union field is offset")

        // Process the field
        dispatch_item(IdentityRef(field, item.ptr));
        // Processed a field with a name matching the tag's, so end
        return;
    }

    // don't ask for fields if it's all padding
    if (all_padding)
        return;

    // None of the item's fields matched the tag's name, so fail
    FAIL_MSG("tagged union missing " << *tag_name << " field to match tag (accessed as ????) value (" << tag_value << ")")
}

// Process a list of union and tags
static void dispatch_tagged_union_vector(const IdentityRef& container, const IdentityRef& tag_container, const char* attr_name)
{
    // Get the container's type data
    const container_identity* union_container_identity = static_cast<const container_identity*>(container.identity);
    // Get the type data of the container's items
    const type_identity* union_item_identity = union_container_identity->getItemType();
    // If the container's type isn't a container type, wrap the type in a pointer
    if (union_container_identity->type() != IDTYPE_CONTAINER)
        union_item_identity = wrap_in_pointer(union_item_identity);

    // Get the tag container's type data
    const container_identity* tag_container_identity = static_cast<const container_identity*>(tag_container.identity);
    // Get what the name of the tag container's type would be if its items were of type void
    std::string tag_container_base = tag_container_identity->getFullName(nullptr);
    // If the tag container is a vector
    if (tag_container_base == "vector<void>")
    {
        // Attempt to get an IdentityRef for the container's array
        IdentityRef vec_union = validate_vector_size(container.ptr, union_item_identity);
        // Get the type data of the tag container's items
        const type_identity* tag_item_identity = tag_container_identity->getItemType();
        // Attempt to get an IdentityRef for the tag container's array
        IdentityRef vec_tag = validate_vector_size(tag_container.ptr, tag_item_identity);
        // If either the container's or tag container's array is invalid, fail
        if (!vec_union.ptr || !vec_tag.ptr)
            return;
        // If both of the arrays are empty, fail
        if (!vec_union.count && !vec_tag.count)
            return;
        // If the arrays are of different lengths, fail
        if (vec_union.count != vec_tag.count)
            FAIL_MSG("tagged union vector is " << vec_union.count << " elements, but tag vector (accessed as ????) is " << vec_tag.count << " elements")

        // Loop through the elements of both of the arrays
        for (size_t i = 0; i < vec_union.count && i < vec_tag.count; i++)
        {
            // Process the union from container with the tag from tag_container
            dispatch_tagged_union(vec_union, vec_tag, attr_name);
            // Advance the pointers to the next array elements
            vec_union.ptr = PTR_ADD(vec_union.ptr, union_item_identity->byte_size());
            vec_tag.ptr = PTR_ADD(vec_tag.ptr, tag_item_identity->byte_size());
        }
    }
    // If the tag container is a vector of booleans, fail
    //  (How would this ever be reached if nullptr is passed to getFullName()??)
    else if (tag_container_base == "vector<bool>")
        FAIL_MSG("invalid boolean vector")
    else
        FAIL_MSG("invalid non-vector container")
}

// Processes a field
static void dispatch_field(const void* ptr, const struct_identity* identity, const struct_field_info* field)
{
    // If the field is a method, fail
    if (
        field->mode == struct_field_info::OBJ_METHOD
        || field->mode == struct_field_info::CLASS_METHOD
    )
        return;

    // Create an IdentityRef for the field
    IdentityRef field_item = IdentityRef(field, PTR_ADD(ptr, field->offset));
    
    // Get the field's union tag field, if it's a union
    const struct_field_info* tag_field = find_union_tag(identity, field);
    // If the field is a union with a valid tag field
    if (tag_field)
    {
        // Create an IdentityRef for the tag field
        IdentityRef tag_item = IdentityRef(tag_field, PTR_ADD(ptr, tag_field->offset));
        // Get the union tag attribute name, if possible
        const char* attr_name = field->extra ? field->extra->union_tag_attr : nullptr;
        // If the tag field is a container, process as a tagged union vector
        if (tag_item.identity->isContainer())
            dispatch_tagged_union_vector(field_item, tag_item, attr_name);
        // If the tag field isn't a container, process as a tagged union
        else
            dispatch_tagged_union(field_item, tag_item, attr_name);
        
        // After processing the tag field, end
        return;
    }

    // Process the field
    dispatch_item(field_item);
}

// Processes a struct
static void dispatch_struct(const void* ptr, const type_identity* identity)
{
    // Get the struct's type data
    const struct_identity* structure = static_cast<const struct_identity*>(identity);
    // Loop through the parents of the struct
    for (const struct_identity* p = structure; p; p = p->getParent())
    {
        // Get the struct's fields
        const struct_field_info* fields = p->getFields();
        // If it has no fields, skip it
        if (!fields)
            continue;

        // Loop through the struct's fields, processing each of them
        for (const struct_field_info* field = fields; field->mode != struct_field_info::END; field++)
            dispatch_field(ptr, structure, field);
    }
}

// Processes a class
static void dispatch_class(const void* ptr, const type_identity* identity)
{
    // Attempt to get the vtable name of the class
    const char* vtable_name = get_vtable_name(ptr);
    // If unable to get the vtable name, fail
    if (!vtable_name)
        return;

    // Get the virtual type data of the identity
    const virtual_identity* base_identity = static_cast<const virtual_identity*>(identity);
    // Get the virtual pointer
    const virtual_ptr vptr = static_cast<virtual_ptr>(const_cast<void*>(ptr));
    // Get the virtual type data of the pointer
    const virtual_identity* videntity = virtual_identity::get(vptr);
    // If unable to find the pointer's virtual identity, fail
    if (!videntity)
        FAIL_RET("unidentified subclass of " << base_identity->getFullName() << ": " << vtable_name)
    // If the 2 identities are different and the pointer's isn't a subclass, fail
    if (base_identity != videntity && !base_identity->is_subclass(videntity))
        FAIL_RET("expected subclass of " << base_identity->getFullName() << ", but got " << videntity->getFullName())

    // IdentityRef.path is originally used here to determine repeat accesses to the same class
    //  However, currently IdentityRef doesn't track the path
    //  This may end up being necessary
    /*
    // From dispatch.cpp Checker::dispatch_class() line 601
    // If the data map contains ptr and the path stored for it matches item's
    if (data.count(ptr) && data.at(ptr).first == item.path)
    */
    // If the data map contains ptr, replace the IdentityRef's identity with videntity
    if (data.count(ptr))
        data.at(ptr).identity = videntity;

    // Process the item as a struct
    dispatch_struct(ptr, videntity);
}

// Processes a buffer
static void dispatch_buffer(const void* ptr, const type_identity* identity)
{
    // Get the container's type data
    const container_identity* container = static_cast<const container_identity*>(identity);
    // Get the container items' type data
    const type_identity* item_identity = container->getItemType();
    // Create an item for the buffer as an array of the items
    IdentityRef item = IdentityRef(item_identity, ptr, container->byte_size() / item_identity->byte_size());
    // Set the item's enum identity to match the buffer's
    item.enumIdentity = static_cast<const enum_identity*>(container->getIndexEnumType());
    // Declare it as in a structure
    item.inStructure = true;
    // Process the buffer
    dispatch_item(item);
}

// Processes a pointer vector
static void dispatch_stl_ptr_vector(const void* ptr, const type_identity* identity)
{
    // Get the container's type data
    const container_identity* container = static_cast<const container_identity*>(identity);
    // Get the container items' type data wrapped in a pointer
    const type_identity* ptr_type = wrap_in_pointer(container->getItemType());
    // Process as a vector
    check_stl_vector(ptr, ptr_type);
}

// Process an untagged union
static void dispatch_untagged_union(const void* ptr, const type_identity* identity)
{
    // special case for large_integer weirdness
    // If the identity is that of a 16 byte int
    if (identity == df::identity_traits<df::large_integer>::get())
    {
        // it's 16 bytes on 64-bit linux due to a messy header in libgraphics
        // but only the first 8 bytes are ever used
        // Process it as an 8 byte integer
        dispatch_primitive(ptr, df::identity_traits<int64_t>::get());
        return;
    }

    // Identity didn't match the case, so fail
    FAIL_MSG("unhandled untagged union: ????");
}

#pragma endregion

// Handles the classification of a valid item for processing
static void dispatch_single_item(const void* ptr, const type_identity* identity, size_t count)
{
    // If maxerrors is reduced to 0, terminate processing
    if (!maxerrors)
        return queue.clear();

    //global_console->out << "Dispatch " << stl_sprintf("0x%08zx: ", reinterpret_cast<uintptr_t>(ptr)) << std::endl;

    // Based on the type of data, process the item differently
    switch (identity->type())
    {
    case IDTYPE_GLOBAL:
    case IDTYPE_FUNCTION:
        FAIL_MSG("invalid item identity")
        break;
    case IDTYPE_PTR_CONTAINER:
        // Replacing dispatch.cpp Checker::dispatch_single_item() line 255
        // Checker::dispatch_ptr_container() is made to always fail, so fail directly
        FAIL_MSG("pointer container")
        break;
    case IDTYPE_OPAQUE:
        // (What is this??)
        break;
    case IDTYPE_PRIMITIVE:
        dispatch_primitive(ptr, identity);
        break;
    case IDTYPE_POINTER:
        dispatch_pointer(ptr, identity, count);
        break;
    case IDTYPE_CONTAINER:
        dispatch_container(ptr, identity);
        break;
    case IDTYPE_BIT_CONTAINER:
        dispatch_bit_container(ptr, identity);
        break;
    case IDTYPE_BITFIELD:
        dispatch_bitfield(ptr, identity);
        break;
    case IDTYPE_ENUM:
        dispatch_enum(ptr, identity);
        break;
    case IDTYPE_STRUCT:
        dispatch_struct(ptr, identity);
        break;
    case IDTYPE_CLASS:
        dispatch_class(ptr, identity);
        break;
    case IDTYPE_BUFFER:
        dispatch_buffer(ptr, identity);
        break;
    case IDTYPE_STL_PTR_VECTOR:
        dispatch_stl_ptr_vector(ptr, identity);
        break;
    case IDTYPE_UNION:
        dispatch_untagged_union(ptr, identity);
        break;
    }
}

// Validates an item for processing
static void dispatch_item(const IdentityRef& item) {
    // If the item isn't valid, fail
    if (!is_valid_dereference(item.ptr, item.getByteSize()))
        return;

    // If the item isn't a list, process it directly
    if (!item.count)
        return dispatch_single_item(item.ptr, item.identity, item.count);

    // Skipping dispatch.cpp Checker::dispatch_item() line 176-213 (struct and class size reporting)

    // Get the list's start point and item size
    auto ptr = item.ptr;
    auto size = item.identity->byte_size();
    // Loop through each element of the list
    for (size_t i = 0; i < item.count; i++)
    {
        // Dispatch the element
        dispatch_single_item(ptr, item.identity, item.count);
        // Advance to the next element in the list
        ptr = PTR_ADD(ptr, size);
    }
}

// Processes the 1st item in the queue
static bool process_queue()
{
    // If the processing queue is empty, fail
    if (queue.empty())
        return false;

    // Gets the first item from the queue
    //  (Not entirely sure what std::move does. It's something about
    //      passing data around without making copies of objects)
    IdentityRef&& qItem = std::move(queue.front());
    // Pop the first item from the queue
    queue.pop_front();

    // Get the stored IdentityRef for this item
    auto elem = data.find(qItem.ptr);
    // If not found, skip processing this item
    //  (This happens when the it's part of another structure in data)
    if (elem == data.end())
        return true;

    // Process this item
    dispatch_item(elem->second);

    return true;
}

// Simplified version of main.cpp command() on line 53
static void tester(color_ostream& out, std::string path) {
    global_console = new GlobalConsole(out);

    mapped = std::vector<t_memrange>();
    data = std::map<const void*, IdentityRef>();
    queue = std::deque<IdentityRef>();
    maxerrors = 100000;

    // Grab the Lua state and stick it in a StackUnwinder,
    //  which'll take care of resetting the Lua state on destruction
    StackUnwinder unwinder(State);

    // Run "pcall(utils.df_expr_to_ref(path))" with Lua
    PushModulePublic(out, "utils", "df_expr_to_ref");
    Push(path);
    if (!SafeCall(out, 1, 1))
        FAIL_RET("unable to get expression reference")

    // Create an IdentityRef for the Lua object
    IdentityRef stateRef(State);
    if (!stateRef.ptr || !stateRef.identity)
        FAIL_RET("invalid reference from expression")

    // Store DF's memory ranges in mapped
    DFHack::Core::getInstance().p->getMemRanges(mapped);

    // Debug stuffs
    out << "Start Address: " << stateRef.ptr << std::endl;
    out << "End Address: " << PTR_ADD(stateRef.ptr, stateRef.getByteSize()) << std::endl;
    out << "Identity Name: " << stateRef.identity->getFullName() << std::endl;
    if (stateRef.identity->type() == IDTYPE_CLASS) {
        out << "Is Class" << std::endl;
        auto vtableName = get_vtable_name(stateRef.ptr);
        if (vtableName)
            out << "VTable Name: " << vtableName << std::endl;
        else
            out << "No VTable Name" << std::endl;
    }

    // Add stateRef to the processing queue
    queue_item(stateRef);
    out << "Queued" << std::endl;

    // Continued by main.cpp command() on line 144

    // Process items from in queue until it's empty
    while (process_queue())
        out << "checked fields" << std::endl;

    out << "Finished checking fields" << std::endl;

    return;
}





static command_result do_command(color_ostream& out_, vector<string>& parameters) {
    // Store the value used used for newly allocated bytes
    perturb_byte = check_malloc_perturb();
    if (!perturb_byte)
        out_.printerr("check-structures-sanity: MALLOC_PERTURB_ not set. Some checks may be bypassed or fail.\n");

    // be sure to suspend the core if any DF state is read or modified
    CoreSuspender suspend;

    /*
    // Create and open a text file
    std::ofstream MyFile("world_dump.txt");

    // Close the file
    MyFile.close();
    */

    tester(out_, "df.global.gview.view");

    return CR_OK;
}