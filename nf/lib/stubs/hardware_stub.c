#include <hardware_stub.h>

#include <klee/klee.h>


// Unused - see below
void stub_unused(void) { }

void
stub_hardware_init(void)
{
	// Manually call the ixgbe device registration and PCI bus registration,
	// since they're constructor functions (which KLEE doesn't execute)
	// Except the function isn't in any header, only in the C files;
	// so we use KLEE's aliasing to access them. Sneaky!

//	klee_alias_function("stub_unused", "pciinitfn_net_ixgbe");
//	stub_unused();

//	klee_alias_function("stub_unused", "businitfn_pci");
//	stub_unused();
}
