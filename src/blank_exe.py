from src.utils import *
import random


class BlankExe:
    """
    Simulate the process of blanket execution
    When entering a function, give any value needed as a random value
    """

    def __init__(self, p: angr.Project, cfg=None):
        self.p = p
        self.cfg = cfg
        if self.cfg is None:
            self.cfg = self.p.analyses.CFGFast()

    def get_blank_state(self, addr):
        return self.p.factory.blank_state(addr=addr)

    def exe_from_addr(self, addr):
        state = self.get_blank_state(addr)
        # next we need to initialize all memory and registers being read
