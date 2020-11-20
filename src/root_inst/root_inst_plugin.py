import logging
from copy import deepcopy

from angr.errors import AngrError
from angr.state_plugins.plugin import SimStatePlugin

from src.formulas_extractor import FormulaExtractor
from src.root_inst.root_instrs import ends_with_root_instr
from src.utils import get_block_last_insn

from src.simple_cfg import SimpleCFG

l = logging.getLogger(name=__name__)


class RootInstPlugin(SimStatePlugin):

    def __init__(self, parent_id=0):
        super(RootInstPlugin, self).__init__()
        self.state = None
        self.current_ribb = []
        self.visited = set()
        self.writing_records = set()
        self.parent_id = parent_id

    def set_state(self, state):
        super(RootInstPlugin, self).set_state(state)

    def ends_rib(self):
        block = self.state.block()
        return ends_with_root_instr(block)

    def for_end_rib_step(self):
        pass

    def for_all_step(self):
        """
        it must be called in RootInstTech while going a step
        return True if the state contains a valid block
        return False if the state contains no valid block
        """
        try:
            if self.state.addr == 0:
                return False
            if self.state is not None:
                block = self.state.block()
                if block is not None:
                    if block.addr in self.visited:
                        return False
                    self.visited.add(block.addr)
                    self.current_ribb.append(block.addr)
                    self.writing_records.update(
                        FormulaExtractor.get_writing_reg_record(block, self.state.project.arch.name))
                    return True
            return False
        except AngrError as e:
            print(e)
            return False

    def get_rib_id(self):
        return tuple(self.current_ribb)

    def __getstate__(self):
        d = dict(self.__dict__)
        d['state'] = None
        return d

    def copy(self, _memo):
        n = RootInstPlugin()
        n.current_ribb = deepcopy(self.current_ribb)
        n.visited = deepcopy(self.visited)
        n.writing_records = deepcopy(self.writing_records)
        n.parent_id = self.parent_id
        return n

    def merge(self, _others, _merge_conditions, _common_ancestor=None):  # pylint:disable=unused-argument
        return False

    def widen(self, _others):  # pylint:disable=unused-argument
        l.warning("Widening not implemented for %s" % self.__class__.__name__)

    def init_state(self):
        """
        Use this function to perform any initialization on the state at plugin-add time
        """
        pass


class ContinuousInfoPlugin(SimStatePlugin):

    def __init__(self):
        super(ContinuousInfoPlugin, self).__init__()
        self.rib = []
        self.path_history = []
        self.ri_path_history = []
        self.visited = set()

    def set_state(self, state):
        super(ContinuousInfoPlugin, self).set_state(state)

    def copy(self, _memo):
        n = ContinuousInfoPlugin()
        n.rib = self.rib.copy()
        n.path_history = self.path_history.copy()
        n.ri_path_history = self.ri_path_history.copy()
        n.visited = self.visited.copy()
        return n

    def merge(self, _others, _merge_conditions, _common_ancestor=None):
        return False

    def widen(self, _others):
        l.warning("Widening not implemented for %s" % self.__class__.__name__)

    def init_state(self):
        """
        Use this function to perform any initialization on the state at plugin-add time
        """
        pass

    def for_all_step(self, ida_cfg: SimpleCFG, callees: dict):
        """
        :return: do SE on this state, has_successors, ends with root instruction
        """
        do_se, has_succ, ends_ri, ends_se = False, False, False, False
        cur_block_id = self.state.addr
        if cur_block_id in self.visited:
            return do_se, has_succ, ends_ri, ends_se
        if cur_block_id not in ida_cfg.pool.keys():
            return do_se, has_succ, ends_ri, ends_se
        do_se = True
        self.rib.append(cur_block_id)
        self.path_history.append(cur_block_id)
        self.visited.add(cur_block_id)

        if len(ida_cfg.pool[cur_block_id].children) > 0:
            has_succ = True
        else:
            # this node has no successor, end SE after this node
            ends_se = True
            # set the last instruction as root instruction by default (though it may not be true)
            ends_ri = True

        last_inst = get_block_last_insn(self.state.block())
        if last_inst.address in callees.keys():
            ends_ri = True

        if ends_ri:
            self.ri_path_history.append(tuple(self.rib))
            self.rib.clear()
        return do_se, has_succ, ends_ri, ends_se
