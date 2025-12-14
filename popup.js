// popup.js - DealPal
document.addEventListener('DOMContentLoaded', () => {
  const scanBtn = document.getElementById('scanBtn');
  const trackedList = document.getElementById('trackedList');
  const consentCheckbox = document.getElementById('consent');

  // Load stored tracked items and consent
  chrome.storage.local.get(['trackedItems', 'shareConsent'], (data) => {
    const items = data.trackedItems || [];
    if (items.length) {
      trackedList.innerHTML = '';
      items.forEach(item => addItemToList(item));
    } else {
      trackedList.innerHTML = '<div class="no-items">No tracked items yet.</div>';
    }
    consentCheckbox.checked = !!data.shareConsent;
  });

  // Scan button: injects getProductInfo into active tab
  scanBtn.addEventListener('click', async () => {
    try {
      const [tab] = await chrome.tabs.query({ active: true, currentWindow: true });
      if (!tab || !tab.id) return;
      chrome.scripting.executeScript({
        target: { tabId: tab.id },
        func: getProductInfo
      }, (results) => {
        if (!results || !results[0] || !results[0].result) {
          alert('No product information found on this page.');
          return;
        }
        const product = results[0].result;
        saveTrackedItem(product);
        // refresh UI
        prependItemToList(product);
      });
    } catch (e) {
      console.error('Scan failed', e);
      alert('Scan failed. See console for details.');
    }
  });

  // Save consent on change
  consentCheckbox.addEventListener('change', () => {
    chrome.storage.local.set({ shareConsent: consentCheckbox.checked });
  });

  // Helpers
  function addItemToList(item) {
    const node = document.createElement('div');
    node.className = 'item';
    const title = item.title || item.url || 'Unknown product';
    const price = item.price || item.priceText || 'N/A';
    node.innerHTML = `<div><strong>${escapeHtml(title)}</strong></div><div class="small">Latest: ${escapeHtml(price)}</div>`;
    trackedList.appendChild(node);
  }

  function prependItemToList(item) {
    // ensure list exists
    if (trackedList.querySelector('.no-items')) trackedList.innerHTML = '';
    const node = document.createElement('div');
    node.className = 'item';
    const title = item.title || item.url || 'Unknown product';
    const price = item.price || item.priceText || 'N/A';
    node.innerHTML = `<div><strong>${escapeHtml(title)}</strong></div><div class="small">Latest: ${escapeHtml(price)}</div>`;
    trackedList.prepend(node);
  }

  function saveTrackedItem(item) {
    chrome.storage.local.get(['trackedItems'], (data) => {
      const arr = data.trackedItems || [];
      // keep simple dedupe by url or title
      const exists = arr.find(i => (i.url && i.url === item.url) || (i.title && i.title === item.title));
      if (!exists) arr.unshift(item);
      chrome.storage.local.set({ trackedItems: arr });
    });
  }

  function escapeHtml(text) {
    if (!text) return '';
    return text.replace(/[&<>"'`]/g, (s) => {
      const map = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;', '`': '&#96;' };
      return map[s];
    });
  }

  // This function runs in the page context and extracts simple product info.
  // It returns an object with title, priceText, price (numeric if parsed), url and timestamp.
  function getProductInfo() {
    try {
      const titleCandidates = [
        'h1', '[data-testid="product-title"]', '[itemprop="name"]', '.product-title', '#productTitle', '.prod-ProductTitle'
      ];
      let title = '';
      for (const sel of titleCandidates) {
        const el = document.querySelector(sel);
        if (el && el.innerText && el.innerText.trim().length > 0) {
          title = el.innerText.trim();
          break;
        }
      }
      if (!title) title = document.title || '';

      // price selectors common across sites
      const priceCandidates = [
        '[data-test="price"]', '.priceblock_ourprice', '.priceblock_dealprice', '.a-price .a-offscreen',
        '[itemprop="price"]', '.price', '.prod-Price', '.price-characteristic', '.notranslate'
      ];
      let priceText = '';
      for (const sel of priceCandidates) {
        const el = document.querySelector(sel);
        if (el && (el.innerText || el.textContent)) {
          priceText = (el.innerText || el.textContent).trim();
          if (priceText.length) break;
        }
      }

      // normalize numeric price where possible
      let numeric = null;
      if (priceText) {
        const num = parseFloat(priceText.replace(/[^\d\.]/g, ''));
        if (!isNaN(num)) numeric = num;
      }

      return {
        title: title,
        priceText: priceText || null,
        price: numeric,
        url: location.href,
        ts: Date.now()
      };
    } catch (e) {
      return { title: document.title || '', priceText: null, price: null, url: location.href, ts: Date.now() };
    }
  }
});
